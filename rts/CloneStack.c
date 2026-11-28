/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2020-2021
 *
 * Stack snapshotting and decoding. (Cloning and unwinding.)
 *
 *---------------------------------------------------------------------------*/

#include "Rts.h"
#include "RtsFlags.h"
#include "rts/Messages.h"
#include "Messages.h"
#include "rts/Types.h"
#include "rts/storage/TSO.h"
#include "stg/Types.h"
#include "CloneStack.h"
#include "StablePtr.h"
#include "Threads.h"
#include "Prelude.h"

#if defined(DEBUG)
#include "sm/Sanity.h"
#include "Printer.h"
#endif

#include <string.h>


#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
typedef struct {
  size_t stack_size_offset, dirty_offset, sp_offset, stack_offset;
  size_t underflow_bytes, underflow_info_offset, underflow_next_offset;
  const StgInfoTable *underflow_info[4];
  StgOffset (*check)(const StgClosure *);
} CloneStackLayout;

RTS_PRIVATE StgStack *ghc_rust_clone_stack(Capability *capability,
                                           const StgStack *stack,
                                           const CloneStackLayout *layout);
GHC_STATIC_ASSERT(sizeof(StgStack) == offsetof(StgStack, stack) &&
                  sizeof(((StgStack *)0)->stack_size) == sizeof(uint32_t) &&
                  sizeof(((StgStack *)0)->dirty) == sizeof(uint8_t) &&
                  sizeof(StgUnderflowFrame) % sizeof(StgWord) == 0 &&
                  sizeof(StgWord) == sizeof(size_t),
                  "Rust stack clone uses native stack word layout");

static const CloneStackLayout cloneStackLayout = {
  offsetof(StgStack, stack_size), offsetof(StgStack, dirty),
  offsetof(StgStack, sp), offsetof(StgStack, stack),
  sizeof(StgUnderflowFrame), offsetof(StgUnderflowFrame, info),
  offsetof(StgUnderflowFrame, next_chunk),
  { &stg_stack_underflow_frame_d_info,
    &stg_stack_underflow_frame_v16_info,
    &stg_stack_underflow_frame_v32_info,
    &stg_stack_underflow_frame_v64_info },
#if defined(DEBUG)
  checkClosure
#else
  NULL
#endif
};
#else
static StgStack* cloneStackChunk(Capability* capability, const StgStack* stack)
{
  StgWord spOffset = stack->sp - stack->stack;
  StgWord closureSizeBytes = sizeof(StgStack) + (stack->stack_size * sizeof(StgWord));

  StgStack* newStackClosure = (StgStack*) allocate(capability, ROUNDUP_BYTES_TO_WDS(closureSizeBytes));

  memcpy(newStackClosure, stack, closureSizeBytes);

  newStackClosure->sp = newStackClosure->stack + spOffset;
  // The new stack is not on the mutable list; clear the dirty flag such that
  // we don't claim that it is.
  newStackClosure->dirty = 0;

#if defined(DEBUG)
  checkClosure((StgClosure*) newStackClosure);
#endif

  return newStackClosure;
}
#endif

StgStack* cloneStack(Capability* capability, const StgStack* stack)
{
#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
  return ghc_rust_clone_stack(capability, stack, &cloneStackLayout);
#else
  StgStack *top_stack = cloneStackChunk(capability, stack);
  StgStack *last_stack = top_stack;
  while (true) {
    StgPtr end = last_stack->stack + last_stack->stack_size;
    // The collector copies only the live words from sp to end.
    if ((size_t)(end - last_stack->sp) < sizeofW(StgUnderflowFrame)) {
      break;
    }
    StgUnderflowFrame *frame = (StgUnderflowFrame *)(end - sizeofW(StgUnderflowFrame));
    if (frame->info == &stg_stack_underflow_frame_d_info
      ||frame->info == &stg_stack_underflow_frame_v16_info
      ||frame->info == &stg_stack_underflow_frame_v32_info
      ||frame->info == &stg_stack_underflow_frame_v64_info) {
      StgStack *s = cloneStackChunk(capability, frame->next_chunk);
      frame->next_chunk = s;
      last_stack = s;
    } else {
      break;
    }
  }
  return top_stack;
#endif
}

#if defined(THREADED_RTS)

// ThreadId# in Haskell is a StgTSO* in RTS.
void sendCloneStackMessage(StgTSO *tso, HsStablePtr mvar) {
  Capability *srcCapability = rts_unsafeGetMyCapability();

  MessageCloneStack *msg;
  msg = (MessageCloneStack *)allocate(srcCapability, sizeofW(MessageCloneStack));
  msg->tso = tso;
  msg->result = (StgMVar*)deRefStablePtr(mvar);
  SET_HDR_RELEASE(msg, &stg_MSG_CLONE_STACK_info, CCS_SYSTEM);

  sendMessage(srcCapability, tso->cap, (Message *)msg);
}

// The cap argument is the capability which is handling the CloneStack message
void handleCloneStackMessage(Capability *cap, MessageCloneStack *msg){
  // We must check that the current owner of the thread we want to clone the stack for
  // is still this capability.
  // See Note [TSO owner may change in between Msg being sent and received]
  Capability *owner = RELAXED_LOAD(&msg->tso->cap);
  if (owner != cap) {
    // The target TSO may have migrated after the message was queued on the old
    // capability. In that case we must forward the request to the current
    // owner; otherwise we would race with another capability mutating the
    // stack while we clone it.
    sendMessage(cap, owner, (Message *)msg);
    return;
  }

  // At this point the executing capability owns the TSO, so it is the only
  // capability that may safely inspect the live stack and the one whose
  // allocator we must use for the cloned StgStack closure.
  StgStack* newStackClosure = cloneStack(cap, msg->tso->stackobj);

  // Lift StackSnapshot# to StackSnapshot by applying it's constructor.
  // This is necessary because performTryPutMVar() puts the closure onto the
  // stack for evaluation and stacks can not be evaluated (entered).
  HaskellObj result = rts_apply(cap, StackSnapshot_constructor_closure, (HaskellObj) newStackClosure);

  bool putMVarWasSuccessful = performTryPutMVar(cap, msg->result, result);

  if(!putMVarWasSuccessful) {
    barf("Can't put stack cloning result into MVar.");
  }
}

#else // !defined(THREADED_RTS)

STG_NORETURN
void sendCloneStackMessage(StgTSO *tso STG_UNUSED, HsStablePtr mvar STG_UNUSED) {
  barf("Sending CloneStackMessages is only available in threaded RTS!");
}

#endif // end !defined(THREADED_RTS)
