#pragma once

#include "Capability.h"

#if defined(USE_RUST_RTS) && !defined(TSAN_ENABLED)
#define USE_RUST_SUSPENDED_CALLS

GHC_STATIC_ASSERT(offsetof(InCall, next) == offsetof(InCall, prev) + sizeof(InCall *),
                  "InCall links must be adjacent");
GHC_STATIC_ASSERT(sizeof(((InCall *)0)->suspended_tso) == sizeof(StgClosure *),
                  "InCall suspended TSO slot must hold a closure pointer");

RTS_PRIVATE void ghc_rust_suspended_calls_insert(InCall **head, uint32_t *count,
                                                  InCall *incall, size_t links_offset);
RTS_PRIVATE void ghc_rust_suspended_calls_remove(InCall **head, uint32_t *count,
                                                  InCall *incall, size_t links_offset);
RTS_PRIVATE void ghc_rust_suspended_calls_visit(InCall *head,
                                                 size_t links_offset,
                                                 size_t tso_offset,
                                                 evac_fn evac, void *user);
RTS_PRIVATE InCall *ghc_rust_suspended_calls_find(InCall *head, StgTSO *target,
                                                   size_t links_offset, size_t tso_offset);
#endif
