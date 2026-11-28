#include "Rts.h"

#if !defined(USE_RUST_RTS)
W_ hs_mulIntMayOflo(W_ a, W_ b) {
  I_ r;
  return (W_)__builtin_mul_overflow((I_)a, (I_)b, &r);
}
#endif
