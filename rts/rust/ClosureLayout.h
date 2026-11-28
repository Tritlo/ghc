#pragma once

#include "Rts.h"

#define FIELD(name, type, field, width)                                        \
    GHC_STATIC_ASSERT(sizeof(((type *)0)->field) == sizeof(width),             \
                      "Rust reads the native width of " #type "." #field);    \
    const char ghc_rust_usize_##name[1 + offsetof(type, field)] = {0}

#define TAG(name)         const char ghc_rust_u32_TAG_##name[1 + (name)] = {0}
#define OFFSET(name, value) const char ghc_rust_usize_##name[1 + (value)] = {0}

GHC_STATIC_ASSERT(sizeof(StgWord) == sizeof(size_t), "Rust uses a native machine word");
