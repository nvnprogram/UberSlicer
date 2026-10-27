
#ifndef UB_SM86_SCHED_CLASSIFY_H
#define UB_SM86_SCHED_CLASSIFY_H

#include <cstdint>

#include "../sm86.h"
#include "schedtab.h"

namespace ub {
namespace sm86 {
namespace sched {

enum {
    GF_MUST_BE_SINGLETON = 1 << 0, GF_NEEDS_READ_SB = 1 << 1, GF_NEEDS_WRITE_SB = 1 << 2,
    GF_IS_LONG_LATENCY = 1 << 3, GF_USE_HIGH_COST_SB = 1 << 4, GF_IS_TEX_BATCH = 1 << 5,
    GF_DEF_CC_OR_PREG = 1 << 6, GF_IS_PREDICATED = 1 << 7, GF_IS_LONG_LAT_MEM_READ = 1 << 8,
    GF_REQ_LONG_LATENCY_SB = 1 << 9, GF_REQ_PREDICATED_SB = 1 << 10, GF_FP16 = 1 << 11,
    GF_PROHIBIT_REUSE = 1 << 12, GF_COUPLED = 1 << 13, GF_DECOUPLED = 1 << 14,
    GF_REDIRECTED = 1 << 15, GF_HYBRID = 1 << 16, GF_USE_RESERVED_SB = 1 << 17,
    GF_USE_RESERVED_SB2 = 1 << 18, GF_REQ_DECOUPLED_SB = 1 << 19, GF_PADDED_FOR_CC_OR_P = 1 << 20,
    GF_IS_READ_BATCH = 1 << 21, GF_IS_LONG_LAT_MEM_WRITE = 1 << 22, GF_USES_CC_REG = 1 << 23,
    GF_IS_INDEXED_LDC = 1 << 24, GF_HAS_UNIFORM_REF = 1 << 25, GF_NO_PRED_BYPASS = 1 << 26,
    GF_BAR_DEP = 1 << 27, GF_NOT_FIRST_IN_PAIR = 1 << 28, GF_NOT_SECOND_IN_PAIR = 1 << 29,
    GF_IS_COLLECTOR_CACHE_VALID = 1 << 30
};

struct SchedClass {
    int16_t sop;
    uint8_t unit;
    uint8_t vq;
    uint8_t pipe;
    uint8_t sbk;
    int16_t latency;
    uint32_t res;
    uint32_t flags;
};

static const uint32_t CLASSIFY_FLAGS =
    GF_NEEDS_READ_SB | GF_NEEDS_WRITE_SB | GF_IS_LONG_LATENCY | GF_USE_HIGH_COST_SB |
    GF_IS_TEX_BATCH | GF_DEF_CC_OR_PREG | GF_IS_PREDICATED | GF_IS_LONG_LAT_MEM_READ |
    GF_IS_LONG_LAT_MEM_WRITE | GF_COUPLED | GF_DECOUPLED | GF_REDIRECTED | GF_HYBRID |
    GF_HAS_UNIFORM_REF | GF_NO_PRED_BYPASS | GF_IS_COLLECTOR_CACHE_VALID;

int sass_op(const Inst &i);

bool classify(const Inst &i, int shader_type, SchedClass *c);

}
}
}

#endif
