
#ifndef UB_SM86_SCHED_DEPS_H
#define UB_SM86_SCHED_DEPS_H

#include <cstdint>
#include <vector>

#include "machine.h"
#include "prog.h"

namespace ub {
namespace sm86 {
namespace sched {

enum MemDomainRest {
    MD_OBUF = 4, MD_IBUF = 5, MD_TEX = 7, MD_PATCH = 8, MD_KILL = 9, MD_ARCH_STATE = 10,
    MD_SPILL_LOCAL = 11, MD_SPILL_SHARED = 12, MD_UR = 13, MD_ACTIVE_MASK = 14, MD_TTU = 15,
    MD_MAP = 16, MD_CONST = 17, MD_IPARAM = 18, MD_IMPLICIT_DERIVATIVES = 19, MD_COUNT = 20
};

struct DepEdge {
    int to;
    uint8_t type;
    uint16_t reg_mask;
    uint32_t mem_mask;
};

struct BlockDeps {

    std::vector<std::vector<DepEdge>> out;

    std::vector<int> ref;

    std::vector<uint8_t> prohibit_reuse;
};

struct DepsCtx {
    bool has_kil = false;
    bool compute = false;
    bool shared_isb = false;

    uint64_t ur_nc[2] = {0, 0};
    uint8_t up_nc = 0;

    const SInst *after = nullptr;
    int nafter = 0;
};

bool dont_schedule(const SInst &s);

void calc_deps(const SInst *in, int n, const DepsCtx &ctx, BlockDeps *out);

void ur_nc_step(const SInst *in, int n, DepsCtx &ctx);

int rev_regs(const SInst &s, uint8_t *ord);

}
}
}

#endif
