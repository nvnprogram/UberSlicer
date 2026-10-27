
#ifndef UB_SM86_SCHED_MACHINE_H
#define UB_SM86_SCHED_MACHINE_H

#include <cstdint>

#include "prog.h"

namespace ub {
namespace sm86 {
namespace sched {

enum DepType { DEP_FLOW = 0, DEP_OUTPUT = 1, DEP_ANTI = 2, DEP_ORDER = 3 };

enum MemDomain { MD_GENMEM = 0, MD_SMEM = 1, MD_LMEM = 2, MD_GMEM = 3, MD_SURF = 6 };

struct LatCfg {
    int texDefaultLatency = 300;
    int readDefaultLatency = 300;
    int barSuppLatency = 0;
    bool wawTransitivity = true;
};
extern LatCfg g_lat;

extern thread_local long long g_latency_worst_calls;

bool bar_defer_blocking(const SInst &s);

const SInst &eb_inst();

int latency(const SInst &from, const SInst *to, int regClassMask);
int output_dep_latency(const SInst &from, const SInst &to, int regClassMask);
int anti_dep_latency(const SInst &from, const SInst &to, int regClassMask);
int order_dep_latency(const SInst &from, const SInst &to, unsigned memDomainMask, bool tepid);

int dep_latency(int depType, const SInst &from, const SInst &to, int regClassMask,
                unsigned memDomainMask, bool tepid);

const int SCOREBOARD_RAW_DELAY = 2;

int read_sb_latency(const SInst &ip);
int write_sb_latency(const SInst &ip);

bool has_sb_reg_anti_dep(const SInst &from, const SInst &to);
bool same_ordered_vq(const SInst &a, const SInst &b);

}
}
}

#endif
