
#ifndef UB_SM86_SCHED_PHASE_A_H
#define UB_SM86_SCHED_PHASE_A_H

#include <cstdint>
#include <vector>

#include "deps.h"

namespace ub {
namespace sm86 {
namespace sched {

struct Sel {
    int idx = -1;
    int latency = 0;
    int overrideValue = 0;
    bool BreaksBatch = false;
    int afterNextTex = 0;
    bool CriticalKilDep = false;
    bool ToBePaired = false;
    int stallPreDepBar = 0;
    bool GoodForStall = false;
    int adjStallDistance = 0;
    bool IsKill = false;
    int maxRegBankUse = 0;
    int extraBankConflict = 0;
    bool IsGlobalRead = false;
    int instOrder = 0;
    bool DefCcOrPReg = false;
    bool IsOffDeck = false;
};

bool sel_better(const Sel &cur, const Sel &best, int numOfLdgDepBar);

int sel_pick(const std::vector<Sel> &cands, int numOfLdgDepBar, int availSize);

struct PaInfo {
    int distance = 0;
    int closestTex = 0, closestDepTex = 0, closestRead = 0, closestKil = 0;
    int texDepIndex = -1;
    bool critKil = false;
};

struct PaLimits {
    int texLimit = 0, readLimit = 0, kilLimit = 0, texDistance = 0;
};

const int PA_CLOSEST_OUT_OF_BLOCK = 9999999;

int info_edge_latency(const SInst &from, const SInst &to, const DepEdge &e);

void calc_info(const SInst *in, int n, const BlockDeps &deps, std::vector<PaInfo> &info, PaLimits &lim);

struct PaMachine {
    virtual ~PaMachine() {}
    virtual void init_block(SInst *in, int n) = 0;
    virtual int time() const = 0;
    virtual void set_time(int t) = 0;
    virtual int ready_time(int i) = 0;
    virtual int pick_override(int i, int timeAvailable) = 0;
    virtual int max_reg_bank(int i) = 0;
    virtual int dep_latency(int from, const DepEdge &e) = 0;
    virtual void schedule(int i) = 0;
    virtual void finish_block() = 0;

    virtual void set_deps(const BlockDeps *) {}
    virtual void process_pick(int) {}
    virtual void avail_added(int, const std::vector<int> &) {}
    virtual void avail_removed(int, const std::vector<int> &) {}
    virtual void finish_inst(int) {}
    virtual void dep_released(int, const DepEdge &) {}

};

bool inst_off_deck(const SInst &s, bool lastInBlock);

bool inst_memory_read(const SInst &s);

void phase_a_block(SInst *in, int n, const BlockDeps &deps, PaMachine &m, std::vector<int> &order);

void phase_a_program(std::vector<SInst> &prog, const std::vector<int> &starts, DepsCtx ctx, PaMachine &m,
                     std::vector<int> &perm);

}
}
}

#endif
