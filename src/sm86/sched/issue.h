
#ifndef UB_SM86_SCHED_ISSUE_H
#define UB_SM86_SCHED_ISSUE_H

#include <cstdint>
#include <vector>

#include "deps.h"
#include "machine.h"
#include "phase_a.h"
#include "prog.h"

namespace ub {
namespace sm86 {
namespace sched {

struct OriKind {
    bool flow;
    bool mem;
    int minNext;
    int minNextStrict;
};
OriKind ori_kind(const SInst &s);

const int I2I_ISSUE_RATE = 1;

int res_busy(const SInst &s);
int max_res_busy();

bool use_group_for(const SInst &s, int wait);

bool barrier_sync_event(const SInst &s);

struct IssueMachine : PaMachine {

    bool RegAlloc = true;
    bool DoOpexing = false;

    SInst *in = nullptr;
    int n = 0;
    const BlockDeps *deps = nullptr;

    int now = 0;
    int resTimeFree[32];
    int dispatchTimeFree[10];
    int lastIssued[32];
    int nextTexTime = 0, lastTexTime = -999;
    bool BarAvailable = false, BarDepReady = false, ScheduledMemOpSinceBar = false;
    int ipPriorDeferredBar = -1;
    int ipPriorSched = -1;

    int waitTime = 0, maxWaitTime = 0, maxCcOrPTime = 0;
    int cumuWaitSinceEndGroup = 0, numInstsSinceLastGroup = 0;
    int resTimeWait[32];
    int sbTime[6];
    int sbTimeSet[6];
    int depbarWaitTime = 0;
    bool SeenGenericRead = false;

    std::vector<const SInst *> depbarConsumer;
    long long assertHits = 0;

    std::vector<int> resToUse;
    std::vector<uint8_t> barDep;

    void init_block(SInst *in, int n) override;
    int time() const override { return now; }
    void set_time(int t) override { now = t; }
    int ready_time(int i) override;
    int pick_override(int i, int timeAvailable) override;
    int max_reg_bank(int) override { return 0; }
    int dep_latency(int from, const DepEdge &e) override;
    void schedule(int i) override;
    void finish_block() override {}

    void set_deps(const BlockDeps *d) override;
    void process_pick(int i) override;
    void avail_added(int i, const std::vector<int> &ref) override;
    void avail_removed(int i, const std::vector<int> &ref) override;

    void finish_inst(int i) override;
    void dep_released(int from, const DepEdge &e) override;

    int get_ready_time_fermi(int i);
    int get_ready_time(int i);
    int ready_time_adj(int i);
    int get_issue_delay(int i, int candidateIssueTime) const;
    int res_busy_time(int i) const;
    int min_next_issue(int i, bool strict = false) const;
    bool barrier_sync_event(int i) const;

    void update_wait_info(int prior, int i);
    int opex_wait(int i, bool *endGroup);
    bool use_group(int i, int wait) const;
    void update_last_group_info(int prior, int i);
    void opex_process_inst(int i);
    void update_time_available_from_sb(int i);
    void opex_block_end();
};

}
}
}

#endif
