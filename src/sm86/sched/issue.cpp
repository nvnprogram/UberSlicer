
#include "issue.h"

#include <algorithm>
#include <cstring>

namespace ub {
namespace sm86 {
namespace sched {

namespace {

const int NUM_RES = 32;
const int NUM_DISPATCH = 10;
const int BAR_DELAY = 200;

enum { D_ALU, D_FMA, D_FMA64, D_FP16, D_LSU, D_CBU, D_HMMA, D_IMMA, D_REDUX };

int busy_time(int res) {
    switch (res) {
    case RES_FMA: case RES_ALU: case RES_HMMA32: case RES_FP16C: case RES_UDP: case RES_HFMA2MMA: return 2;
    case RES_FMA64LITE: case RES_HMMA16: case RES_IMMA: case RES_LSU: case RES_CBU: case RES_HMMA1688:
    case RES_IMMA16816: case RES_CLMAD: return 4;
    case RES_HMMASP1688: case RES_IMMASP16832: return 6;
    case RES_ADU: case RES_XU64: case RES_HMMA16816: case RES_REDUX: case RES_IMMA16832: return 8;
    case RES_DMMA: return 10;
    case RES_2XFMA: return 1;
    default: return 0;
    }
}

int dispatch_unit(int res) {
    switch (res) {
    case RES_FMA: case RES_2XFMA: return D_FMA;
    case RES_FMA64LITE: case RES_CLMAD: return D_FMA64;
    case RES_FP16C: case RES_HFMA2MMA: return D_FP16;
    case RES_LSU: return D_LSU;
    case RES_CBU: return D_CBU;
    case RES_HMMA16: case RES_HMMA32: case RES_HMMA1688: case RES_HMMA16816: case RES_DMMA:
    case RES_HMMASP1688: return D_HMMA;
    case RES_IMMA: case RES_IMMA16816: case RES_IMMA16832: case RES_IMMASP16832: return D_IMMA;
    case RES_REDUX: return D_REDUX;
    default: return D_ALU;
    }
}

uint32_t bit(int r) { return 1u << r; }

uint32_t modeled(uint32_t res, bool regAlloc) {
    uint32_t a = bit(RES_CLMAD) | bit(RES_DMMA) | bit(RES_REDUX) | bit(RES_HFMA2MMA) | bit(RES_HMMASP1688) |
                 bit(RES_IMMA16816) | bit(RES_IMMA16832) | bit(RES_IMMASP16832) | bit(RES_2XFMA);
    if (res & a) return res & a;
    uint32_t t = bit(RES_HMMA16816) | bit(RES_HMMA1688) | bit(RES_UDP);
    if (res & t) return res & t;
    uint32_t v = bit(RES_FMA64LITE) | bit(RES_HMMA16) | bit(RES_HMMA32) | bit(RES_IMMA) | bit(RES_XU64);
    if (regAlloc) v |= bit(RES_FMA) | bit(RES_ALU) | bit(RES_LSU) | bit(RES_FP16C) | bit(RES_ADU);
    return res & v;
}

bool defer_blocking(const SInst &s) {
    if (s.sc.sop != SOP_SM70_BAR) return false;
    int v = val_index(s.in.cls, "defer_blocking");
    return v >= 0 && get(s.in, v) != 0;
}

bool is_tex_batch(const SInst &s) { return (s.flags & GF_IS_TEX_BATCH) != 0; }

int busy_of(const SInst &s, int res) {
    int op = s.sc.sop;
    if (op == SOP_SM70_LDS || op == SOP_SM73_LDSM) return busy_time(RES_LSU);
    if (op == SOP_SM70_IMAD_WIDE) return 4;
    return busy_time(res);
}

const int NUM_SB = 6;
const int SB_MULTI_TEX = NUM_SB - 1;
const int WAIT_REQ_FOR_END_GROUP = 2;
const int MAX_CUMU_WAIT_SINCE_END_GROUP = 10;

bool is_mma(const SInst &s) {
    switch (s.sc.sop) {
    case SOP_SM70_HMMA_16: case SOP_SM70_HMMA_32: case SOP_SM70_IMMA: case SOP_SM73_BMMA:
    case SOP_SM73_HMMA_16816: case SOP_SM73_HMMA_1688: case SOP_SM82_BMMA_168128: case SOP_SM82_BMMA_168256:
    case SOP_SM82_BMMA_88128: case SOP_SM82_DMMA: case SOP_SM82_HMMA_SP_1688: case SOP_SM82_IMMA_16816:
    case SOP_SM82_IMMA_16832: case SOP_SM82_IMMA_88: case SOP_SM82_IMMA_SP_16832: case SOP_SM82_IMMA_SP_88:
        return true;
    default:
        return false;
    }
}

int cc_or_p_latency(const SInst &s) {
    switch (s.sc.sop) {
    case SOP_SM70_MUFU: case SOP_SM70_F2F: case SOP_SM70_F2I: case SOP_SM70_I2F: case SOP_SM72_I2I:
    case SOP_SM70_POPC: case SOP_SM70_FLO: case SOP_SM70_IPA: case SOP_SM70_S2R: case SOP_SM70_ISBERD:
    case SOP_SM70_LD: case SOP_SM70_LDG: case SOP_SM70_LDS: case SOP_SM70_LDL: case SOP_SM70_LDC:
    case SOP_SM70_ALD: case SOP_SM70_ATOM: case SOP_SM70_ATOMG: case SOP_SM70_ATOMS: case SOP_SM70_SULD:
    case SOP_SM70_SUATOM: case SOP_SM70_TEX: case SOP_SM70_TLD: case SOP_SM70_TLD4: case SOP_SM70_TXD:
    case SOP_SM70_TMML: case SOP_SM70_TXQ:
        return 15;
    default:
        return 13;
    }
}

}

OriKind ori_kind(const SInst &s) {
    OriKind k = {false, false, 0, 0};
    switch (s.sc.sop) {
    case SOP_SM70_BRA: case SOP_SM70_BRX: case SOP_SM73_BRXU: case SOP_SM70_JMP: case SOP_SM70_JMX:
    case SOP_SM70_CALL: case SOP_SM70_RET: case SOP_SM70_EXIT: case SOP_SM70_BSYNC: case SOP_SM70_BPT:
    case SOP_SM70_IDE:
        k.flow = true;
        k.minNext = 5;
        break;
    case SOP_SM70_KILL: k.minNext = 5; break;
    case SOP_SM70_MEMBAR:

        k.flow = k.mem = true;
        k.minNext = s.in.cls >= 0 && s.in.op == op_id("NOP") ? 0 : 6;
        break;
    case SOP_SM70_BAR: k.mem = true; k.minNext = 6; break;
    case SOP_SM70_DEPBAR: k.mem = true; k.minNext = 4; break;
    case SOP_SM70_CCTL: case SOP_SM70_CCTLL: case SOP_SM70_CCTLT: case SOP_SM70_CCTL_NO_SB:
        k.mem = true;
        k.minNext = 5;
        break;
    case SOP_SM70_ERRBAR: case SOP_SM70_NANOSLEEP:
    case SOP_SM70_LD: case SOP_SM70_LDG: case SOP_SM70_LDL: case SOP_SM70_LDS: case SOP_SM73_LDSM:
    case SOP_SM70_LDC: case SOP_SM70_ALD: case SOP_SM70_AST: case SOP_SM70_ST: case SOP_SM70_STG:
    case SOP_SM70_STL: case SOP_SM70_STS: case SOP_SM70_ATOM: case SOP_SM70_ATOMG: case SOP_SM70_ATOMS:
    case SOP_SM70_RED: case SOP_SM70_SULD: case SOP_SM70_SUST: case SOP_SM70_SURED: case SOP_SM70_SUATOM:
    case SOP_SM70_ISBERD: case SOP_SM73_ISBEWR: case SOP_SM82_LDGSTS: case SOP_SM82_LDGDEPBAR:
        k.mem = true;
        break;
    case SOP_SM70_WARPSYNC: {

        Operand o[MAX_OPNDS];
        int no = operands(s.in, o, MAX_OPNDS);
        bool imm = false;
        for (int j = 0; j < no; j++)
            if (o[j].kind == O_IMM) imm = true;
        k.minNext = imm ? 0 : 4;
        break;
    }
    default: break;
    }
    k.minNextStrict = k.minNext;
    if (defer_blocking(s)) k.minNext = 0;
    return k;
}

void IssueMachine::set_deps(const BlockDeps *d) { deps = d; }

void IssueMachine::init_block(SInst *fin, int fn) {
    in = fin;
    n = fn;
    now = 0;
    nextTexTime = 0;
    lastTexTime = -999;
    memset(resTimeFree, 0, sizeof resTimeFree);
    memset(dispatchTimeFree, 0, sizeof dispatchTimeFree);
    for (int &x : lastIssued) x = -1;
    BarAvailable = BarDepReady = ScheduledMemOpSinceBar = false;
    waitTime = maxWaitTime = maxCcOrPTime = 0;
    numInstsSinceLastGroup = 0;
    ipPriorSched = -1;
    ipPriorDeferredBar = -1;
    memset(resTimeWait, 0, sizeof resTimeWait);
    for (int &x : sbTime) x = -1;

    memset(sbTimeSet, 0, sizeof sbTimeSet);
    depbarWaitTime = 0;
    resToUse.assign(n, 0);
    barDep.assign(n, 0);
    for (int i = 0; i < n; i++) in[i].ta = 0;
    if (deps) {
        for (int i = 0; i < n && i < (int)deps->out.size(); i++) {
            int s = in[i].sc.sop;
            if (s != SOP_SM70_BAR && s != SOP_SM70_MEMBAR) continue;
            for (const DepEdge &e : deps->out[i]) barDep[e.to] = 1;
        }
    }
}

int IssueMachine::min_next_issue(int i, bool strict) const {
    OriKind k = ori_kind(in[i]);
    return strict ? k.minNextStrict : k.minNext;
}

int IssueMachine::res_busy_time(int i) const { return busy_of(in[i], resToUse[i]); }

int res_busy(const SInst &s) { return busy_of(s, s.resToUse); }

int max_res_busy() {
    int m = 0;
    for (int r = 0; r < NUM_RES; r++) m = std::max(m, busy_time(r));
    return m;
}

bool IssueMachine::barrier_sync_event(int i) const { return sched::barrier_sync_event(in[i]); }

bool barrier_sync_event(const SInst &s) {
    if (s.flags & (GF_DECOUPLED | GF_REDIRECTED)) return true;
    switch (s.sc.sop) {
    case SOP_SM70_NOP: case SOP_SM70_PMTRIG: case SOP_SM70_ERRBAR: case SOP_SM70_IDE: case SOP_SM70_BPT:
    case SOP_SM70_CCTL_NO_SB: case SOP_SM70_DEPBAR:
        return true;
    default:
        return false;
    }
}

int IssueMachine::get_issue_delay(int i, int candidateIssueTime) const {
    int delay = 0;
    if (ipPriorDeferredBar >= 0 && barrier_sync_event(i)) {
        int minSync = min_next_issue(ipPriorDeferredBar, true);
        int conf = DoOpexing ? in[ipPriorDeferredBar].waitTa : in[ipPriorDeferredBar].ta;
        delay = std::max(delay, conf + minSync - candidateIssueTime);
    }
    return delay;
}

int IssueMachine::get_ready_time_fermi(int i) {
    SInst &s = in[i];
    int readyTime = s.ta;
    if (!is_tex_batch(s) && lastTexTime > readyTime) readyTime = lastTexTime;
    if (readyTime < now) readyTime = now;
    uint32_t res = s.sc.res;
    if (modeled(res, RegAlloc) == 0) {
        if (RegAlloc) readyTime += get_issue_delay(i, readyTime);
        return readyTime;
    }
    int best = -1, bestTime = 99999;
    for (int r = 0; r < NUM_RES && res; r++, res >>= 1) {
        if (!(res & 1)) continue;
        int t = std::max(resTimeFree[r], dispatchTimeFree[dispatch_unit(r)]);
        if (t <= readyTime) {
            best = r;
            bestTime = readyTime;
            break;
        }
        if (t < bestTime) {
            best = r;
            bestTime = t;
        }
    }
    if (best < 0) return 99999;
    resToUse[i] = best;
    if (RegAlloc) bestTime += get_issue_delay(i, bestTime);
    return bestTime;
}

int IssueMachine::get_ready_time(int i) { return get_ready_time_fermi(i); }

int IssueMachine::ready_time_adj(int i) {
    int op = in[i].sc.sop;
    if (op != SOP_SM70_BAR && op != SOP_SM70_MEMBAR) return 0;
    return ScheduledMemOpSinceBar && !BarDepReady ? BAR_DELAY : 0;
}

int IssueMachine::ready_time(int i) {
    int adj = ready_time_adj(i);
    return get_ready_time(i) + adj;
}

int IssueMachine::pick_override(int, int) { return 0; }

int IssueMachine::dep_latency(int from, const DepEdge &e) {
    return sched::dep_latency(e.type, in[from], in[e.to], e.reg_mask, e.mem_mask, true);
}

void IssueMachine::process_pick(int i) {
    in[i].ta = get_ready_time_fermi(i);
    if (DoOpexing) opex_process_inst(i);
}

void IssueMachine::dep_released(int from, const DepEdge &e) {
    if (e.type != DEP_FLOW || !(in[from].flags & GF_USE_HIGH_COST_SB)) return;
    int t = now + dep_latency(from, e);
    if (t > in[e.to].depbarCommit) in[e.to].depbarCommit = t;
}

void IssueMachine::avail_added(int i, const std::vector<int> &ref) {
    if (in[i].sc.sop != SOP_SM70_BAR) return;
    BarAvailable = true;
    if (!deps) return;
    for (const DepEdge &e : deps->out[i])
        if (ref[e.to] == 1) {
            BarDepReady = true;
            break;
        }
}

void IssueMachine::avail_removed(int i, const std::vector<int> &ref) {
    int op = in[i].sc.sop;
    if (op == SOP_SM70_BAR || op == SOP_SM70_MEMBAR) {
        ScheduledMemOpSinceBar = BarAvailable = BarDepReady = false;
    } else if (ori_kind(in[i]).mem) {
        ScheduledMemOpSinceBar = true;
    }
    if (BarAvailable && !BarDepReady && deps) {
        for (const DepEdge &e : deps->out[i])
            if (barDep[e.to] && ref[e.to] == 1) {
                BarDepReady = true;
                break;
            }
    }
}

void IssueMachine::schedule(int i) {
    SInst &s = in[i];

    if (RegAlloc && DoOpexing) {
        s.ta = now;
        update_wait_info(ipPriorSched, i);
        update_last_group_info(ipPriorSched, i);
        if (i == n - 1) {
            bool eg;
            s.waitLatency = opex_wait(i, &eg);
            s.endGroup = eg;
        }
    }

    s.ta = now;
    if (is_tex_batch(s)) {
        if (now < nextTexTime) now = nextTexTime;
        nextTexTime = now + 1;
        lastTexTime = now;
    }
    if (modeled(s.sc.res, RegAlloc) != 0) {
        int r = resToUse[i];
        lastIssued[r] = i;
        resTimeFree[r] = now + res_busy_time(i);
        dispatchTimeFree[dispatch_unit(r)] = now + 1;
    }
    int minNext = min_next_issue(i);
    if (minNext != 0) now += minNext - I2I_ISSUE_RATE;
    now += I2I_ISSUE_RATE;
    ipPriorSched = i;

    if (RegAlloc) {
        if (defer_blocking(s)) ipPriorDeferredBar = i;
        else if (ipPriorDeferredBar >= 0 && barrier_sync_event(i) && !(s.flags & GF_REDIRECTED))
            ipPriorDeferredBar = -1;
    }
}

void IssueMachine::finish_inst(int i) {
    in[i].ta = get_ready_time(i);
    process_pick(i);
    if (in[i].ta > now) now = in[i].ta;
    schedule(i);
}

void IssueMachine::update_wait_info(int prior, int i) {
    SInst &s = in[i];
    bool res = modeled(s.sc.res, RegAlloc) != 0;
    if (res && s.waitTa < resTimeWait[resToUse[i]]) s.waitTa = resTimeWait[resToUse[i]];
    if (prior >= 0) {
        bool eg;
        int wl = opex_wait(prior, &eg);
        in[prior].waitLatency = wl;
        in[prior].endGroup = eg;
        waitTime += wl;
        if (waitTime < s.waitTa) assertHits++;
        s.waitTa = waitTime;
    }
    if (res) resTimeWait[resToUse[i]] = waitTime + res_busy_time(i);
    if (deps)
        for (const DepEdge &e : deps->out[i]) {
            int t = waitTime + sched::dep_latency(e.type, s, in[e.to], e.reg_mask, e.mem_mask, false);
            if (t > in[e.to].waitTa) in[e.to].waitTa = t;
        }
    bool decoupled = (s.flags & GF_DECOUPLED) != 0;
    int lat = decoupled ? 0 : latency(s, nullptr, 0);
    lat = std::max(lat, order_dep_latency(s, eb_inst(), 0, false));
    maxWaitTime = std::max(maxWaitTime, waitTime + lat);
    if ((s.flags & GF_DEF_CC_OR_PREG) && !decoupled) maxCcOrPTime = std::max(maxCcOrPTime, s.ta + cc_or_p_latency(s));
    s.maxCcOrP = maxCcOrPTime;
    if (!(s.flags & GF_COUPLED)) {
        if (s.rdSB >= 0) sbTimeSet[s.rdSB] = waitTime;
        if (s.wrSB >= 0) sbTimeSet[s.wrSB] = waitTime;
        if (deps)
            for (const DepEdge &e : deps->out[i]) {
                if (e.type != DEP_ANTI) continue;
                SInst &d = in[e.to];
                int extra = has_sb_reg_anti_dep(s, d) ? SCOREBOARD_RAW_DELAY : 0;
                d.waitTa = std::max(d.waitTa, waitTime + extra);
                d.ta = std::max(d.ta, s.ta + extra);
            }
        maxWaitTime = std::max(maxWaitTime, waitTime + SCOREBOARD_RAW_DELAY);
    }

    if (SeenGenericRead && (s.flags & GF_USE_HIGH_COST_SB) && s.wrSB == SB_MULTI_TEX) depbarWaitTime = waitTime + 3;
}

int IssueMachine::opex_wait(int i, bool *endGroup) {
    int minWait = min_next_issue(i);
    int wait;
    bool last = i == n - 1;
    if (last || ori_kind(in[i]).flow) {
        wait = std::max(maxWaitTime - waitTime, minWait);
        if (wait < 1) wait = 1;
    } else {
        wait = std::max(in[i + 1].waitTa - waitTime, minWait);
        if (wait <= 0 && in[i + 1].ta != in[i].ta) wait = 1;
    }
    if (!last) wait += get_issue_delay(i + 1, waitTime + wait);
    *endGroup = use_group(i, wait);
    return wait;
}

bool IssueMachine::use_group(int i, int wait) const { return use_group_for(in[i], wait); }

bool use_group_for(const SInst &s, int wait) {
    if (wait > 11) return true;
    if (is_mma(s)) return false;
    if (s.flags & GF_DECOUPLED) return false;
    if (wait > WAIT_REQ_FOR_END_GROUP) return true;
    return wait > 1 && s.cumuWait >= MAX_CUMU_WAIT_SINCE_END_GROUP;
}

void IssueMachine::update_last_group_info(int prior, int i) {
    if (prior < 0) return;
    const SInst &p = in[prior];
    if ((p.flags & GF_IS_TEX_BATCH) || p.endGroup) cumuWaitSinceEndGroup = 0;
    else cumuWaitSinceEndGroup += p.waitLatency;
    in[i].cumuWait = cumuWaitSinceEndGroup;
}

void IssueMachine::opex_process_inst(int i) {
    SInst &s = in[i];
    if (s.sc.sop == SOP_SM70_LD) SeenGenericRead = true;
    if (s.sc.sop == SOP_SM70_DEPBAR && (s.flags & GF_REQ_LONG_LATENCY_SB)) {
        if (depbarWaitTime >= waitTime) s.ta = s.waitTa = depbarWaitTime;
        const SInst *c = i < (int)depbarConsumer.size() ? depbarConsumer[i] : nullptr;
        if (c && c->depbarCommit > s.ta) s.ta = c->depbarCommit;
    }
    update_time_available_from_sb(i);
}

void IssueMachine::update_time_available_from_sb(int i) {
    SInst &s = in[i];
    int my = s.ta;
    for (int k = 0; k < NUM_SB; k++) {
        if (!(s.reqSB & (1 << k))) continue;
        my = std::max(my, sbTime[k]);

        if (sbTime[k] > -1) {
            s.waitTa = std::max(s.waitTa, sbTimeSet[k] + SCOREBOARD_RAW_DELAY);
            sbTime[k] = -1;
        }
    }
    s.ta = my;
    if (s.rdSB >= 0) sbTime[s.rdSB] = std::max(sbTime[s.rdSB], read_sb_latency(s) + my);
    if (s.wrSB >= 0) sbTime[s.wrSB] = std::max(sbTime[s.wrSB], write_sb_latency(s) + my);
}

void IssueMachine::opex_block_end() {
    if (depbarWaitTime <= 0 || n == 0) return;
    SInst &p = in[n - 1];
    int extra = depbarWaitTime - (waitTime + p.waitLatency);
    if (extra <= 0) return;

    int w = p.waitLatency + extra;
    if (!use_group(n - 1, w)) {
        p.waitLatency = w;
        p.endGroup = 0;
    } else {
        p.waitLatency = std::min(w, 15);
        p.endGroup = 1;
    }
}

}
}
}
