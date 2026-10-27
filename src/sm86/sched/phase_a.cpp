
#include "phase_a.h"

#include "machine.h"

namespace ub {
namespace sm86 {
namespace sched {

namespace {

bool select_paired(const Sel &cur, const Sel &best, bool &better) {
    if (cur.latency != best.latency) {
        if (cur.latency < best.latency) better = true;
    } else if (cur.extraBankConflict != best.extraBankConflict) {
        if (cur.extraBankConflict < best.extraBankConflict) better = true;
    } else if (cur.maxRegBankUse != best.maxRegBankUse) {
        if (cur.maxRegBankUse > best.maxRegBankUse) better = true;
    } else {
        return false;
    }
    return true;
}

}

bool sel_better(const Sel &cur, const Sel &best, int numOfLdgDepBar) {
    bool better = false;
    if (cur.overrideValue != best.overrideValue) {
        better = cur.overrideValue < best.overrideValue;
    } else if (cur.BreaksBatch != best.BreaksBatch) {
        better = best.BreaksBatch;
    } else if (cur.afterNextTex != best.afterNextTex) {
        better = cur.afterNextTex < best.afterNextTex;
    } else if (cur.CriticalKilDep != best.CriticalKilDep) {
        better = cur.CriticalKilDep;
    } else if (cur.ToBePaired != best.ToBePaired) {
        better = cur.ToBePaired;
    } else if (cur.ToBePaired && select_paired(cur, best, better)) {
    } else if (cur.stallPreDepBar < best.stallPreDepBar && cur.GoodForStall) {
        better = true;
    } else if (best.stallPreDepBar < cur.stallPreDepBar && best.GoodForStall) {
    } else if (cur.IsGlobalRead != best.IsGlobalRead && numOfLdgDepBar > 0) {
        better = best.IsGlobalRead;
    } else if (cur.adjStallDistance != best.adjStallDistance) {
        better = cur.adjStallDistance > best.adjStallDistance;
    } else if (cur.latency != best.latency) {
        better = cur.latency < best.latency;
    } else if (cur.IsKill != best.IsKill) {
        better = cur.IsKill;
    } else if (cur.maxRegBankUse != best.maxRegBankUse) {
        better = cur.maxRegBankUse > best.maxRegBankUse;
    } else {
        better = cur.instOrder < best.instOrder;
    }
    return better;
}

int sel_pick(const std::vector<Sel> &cands, int numOfLdgDepBar, int availSize) {
    int best = -1, offDeck = -1;
    for (int k = 0; k < (int)cands.size(); k++) {
        if (best < 0 || sel_better(cands[k], cands[best], numOfLdgDepBar)) best = k;
        if (cands[k].IsOffDeck) offDeck = k;
    }
    if (best >= 0 && cands[best].DefCcOrPReg && offDeck >= 0 && availSize < 9) best = offDeck;
    return best;
}

int info_edge_latency(const SInst &from, const SInst &to, const DepEdge &e) {
    switch (e.type) {
    case DEP_FLOW: return latency(from, &to, e.reg_mask);
    case DEP_OUTPUT: return output_dep_latency(from, to, e.reg_mask);
    case DEP_ANTI: return 1;
    default: {
        int o = order_dep_latency(from, to, e.mem_mask, true);
        return o > 1 ? o : 1;
    }
    }
}

void calc_info(const SInst *in, int n, const BlockDeps &deps, std::vector<PaInfo> &info, PaLimits &lim) {
    info.assign(n, PaInfo());
    const int tex2TexDelay = 1;
    int maxTime = 0, closestTex = PA_CLOSEST_OUT_OF_BLOCK, closestRead = PA_CLOSEST_OUT_OF_BLOCK,
        closestKil = PA_CLOSEST_OUT_OF_BLOCK, nextTexDistance = 0, texIndex = 0;
    for (int i = 0; i < n; i++)
        if (in[i].sc.flags & GF_IS_TEX_BATCH) texIndex++;
    for (int i = n - 1; i >= 0; i--) {
        const SInst &s = in[i];
        PaInfo &c = info[i];
        bool tex = (s.sc.flags & GF_IS_TEX_BATCH) != 0;
        bool kil = s.sc.sop == SOP_SM70_KILL;
        int time = 0;
        if (deps.out[i].empty()) time = latency(s, &eb_inst(), 0);
        if (kil && maxTime > time) time = maxTime;
        for (const DepEdge &e : deps.out[i]) {
            PaInfo &t = info[e.to];
            if (t.critKil) c.critKil = true;
            int tt = t.distance + info_edge_latency(s, in[e.to], e);
            if (tt > time) time = tt;
            if (tex && texIndex > t.texDepIndex) t.texDepIndex = texIndex;
        }
        c.closestTex = closestTex;
        c.closestDepTex = nextTexDistance;
        c.closestRead = closestRead;
        c.closestKil = closestKil;
        if (tex) {
            if (time < nextTexDistance + tex2TexDelay) time = nextTexDistance + tex2TexDelay;
            if (maxTime > time) time = maxTime;
            closestTex = i + 1;
            nextTexDistance = time;
            texIndex--;
        }
        if (s.sc.flags & GF_IS_LONG_LAT_MEM_READ) closestRead = i + 1;
        if (kil) closestKil = i + 1;
        c.distance = time;
        if (time > maxTime) maxTime = time;
    }
    lim.texLimit = closestTex;
    lim.readLimit = closestRead;
    lim.kilLimit = closestKil;
    lim.texDistance = nextTexDistance;
}

bool inst_off_deck(const SInst &s, bool lastInBlock) {
    switch (s.sc.sop) {
    case SOP_SM70_RET: case SOP_SM70_BAR: case SOP_SM70_MEMBAR: case SOP_SM70_SETLMEMBASE:
        return true;
    case SOP_SM70_NOP:
        return lastInBlock;
    default:
        return false;
    }
}

bool inst_memory_read(const SInst &s) {
    if (s.sc.flags & GF_IS_LONG_LAT_MEM_READ) return true;
    switch (s.sc.sop) {
    case SOP_SM70_ALD: case SOP_SM70_LDS:
        return true;
    case SOP_SM70_LDC: {
        int v = val_index(s.in.cls, "sz");
        return v >= 0 && get(s.in, v) >= 5;
    }
    default:
        return false;
    }
}

void phase_a_block(SInst *in, int n, const BlockDeps &deps, PaMachine &m, std::vector<int> &order) {
    order.clear();
    if (n == 0) return;
    std::vector<int> ref = deps.ref;
    m.set_deps(&deps);
    m.init_block(in, n);
    std::vector<int> avail;
    for (int i = 0; i < n; i++)
        if (ref[i] == 0) {
            avail.insert(avail.begin(), i);
            m.avail_added(i, ref);
        }
    std::vector<PaInfo> info;
    PaLimits lim;
    calc_info(in, n, deps, info, lim);

    int nextTexDistance = lim.texDistance, maxTexIndexCommitted = 0, lastTexSchedTime = -9999;
    int nextTexLimit = lim.texLimit, nextReadLimit = lim.readLimit, nextKilLimit = lim.kilLimit;
    std::vector<Sel> cands;
    while (!avail.empty()) {
        int time = m.time();
        cands.clear();
        int nextReadOrderNo = PA_CLOSEST_OUT_OF_BLOCK, nextKilOrderNo = PA_CLOSEST_OUT_OF_BLOCK;
        bool globalRead = false;
        for (int i : avail) {
            const SInst &s = in[i];
            const PaInfo &c = info[i];
            int instOrder = i + 1;
            bool tex = (s.sc.flags & GF_IS_TEX_BATCH) != 0;
            if (nextReadOrderNo > c.closestRead) nextReadOrderNo = c.closestRead;
            if (nextKilOrderNo > c.closestKil) nextKilOrderNo = c.closestKil;
            Sel q;
            q.idx = i;
            int ta = m.ready_time(i);
            q.latency = ta - time;
            q.overrideValue = m.pick_override(i, ta);
            if (q.latency < 0) q.latency = 0;
            q.IsKill = s.sc.sop == SOP_SM70_KILL;
            q.CriticalKilDep = c.critKil;
            q.maxRegBankUse = m.max_reg_bank(i);
            q.afterNextTex = (instOrder > nextTexLimit) * 2;
            if (time <= lastTexSchedTime + 1) {
                if (tex) {
                    if (c.distance != nextTexDistance || time + q.latency > lastTexSchedTime + 1) q.BreaksBatch = true;
                } else if (time + q.latency + 1 > lastTexSchedTime + 1) {
                    q.BreaksBatch = true;
                }
            }
            q.stallPreDepBar = q.latency;
            q.adjStallDistance = c.distance - q.latency;
            q.GoodForStall = c.texDepIndex <= maxTexIndexCommitted &&
                             (instOrder <= nextReadLimit || inst_memory_read(s)) && instOrder <= nextKilLimit &&
                             c.closestTex <= nextTexLimit;
            if (s.sc.sop == SOP_SM70_LDG) globalRead = true;
            q.IsGlobalRead = globalRead;
            q.instOrder = instOrder;
            q.DefCcOrPReg = (s.sc.flags & GF_DEF_CC_OR_PREG) != 0;
            q.IsOffDeck = inst_off_deck(s, i == n - 1);
            cands.push_back(q);
        }
        int k = sel_pick(cands, 0, (int)cands.size());
        int best = cands[k].idx;
        const Sel &bs = cands[k];
        const PaInfo &bi = info[best];
        if (in[best].sc.flags & GF_IS_TEX_BATCH) {
            lastTexSchedTime = time + bs.latency;
            if (nextTexLimit < bi.closestTex) {
                nextTexLimit = bi.closestTex;
                nextTexDistance = bi.closestDepTex;
            }
        }
        if (bi.texDepIndex > maxTexIndexCommitted) maxTexIndexCommitted = bi.texDepIndex;
        if (best + 1 == nextReadLimit) nextReadLimit = nextReadOrderNo;
        if (best + 1 == nextKilLimit) nextKilLimit = nextKilOrderNo;

        m.process_pick(best);
        if (in[best].ta > m.time()) m.set_time(in[best].ta);
        avail.erase(avail.begin() + k);
        for (const DepEdge &e : deps.out[best]) {
            int t = m.time() + m.dep_latency(best, e);
            if (t > in[e.to].ta) in[e.to].ta = t;
            m.dep_released(best, e);
            if (--ref[e.to] == 0) {
                avail.insert(avail.begin(), e.to);
                m.avail_added(e.to, ref);
            }
        }
        m.avail_removed(best, ref);
        order.push_back(best);
        m.schedule(best);
    }

    std::vector<uint8_t> done(n, 0);
    for (int i : order) done[i] = 1;
    for (int i = 0; i < n; i++)
        if (!done[i]) {
            order.push_back(i);
            m.finish_inst(i);
        }
    m.finish_block();
}

void phase_a_program(std::vector<SInst> &prog, const std::vector<int> &starts, DepsCtx ctx, PaMachine &m,
                     std::vector<int> &perm) {
    const std::vector<SInst> orig = prog;
    int total = (int)orig.size();
    perm.resize(total);
    for (int k = 0; k < total; k++) perm[k] = k;
    std::vector<SInst> si;
    std::vector<int> ord;
    for (size_t b = 0; b < starts.size(); b++) {
        int s0 = starts[b], n = (b + 1 < starts.size() ? starts[b + 1] : total) - s0;
        if (n <= 0) continue;
        si.assign(orig.begin() + s0, orig.begin() + s0 + n);
        ctx.after = orig.data() + s0 + n;
        ctx.nafter = total - s0 - n;
        BlockDeps bd;
        calc_deps(si.data(), n, ctx, &bd);
        ur_nc_step(si.data(), n, ctx);
        phase_a_block(si.data(), n, bd, m, ord);
        for (int k = 0; k < n; k++) {
            prog[s0 + k] = orig[s0 + ord[k]];
            perm[s0 + k] = s0 + ord[k];
        }
    }
}

}
}
}
