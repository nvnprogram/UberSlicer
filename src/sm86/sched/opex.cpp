
#include <vector>

#include "deps.h"
#include "issue.h"
#include "sb.h"

namespace ub {
namespace sm86 {
namespace sched {

void opex_replay(SbProg &p, DepsCtx ctx, SbStats *stats) {
    std::vector<SInst> flat;
    std::vector<int> node, flatOf(p.nodes.size(), -1), start(p.blocks.size() + 1, 0);
    for (size_t b = 0; b < p.blocks.size(); b++) {
        start[b] = (int)flat.size();
        for (int k = p.first_inst((int)b); k != p.blocks[b].eb; k = p.nodes[k].next) {
            flatOf[k] = (int)flat.size();
            flat.push_back(p.nodes[k].s);
            node.push_back(k);
        }
    }
    start[p.blocks.size()] = (int)flat.size();

    for (SInst &s : flat) {
        s.waitTa = s.waitLatency = s.cumuWait = s.maxCcOrP = 0;
        s.endGroup = 0;
    }
    for (SbBlock &b : p.blocks) b.maxHazard = false;
    IssueMachine m;
    m.DoOpexing = true;
    const int total = (int)flat.size();
    for (size_t b = 0; b < p.blocks.size(); b++) {
        int s0 = start[b], n = start[b + 1] - s0;
        if (n == 0) continue;
        SInst *in = flat.data() + s0;
        ctx.after = in + n;
        ctx.nafter = total - s0 - n;
        BlockDeps bd;
        calc_deps(in, n, ctx, &bd);
        ur_nc_step(in, n, ctx);
        for (int j = 0; j < n && j < (int)bd.prohibit_reuse.size(); j++)
            if (bd.prohibit_reuse[j]) in[j].flags |= GF_PROHIBIT_REUSE;
        m.set_deps(&bd);
        m.init_block(in, n);
        m.depbarConsumer.assign(n, nullptr);
        for (int i = 0; i < n; i++) {
            int c = p.nodes[node[s0 + i]].depConsumer;
            if (c >= 0 && flatOf[c] >= 0) m.depbarConsumer[i] = &flat[flatOf[c]];
        }
        long long worst0 = g_latency_worst_calls;
        std::vector<int> ref = bd.ref;
        int i = 0;
        bool avail = !ori_kind(in[0]).flow;
        if (avail) m.avail_added(0, ref);
        while (avail) {
            m.process_pick(i);
            if (in[i].ta > m.now) m.now = in[i].ta;
            for (const DepEdge &e : bd.out[i]) {
                int t = m.now + m.dep_latency(i, e);
                if (t > in[e.to].ta) in[e.to].ta = t;
                m.dep_released(i, e);
            }
            avail = i + 1 < n && !ori_kind(in[i + 1]).flow;
            if (avail) m.avail_added(i + 1, ref);
            m.avail_removed(i, ref);
            m.schedule(i);
            i++;
        }

        if (i < n) m.finish_inst(i++);
        m.opex_block_end();
        if (g_latency_worst_calls != worst0) p.blocks[b].maxHazard = true;
        for (int j = 0; j < n; j++) in[j].resToUse = (int8_t)m.resToUse[j];
    }
    if (stats) stats->assertHits += m.assertHits;
    for (int j = 0; j < total; j++) p.nodes[node[j]].s = flat[j];
}

}
}
}
