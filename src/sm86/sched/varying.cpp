
#include <algorithm>

#include "sb.h"

namespace ub {
namespace sm86 {
namespace sched {

namespace {

const int NREG = 256 + 7;

bool varying_result(int op) {
    switch (op) {
    case SOP_SM70_S2R: case SOP_SM70_IPA: case SOP_SM70_ALD: case SOP_SM70_LDS: case SOP_SM70_LDG:
    case SOP_SM70_LDL: case SOP_SM70_LD: case SOP_SM70_ATOM: case SOP_SM70_ATOMG: case SOP_SM70_ATOMS:
    case SOP_SM70_TEX: case SOP_SM70_TLD: case SOP_SM70_TLD4: case SOP_SM70_TMML: case SOP_SM70_TXD:
    case SOP_SM70_TXQ: case SOP_SM70_SHFL: case SOP_SM70_SULD: case SOP_SM70_SUATOM: case SOP_SM70_PIXLD:
    case SOP_SM70_ISBERD: case SOP_SM70_FSWZADD: case SOP_SM70_AL2P: case SOP_SM70_AL2P_INDEXED:
    case SOP_SM73_LDSM: case SOP_SM70_MATCH: case SOP_SM70_CS2R_32: case SOP_SM70_CS2R_64:
        return true;
    }
    return false;
}

int reg_index(const SReg &r) {
    if (r.cls == RC_R && r.no >= 0 && r.no < 256) return r.no;
    if (r.cls == RC_P && r.no >= 0 && r.no < 7) return 256 + r.no;
    return -1;
}

bool is_branch(const SInst &s) {
    int op = s.sc.sop;
    return op == SOP_SM70_BRA || op == SOP_SM70_BRX || op == SOP_SM70_EXIT || op == SOP_SM70_RET;
}

void add_unique(std::vector<int> &v, int x) {
    if (std::find(v.begin(), v.end(), x) == v.end()) v.push_back(x);
}

class Analysis {
public:
    explicit Analysis(const SbProg &prog) : p(prog), nb((int)prog.blocks.size()) {}

    void run() {
        reaching_defs();
        postdominators();
        nodeVarying.assign(p.nodes.size(), 0);
        scratch.assign(nb, -1);
        divergent.assign(nb, 0);
        multiEnclosing.assign(nb, 0);
        activeSucc.assign(nb, 0);
        reached.assign(nb, 0);
        bool changed = true;
        while (changed) {
            changed = false;
            for (int b = 0; b < nb; b++)
                for_insts(b, [&](int k) { changed |= visit(b, k); });
            if (!p.hasBackEdge) break;
        }
    }

    bool operand_varying(int k, int i) const {
        const std::vector<int> &defs = reach[k][i];
        if (defs.empty()) return false;
        int control = scratch[nodeBlock[defNode[defs[0]]]];
        bool sameControl = true;
        for (int d : defs) sameControl = sameControl && scratch[nodeBlock[defNode[d]]] == control;
        bool sameInv = same_invariant(defs);
        int ub = nodeBlock[k];
        for (int d : defs) {
            int db = nodeBlock[defNode[d]];
            if (nodeVarying[defNode[d]] || (!sameInv && (!sameControl || multiEnclosing[ub] || multiEnclosing[db])))
                return true;
        }
        return false;
    }

    bool in_block(int k) const { return nodeBlock[k] >= 0; }

    std::vector<char> may_diverge() const {
        std::vector<char> d = reached;
        std::vector<char> funcDone(p.funcs.size(), 0);
        bool changed = true;
        while (changed) {
            changed = false;
            for (int b = 0; b < nb; b++) {
                int c = p.blocks[b].callee;
                if (!d[b] || c < 0 || c >= (int)p.funcs.size() || funcDone[c]) continue;
                int last = p.last_node(b);
                if (last == p.blocks[b].lab || !sb_is_call(p.nodes[last].s)) continue;
                funcDone[c] = 1;
                for (int x = p.funcs[c].first; x <= p.funcs[c].last && x < nb; x++) d[x] = 1;
                changed = true;
            }
        }
        return d;
    }

private:
    const SbProg &p;
    int nb;
    std::vector<int> nodeBlock;
    std::vector<std::vector<std::vector<int>>> reach;
    std::vector<int> defNode;
    std::vector<std::vector<int>> defIdOf;
    std::vector<char> nodeVarying;
    std::vector<int> scratch;
    std::vector<char> divergent, multiEnclosing, activeSucc, reached;
    std::vector<std::vector<uint64_t>> pdom;

    template <class F> void for_insts(int b, F f) const {
        for (int k = p.first_inst(b); k != p.blocks[b].eb; k = p.nodes[k].next)
            if (p.nodes[k].kind == SBN_INST) f(k);
    }

    typedef std::vector<std::vector<int>> RegDefs;

    RegDefs block_in(int b, const std::vector<RegDefs> &out) const {
        RegDefs st(NREG);
        for (int pr : p.blocks[b].pred)
            for (int r = 0; r < NREG; r++)
                for (int d : out[pr][r]) add_unique(st[r], d);
        return st;
    }

    void transfer(int b, RegDefs &st, bool record) {
        for_insts(b, [&](int k) {
            const SInst &s = p.nodes[k].s;
            if (record) {
                reach[k].assign(s.nregs, std::vector<int>());
                for (int i = 0; i < s.nregs; i++) {
                    int r = reg_index(s.regs[i]);
                    if (r >= 0 && !s.regs[i].def) reach[k][i] = st[r];
                }
            }
            bool guarded = s.pred >= 0 && !is_branch(s);
            for (int i = 0; i < s.nregs; i++) {
                int r = reg_index(s.regs[i]), d = defIdOf[k][i];
                if (r < 0 || d < 0) continue;
                if (!guarded) st[r].clear();
                add_unique(st[r], d);
            }
        });
    }

    void reaching_defs() {
        nodeBlock.assign(p.nodes.size(), -1);
        defIdOf.assign(p.nodes.size(), std::vector<int>());
        for (int b = 0; b < nb; b++)
            for_insts(b, [&](int k) {
                nodeBlock[k] = b;
                const SInst &s = p.nodes[k].s;
                defIdOf[k].assign(s.nregs, -1);
                for (int i = 0; i < s.nregs; i++)
                    if (s.regs[i].def && reg_index(s.regs[i]) >= 0) {
                        defIdOf[k][i] = (int)defNode.size();
                        defNode.push_back(k);
                    }
            });
        std::vector<RegDefs> out(nb, RegDefs(NREG));
        bool changed = true;
        while (changed) {
            changed = false;
            for (int b = 0; b < nb; b++) {
                RegDefs st = block_in(b, out);
                transfer(b, st, false);
                for (int r = 0; r < NREG; r++) {
                    std::sort(st[r].begin(), st[r].end());
                    if (st[r] != out[b][r]) changed = true;
                }
                out[b].swap(st);
            }
        }
        reach.assign(p.nodes.size(), std::vector<std::vector<int>>());
        for (int b = 0; b < nb; b++) {
            RegDefs st = block_in(b, out);
            transfer(b, st, true);
        }
    }

    void postdominators() {
        int words = (nb + 63) / 64;
        pdom.assign(nb, std::vector<uint64_t>(words, ~0ull));
        for (int b = 0; b < nb; b++)
            if (p.blocks[b].succ.empty()) {
                std::fill(pdom[b].begin(), pdom[b].end(), 0);
                pdom[b][b >> 6] |= 1ull << (b & 63);
            }
        bool changed = true;
        while (changed) {
            changed = false;
            for (int b = nb; b-- > 0;) {
                if (p.blocks[b].succ.empty()) continue;
                std::vector<uint64_t> n(words, ~0ull);
                for (int sc : p.blocks[b].succ)
                    for (int w = 0; w < words; w++) n[w] &= pdom[sc][w];
                n[b >> 6] |= 1ull << (b & 63);
                if (n != pdom[b]) {
                    pdom[b].swap(n);
                    changed = true;
                }
            }
        }
    }

    int closest_pdom(int b) const {
        for (int x = b + 1; x < nb && p.blocks[x].func == p.blocks[b].func; x++)
            if ((pdom[b][x >> 6] >> (x & 63)) & 1) return x;
        return -1;
    }

    void propagate_from(int start, int pd) {
        int diverge = start;
        std::vector<char> visited(nb, 0);
        std::vector<int> backedge;
        std::vector<std::pair<int, size_t>> stack;
        auto enter = [&](int b) {
            if (b == pd || scratch[b] == diverge || visited[b]) return;
            if (p.blocks[b].index < p.blocks[diverge].index) {
                backedge.push_back(diverge);
                diverge = b;
            }
            if (scratch[b] != -1) {
                if (activeSucc[scratch[b]]) multiEnclosing[b] = 1;
                if (p.blocks[scratch[b]].index < p.blocks[diverge].index) scratch[b] = diverge;
            } else {
                scratch[b] = diverge;
            }
            visited[b] = 1;
            reached[b] = 1;
            stack.push_back({b, 0});
        };
        enter(start);
        while (!stack.empty()) {
            int b = stack.back().first;
            size_t &next = stack.back().second;
            if (next < p.blocks[b].succ.size()) {
                enter(p.blocks[b].succ[next++]);
                continue;
            }
            stack.pop_back();
            if (diverge == b && !backedge.empty() && p.blocks[backedge.back()].index > p.blocks[diverge].index) {
                diverge = backedge.back();
                backedge.pop_back();
            }
        }
    }

    void propagate_divergence(int b, int pd) {
        for (int sc : p.blocks[b].succ) activeSucc[sc] = 1;
        for (int sc : p.blocks[b].succ)
            if (sc != pd) propagate_from(sc, pd);
        for (int sc : p.blocks[b].succ) activeSucc[sc] = 0;
    }

    bool same_invariant(const std::vector<int> &defs) const {
        const SInst &f = p.nodes[defNode[defs[0]]].s;
        for (int i = 0; i < f.nregs; i++)
            if (!f.regs[i].def) return false;
        const uint64_t noControl = (1ull << 41) - 1;
        for (int d : defs) {
            const Word &w = p.nodes[defNode[d]].s.w;
            if (w.lo != f.w.lo || (w.hi & noControl) != (f.w.hi & noControl)) return false;
        }
        return true;
    }

    bool visit(int b, int k) {
        const SInst &s = p.nodes[k].s;
        bool branch = is_branch(s) && k == p.last_node(b);
        bool vary = false;
        for (int i = 0; i < s.nregs && !vary; i++) {
            const SReg &r = s.regs[i];
            if (r.def || reg_index(r) < 0 || ((r.attr & SR_GUARD) && !branch)) continue;
            vary = operand_varying(k, i);
        }
        if (s.sc.sop == SOP_SM70_VOTE) vary = false;
        else if (varying_result(s.sc.sop)) vary = true;
        bool changed = false;
        if (vary && !nodeVarying[k]) {
            nodeVarying[k] = 1;
            changed = true;
        }
        if (branch && vary && !divergent[b]) {
            divergent[b] = 1;
            changed = true;

            propagate_divergence(b, s.sc.sop == SOP_SM70_RET ? -1 : closest_pdom(b));
        }
        return changed;
    }
};

}

std::vector<char> sb_varying_ldc(const SbProg &p) {
    Analysis a(p);
    a.run();
    std::vector<char> res(p.nodes.size(), 0);
    for (size_t k = 0; k < p.nodes.size(); k++) {
        const SInst &s = p.nodes[k].s;
        if (p.nodes[k].kind != SBN_INST || s.sc.sop != SOP_SM70_LDC || !a.in_block((int)k)) continue;
        for (int i = 0; i < s.nregs; i++)
            if (!s.regs[i].def && reg_index(s.regs[i]) >= 0 && s.regs[i].cls == RC_R) {
                res[k] = a.operand_varying((int)k, i);
                break;
            }
    }
    return res;
}

std::vector<char> sb_may_diverge(const SbProg &p) {
    Analysis a(p);
    a.run();
    return a.may_diverge();
}

void sb_ldc_latency(SbProg &p) {
    std::vector<char> v = sb_varying_ldc(p);
    for (size_t k = 0; k < v.size(); k++)
        if (v[k]) p.nodes[k].s.sc.latency = (int16_t)(2 * p.nodes[k].s.sc.latency);
}

}
}
}
