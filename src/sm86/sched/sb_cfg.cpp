
#include <algorithm>
#include <cstdlib>
#include <cstring>

#include "sb.h"

namespace ub {
namespace sm86 {
namespace sched {

int SbProg::add_block(int func) {
    SbBlock b;
    b.func = func;
    int bi = (int)blocks.size();
    SbNode lab, eb;
    lab.kind = SBN_LAB;
    eb.kind = SBN_EB;
    lab.block = eb.block = bi;
    b.lab = (int)nodes.size();
    nodes.push_back(lab);
    b.eb = (int)nodes.size();
    nodes.push_back(eb);
    nodes[b.lab].next = b.eb;
    nodes[b.eb].prev = b.lab;
    if (bi > 0) {
        nodes[b.lab].prev = blocks[bi - 1].eb;
        nodes[blocks[bi - 1].eb].next = b.lab;
    }
    blocks.push_back(b);
    return bi;
}

int SbProg::append_inst(int block, const SInst &s) {
    SbNode n;
    n.kind = SBN_INST;
    n.s = s;
    return insert_after(nodes[blocks[block].eb].prev, n);
}

int SbProg::insert_after(int at, const SbNode &n) {
    int k = (int)nodes.size();
    nodes.push_back(n);
    SbNode &x = nodes[k];
    x.block = nodes[at].block;
    x.prev = at;
    x.next = nodes[at].next;
    if (x.next >= 0) nodes[x.next].prev = k;
    nodes[at].next = k;
    return k;
}

int SbProg::insert_block_after(int b) {
    int nb = b + 1;
    for (SbNode &n : nodes) {
        if (n.block > b) n.block++;
        if (n.relBlock > b) n.relBlock++;
    }
    for (SbBlock &x : blocks) {
        if (x.target > b) x.target++;
        for (int &t : x.jmxTargets)
            if (t > b) t++;
    }
    for (SbFunc &f : funcs) {
        if (f.first > b) f.first++;
        if (f.last >= b) f.last++;
    }
    SbBlock x;
    x.func = blocks[b].func;
    SbNode lab, eb;
    lab.kind = SBN_LAB;
    eb.kind = SBN_EB;
    lab.block = eb.block = nb;
    int after = blocks[b].eb, next = nodes[after].next;
    x.lab = (int)nodes.size();
    nodes.push_back(lab);
    x.eb = (int)nodes.size();
    nodes.push_back(eb);
    nodes[after].next = x.lab;
    nodes[x.lab].prev = after;
    nodes[x.lab].next = x.eb;
    nodes[x.eb].prev = x.lab;
    nodes[x.eb].next = next;
    if (next >= 0) nodes[next].prev = x.eb;
    blocks.insert(blocks.begin() + nb, x);
    return nb;
}

void SbProg::unlink(int node) {
    SbNode &x = nodes[node];
    if (x.prev >= 0) nodes[x.prev].next = x.next;
    if (x.next >= 0) nodes[x.next].prev = x.prev;
    x.prev = x.next = -1;
}

static bool branch_has_cond(const SInst &s) {
    for (int k = 0; k < s.nregs; k++) {
        const SReg &r = s.regs[k];
        if (!r.def && (r.cls == RC_P || r.cls == RC_UP) && !(r.attr & SR_GUARD)) return true;
    }
    return false;
}

bool sb_is_jmp(const SInst &s) { return s.sc.sop == SOP_SM70_BRA; }
bool sb_is_cond_flow(const SInst &s) { return sb_is_jmp(s) && (branch_has_cond(s) || s.pred >= 0); }
bool sb_is_jmx(const SInst &s) {
    int o = s.sc.sop;
    return o == SOP_SM70_BRX || o == SOP_SM73_BRXU || o == SOP_SM70_JMX;
}
bool sb_is_call(const SInst &s) { return s.sc.sop == SOP_SM70_CALL; }
bool sb_ret_is_exit(const SInst &s) { return s.sc.sop == SOP_SM70_EXIT; }
bool sb_is_ret(const SInst &s) {
    return s.sc.sop == SOP_SM70_RET || (s.sc.sop == SOP_SM70_EXIT && !branch_has_cond(s) && s.pred < 0);
}
bool sb_is_retc(const SInst &s) { return s.sc.sop == SOP_SM70_EXIT && (branch_has_cond(s) || s.pred >= 0); }

namespace {

void add_edge(SbProg &p, int from, int to) {
    SbBlock &a = p.blocks[from];
    SbBlock &b = p.blocks[to];
    a.succ.insert(a.succ.begin(), to);
    b.pred.insert(b.pred.begin(), from);
    b.predCount++;

    if (b.index != 0) p.hasLoops = true;
}

void add_edge_distinct(SbProg &p, int from, int to) {
    const std::vector<int> &s = p.blocks[from].succ;
    if (std::find(s.begin(), s.end(), to) == s.end()) add_edge(p, from, to);
}

struct LoopEntry {
    int head, tail;
};

void find_loops(SbProg &p) {
    int nb = (int)p.blocks.size();
    auto bix = [&](int index) -> SbBlock & { return p.blocks[index - 1]; };
    std::vector<LoopEntry> stack(1, LoopEntry{0, 0});
    int numLoopEntries = 1;
    int curLoopHead = 0, curLoopTail = 0;
    int nestLevel = 0;
    int entryIdx = -1;
    bool AdjustInLoop = false;
    for (int ii = nb; ii >= 1; ii--) {
        SbBlock &bp = bix(ii);
        if (bp.loopRegion != 0) {
            if (numLoopEntries >= (int)stack.size()) stack.resize(stack.size() * 2);
            entryIdx = numLoopEntries;
            if (stack[numLoopEntries - 1].head < bp.loopRegion) {
                nestLevel++;
                bp.offset = stack[numLoopEntries - 1].tail;
            } else if (stack[numLoopEntries - 1].head == bp.loopRegion) {
                entryIdx = -1;
                if (stack[numLoopEntries - 1].tail < 0) nestLevel++;
                bp.offset = bix(std::abs(stack[numLoopEntries - 1].tail)).offset;
                stack[numLoopEntries - 1].tail = bp.index;
            } else {
                p.hasIrregularLoops = true;
                bp.offset = bix(std::abs(stack[numLoopEntries - 1].tail)).offset;
                int jj;
                for (jj = numLoopEntries - 1; jj >= 0; jj--) {
                    if (stack[jj].head <= bp.loopRegion) break;
                    if (stack[jj].tail > 0) {
                        stack[jj].tail = -stack[jj].tail;
                        nestLevel--;
                        AdjustInLoop = true;
                    }
                }
                if (jj < 0 || stack[jj].head != bp.loopRegion) {
                    entryIdx = 0;
                    for (jj = numLoopEntries - 1; jj >= 0; jj--) {
                        if (stack[jj].head < bp.loopRegion) {
                            entryIdx = jj + 1;
                            break;
                        }
                        stack[jj + 1] = stack[jj];
                    }
                } else {
                    entryIdx = -1;
                }
            }
            curLoopHead = bp.loopRegion;
            curLoopTail = bp.index;
            if (entryIdx >= 0) {
                stack[entryIdx].head = curLoopHead;
                stack[entryIdx].tail = curLoopTail;
                for (int jj = curLoopHead + 1; jj <= curLoopTail; jj++) {
                    for (int pr : bix(jj).pred) {
                        const SbBlock &q = p.blocks[pr];
                        if (q.index < curLoopHead || q.index > curLoopTail) {
                            p.hasIrregularLoops = true;
                            break;
                        }
                    }
                }
                if (entryIdx != numLoopEntries) stack[entryIdx].tail = -curLoopTail;
                numLoopEntries++;
            }
        }

        bool PartOfLoop = false;
        SbBlock *succInInnermostLoop = nullptr;
        int ixOuterTail = 0;
        bool BlockIsLoopTail = (bp.index == curLoopTail);
        if (BlockIsLoopTail && entryIdx >= 0 && stack[entryIdx].tail < 0) curLoopTail = -curLoopTail;
        int idxLimit = BlockIsLoopTail ? curLoopHead : bp.index;
        for (int idx = bp.index; idx >= idxLimit && idx >= 1; idx--) {
            const SbBlock &src = bix(idx);
            for (int sv : src.succ) {
                SbBlock *bp3 = &p.blocks[sv];
                if (bp3->loopHdrIdx == 0) continue;
                auto outside = [&]() {
                    return bp.index < bp3->loopHdrIdx || (BlockIsLoopTail && bp.index == bp3->loopHdrIdx) ||
                           (BlockIsLoopTail && curLoopHead < bp3->loopHdrIdx);
                };
                while (outside()) {
                    if (bp3->offset == 0) break;
                    bp3 = &bix(bp3->offset);
                }
                if (outside()) continue;
                if (succInInnermostLoop == nullptr || std::abs(bp3->loopRegion) < ixOuterTail) {
                    ixOuterTail = std::abs(bp3->loopRegion);
                    succInInnermostLoop = bp3;
                }
            }
        }
        if (BlockIsLoopTail) {
            PartOfLoop = true;
            if (succInInnermostLoop) {
                if (curLoopHead == succInInnermostLoop->loopHdrIdx) {
                    nestLevel = succInInnermostLoop->loopNestLvl;
                    bp.offset = succInInnermostLoop->offset;
                } else {
                    nestLevel = succInInnermostLoop->loopNestLvl + 1;
                    bp.offset = std::abs(succInInnermostLoop->loopRegion);
                }
            } else {
                nestLevel = 1;
                bp.offset = 0;
            }
        } else if (numLoopEntries > 1) {
            if (succInInnermostLoop) {
                PartOfLoop = true;
                curLoopHead = succInInnermostLoop->loopHdrIdx;
                curLoopTail = succInInnermostLoop->loopRegion;
                nestLevel = succInInnermostLoop->loopNestLvl;
                bp.offset = succInInnermostLoop->offset;
            } else {
                bp.offset = 0;
            }
        }
        if (PartOfLoop) {
            bp.loopHdrIdx = curLoopHead;
            bp.loopRegion = curLoopTail;
            bp.loopNestLvl = nestLevel;
        }
        if (stack[numLoopEntries - 1].head == bp.index) {
            if (stack[numLoopEntries - 1].tail > 0) nestLevel--;
            numLoopEntries--;
            if (numLoopEntries < 1) numLoopEntries = 1;
            curLoopHead = stack[numLoopEntries - 1].head;
            curLoopTail = stack[numLoopEntries - 1].tail;
        }
    }
    if (AdjustInLoop) {
        for (int ii = nb; ii >= 1; ii--) {
            SbBlock &bp = bix(ii);
            if (bp.loopRegion != 0 && bp.loopHdrIdx >= 1) bp.loopNestLvl = bix(bp.loopHdrIdx).loopNestLvl;
        }
    }
}

int samram_kind(const SInst &s) {
    if (!s.ok || s.in.cls != 91) return 0;
    int st = val_index(s.in.cls, "cbu_state"), pq = val_index(s.in.cls, "pquad");
    const int CBU_MACTIVE = 26;
    if (st < 0 || pq < 0 || get(s.in, st) != CBU_MACTIVE) return 0;
    return get(s.in, pq) ? 1 : 2;
}

void mark_samram(SbProg &p) {
    bool in = false;
    for (SbBlock &b : p.blocks) {
        bool sam = false, ram = false;
        for (int k = p.nodes[b.lab].next; k != b.eb; k = p.nodes[k].next) {
            int kind = samram_kind(p.nodes[k].s);
            sam |= kind == 1;
            ram |= kind == 2;
        }
        b.samRam = in || ram;
        if (ram) in = false;
        if (sam) in = true;
    }
}

}

void analyze_cfg(SbProg &p) {
    for (SbBlock &b : p.blocks) {
        b.index = b.loopHdrIdx = b.loopRegion = b.loopNestLvl = b.offset = 0;
        b.pred.clear();
        b.succ.clear();
        b.predCount = 0;
    }
    p.hasLoops = p.hasIrregularLoops = p.hasCalls = false;
    int index = 0;
    for (const SbFunc &f : p.funcs) {
        bool FallThru = false;
        int cur = -1;
        for (int b = f.first; b <= f.last; b++) {
            if (FallThru) add_edge_distinct(p, cur, b);
            cur = b;
            p.blocks[b].index = ++index;
            FallThru = true;
            for (int k = p.first_inst(b); k != p.blocks[b].eb; k = p.nodes[k].next) {
                const SInst &s = p.nodes[k].s;
                if (sb_is_jmp(s)) {
                    if (!sb_is_cond_flow(s)) FallThru = false;
                    int t = p.blocks[b].target;
                    if (t < 0) continue;
                    add_edge(p, cur, t);
                    if (p.blocks[t].index != 0) p.blocks[cur].loopRegion = p.blocks[t].index;
                } else if (sb_is_jmx(s)) {
                    FallThru = false;
                    for (int t : p.blocks[b].jmxTargets) add_edge_distinct(p, cur, t);
                } else if (sb_is_call(s)) {
                    p.hasCalls = true;
                } else if (sb_is_ret(s)) {
                    FallThru = false;
                }
            }
        }
    }
    bool abi = false;
    for (const SbFunc &f : p.funcs) abi |= f.abi;
    p.hasBackEdge = p.hasLoops || (p.hasCalls && !abi);
    if (p.hasLoops) find_loops(p);
    mark_samram(p);
}

bool loop_single_entry(const SbProg &p, int bixHead, int bixTail) {
    for (int bix = bixTail; bix >= bixHead; bix--) {
        if (bix == bixHead || bix < 1 || bix > (int)p.blocks.size()) continue;
        for (int pr : p.blocks[bix - 1].pred) {
            int i = p.blocks[pr].index;
            if (i < bixHead || i > bixTail) return false;
        }
    }
    return true;
}

}
}
}
