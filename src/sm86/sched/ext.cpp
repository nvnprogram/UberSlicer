
#include <algorithm>
#include <vector>

#include "sb.h"

namespace ub {
namespace sm86 {
namespace sched {

namespace {

const int SB_NONE = 7;

const int US_DRAIN = 0, US_WAIT0 = 16, US_WAIT1 = 17, US_WAIT11 = 27, US_WAIT1_EG = 1, US_WAIT15_EG = 15;
bool us_is_end_group(int u) { return u >= US_WAIT1_EG && u <= US_WAIT15_EG; }
bool us_is_no_end_group(int u) { return u >= US_WAIT1 && u <= US_WAIT11; }
int us_add_end_group(int u) { return us_is_no_end_group(u) ? u - US_WAIT0 : u; }

enum { BATCH_NONE = 0, BATCH_START = 1, BATCH_END = 4 };

int val_of(const Inst &i, const char *name, int dflt) {
    int v = val_index(i.cls, name);
    return v < 0 ? dflt : (int)get(i, v);
}

Word with_rel(const Word &w, long long bytes) {
    Inst in;
    if (!decode(w, &in)) return w;
    Operand o[MAX_OPNDS];
    int no = operands(in, o, MAX_OPNDS);
    for (int j = 0; j < no; j++)
        if (o[j].kind == O_REL && o[j].val >= 0) {
            set(in, o[j].val, bytes);
            break;
        }
    return in.w;
}

Word make_warpsync_all() {
    Word w = {0x0000000000007948ull, 0x000fc00003800000ull};
    Inst in;
    if (!decode(w, &in)) return w;
    int v = val_index(in.cls, "Sb");
    if (v >= 0) set(in, v, 0xffffffffll);
    return in.w;
}

SbNode new_inst(const Word &w, int stype) {
    SbNode n;
    n.kind = SBN_INST;
    build_sinst(w, stype, false, &n.s);
    n.s.number = -1;
    return n;
}

bool block_has(const SbProg &p, int b, int sop) {
    for (int k = p.first_inst(b); k != p.blocks[b].eb; k = p.nodes[k].next)
        if (p.nodes[k].s.sc.sop == sop) return true;
    return false;
}

}

int warpsync_after_break_regions(SbProg &p, int shader_type) {
    int applied = 0;
    std::vector<char> funcHasBreak(p.funcs.size(), 0), mayDiverge;
    bool programHasBreak = false, haveDiverge = false;

    for (size_t f = 0; f < p.funcs.size(); f++) {
        auto next_in_func = [&](int b) { return b + 1 <= p.funcs[f].last ? b + 1 : -1; };
        bool gen = false;
        int bpNext;
        for (int bp = p.funcs[f].first; bp >= 0 && bp <= p.funcs[f].last; bp = bpNext) {
            bool isMain = p.funcs[f].main;
            bpNext = next_in_func(bp);
            int bssy = -1;
            for (int k = p.first_inst(bp); k != p.blocks[bp].eb; k = p.nodes[k].next)
                if (p.nodes[k].s.sc.sop == SOP_SM70_BSSY) {
                    bssy = k;
                    break;
                }
            if (bssy < 0) continue;
            int sync = p.nodes[bssy].relBlock;
            if (sync < 0) continue;
            int first = p.first_inst(sync);
            if (first != p.blocks[sync].eb) {
                const SInst &s = p.nodes[first].s;
                if (s.sc.sop == SOP_SM70_WARPSYNC && (uint32_t)val_of(s.in, "Sb", 0) == 0xffffffffu) continue;
            }
            if (!haveDiverge) {
                mayDiverge = sb_may_diverge(p);
                haveDiverge = true;
            }

            if (mayDiverge[sync]) continue;
            if (bp > sync) {
                gen = true;
            } else {
                for (int in = bpNext; in >= 0 && in != sync && !gen; in = next_in_func(in)) {
                    int last = p.last_node(in);
                    if (block_has(p, in, SOP_SM70_BREAK)) {
                        funcHasBreak[f] = !isMain;
                        programHasBreak = !isMain;
                        gen = true;
                    } else if (last != p.blocks[in].lab && sb_is_call(p.nodes[last].s)) {
                        int c = p.blocks[in].callee;
                        if (c < 0) gen = programHasBreak;
                        else if (c < (int)funcHasBreak.size() && funcHasBreak[c]) gen = true;
                        funcHasBreak[f] = gen && !isMain;
                    }
                }
                bpNext = sync;
            }
            if (gen) {
                SbNode n = new_inst(make_warpsync_all(), shader_type);
                n.s.waitLatency = 1;
                p.insert_after(p.blocks[sync].lab, n);
                gen = false;
                applied++;
            }
        }
    }
    return applied;
}

void add_padding(SbProg &p, int shader_type) {
    const int instSize = 16, lineSize = 128, linesToPrefetch = 2;
    int count = 0;
    for (size_t b = 0; b < p.blocks.size(); b++)
        for (int k = p.first_inst((int)b); k != p.blocks[b].eb; k = p.nodes[k].next) count++;
    int nops = (lineSize * linesToPrefetch - ((count * instSize % lineSize) + instSize)) / instSize;
    int pad = p.insert_block_after((int)p.blocks.size() - 1);
    SbNode bra = new_inst(with_rel(make_bra(), -instSize), shader_type);
    bra.s.drain = 1;
    bra.s.waitLatency = 15;
    p.insert_after(p.blocks[pad].lab, bra);
    p.blocks[pad].target = pad;
    int nb = p.insert_block_after(pad);
    int at = p.blocks[nb].lab;
    for (int i = 0; i < nops; i++) {
        SbNode n = new_inst(make_nop(), shader_type);
        n.s.drain = 1;
        n.s.waitLatency = 15;
        at = p.insert_after(at, n);
    }
}

void set_opex(SbProg &p, int shader_type) {
    bool insidePix = false, firstInst = true;
    for (size_t b = 0; b < p.blocks.size(); b++)
        for (int k = p.first_inst((int)b); k != p.blocks[b].eb; k = p.nodes[k].next) {
            SInst &s = p.nodes[k].s;
            bool tex = (s.flags & GF_IS_TEX_BATCH) != 0;
            int u = s.drain ? US_DRAIN : s.endGroup ? s.waitLatency : US_WAIT0 + s.waitLatency;
            s.opWrSB = s.wrSB >= 0 ? s.wrSB : SB_NONE;
            s.opRdSB = s.rdSB >= 0 ? s.rdSB : SB_NONE;
            s.batchT = BATCH_NONE;

            if (shader_type == ST_PS && firstInst && !tex) {
                u = u == US_DRAIN ? US_WAIT15_EG : us_add_end_group(u);
                s.batchT = BATCH_START;
                insidePix = true;
            }
            if (tex) {
                u = us_add_end_group(u);
                if (insidePix) {
                    s.batchT = BATCH_END;
                    insidePix = false;
                }
            }
            int op = s.sc.sop;
            if (op == SOP_SM70_SETCTAID || op == SOP_SM70_SETLMEMBASE || op == SOP_SM70_ERRBAR) u = US_DRAIN;
            s.uschedInfo = (uint8_t)u;
            firstInst = false;
        }
}

namespace {

struct Collector {
    int reg = 0, size = -1;
    bool valid = false;
};
struct Lane {
    std::vector<Collector> c;
    int csize = 1;
};
typedef std::vector<Lane> Unit;

const int LANES = 4;

Unit make_unit(int lanes, int perLane, int csize) {
    Unit u(lanes);
    for (Lane &l : u) {
        l.c.resize(perLane);
        l.csize = csize;
    }
    return u;
}

enum { U_ALU_FMA, U_FP16, U_FMA64, U_IMMA, U_HMMA, U_DMMA, U_FP16_MMA, U_NUM };

struct Reuse {
    std::vector<Unit> units;
    Reuse() {
        units.push_back(make_unit(3, 2, 1));
        units.push_back(make_unit(3, 2, 1));
        units.push_back(make_unit(3, 1, 2));

        Unit mma = make_unit(4, 1, 1);
        mma[0].csize = 4;
        mma[1].csize = 2;
        mma[2].csize = 0;
        units.push_back(mma);
        units.push_back(mma);
        units.push_back(make_unit(2, 1, 4));
        units.push_back(make_unit(3, 1, 1));
    }
    void reset() {
        for (Unit &u : units)
            for (Lane &l : u)
                for (Collector &c : l.c) c.valid = false, c.size = -1;
    }
    void invalidate_reg(int reg) {
        for (Unit &u : units)
            for (Lane &l : u) {
                Collector &c = l.c[reg % (int)l.c.size()];
                if (c.reg <= reg && c.reg + (c.size - 1) >= reg) c.valid = false, c.size = -1;
            }
    }
    static bool collected(Lane &l, int reg, int n) {
        int sets = std::max(1, n / l.csize), per = n / sets, shift = l.csize - 1;
        bool ok = true;
        for (int i = 0; i < sets; i += l.csize) {
            const Collector &c = l.c[((reg + i) >> shift) % (int)l.c.size()];
            ok = ok && c.valid && ((reg + i) & 255) == c.reg && per == c.size;
        }
        return ok;
    }
    static void collect(Lane &l, int reg, int n) {
        int sets = std::max(1, n / l.csize), per = n / sets, shift = l.csize - 1;
        for (int i = 0; i < sets; i += l.csize) {
            Collector &c = l.c[((reg + i) >> shift) % (int)l.c.size()];
            c.reg = (reg + i) & 255;
            c.size = per;
            c.valid = true;
        }
    }
};

int collector_unit(const SInst &s) {
    uint32_t r = s.sc.res;
    auto has = [&](int b) { return ((r >> b) & 1) != 0; };
    int op = s.sc.sop;

    if (has(RES_ALU))
        return op == SOP_SM70_HSET2 || op == SOP_SM70_HSETP2 || op == SOP_SM82_HMNMX2 ? U_FP16 : U_ALU_FMA;
    if (has(RES_FMA) || has(RES_2XFMA)) return op == SOP_SM70_HADD2_F32 ? U_FP16 : U_ALU_FMA;
    if (has(RES_FP16C)) return U_FP16;
    if (has(RES_FMA64LITE) || has(RES_CLMAD)) return U_FMA64;
    if (has(RES_IMMA16816) || has(RES_IMMA16832) || has(RES_IMMASP16832)) return U_IMMA;
    if (has(RES_HMMA1688) || has(RES_HMMA16816) || has(RES_HMMASP1688)) return U_HMMA;
    if (has(RES_DMMA)) return U_DMMA;
    if (has(RES_HFMA2MMA)) return U_FP16_MMA;
    return U_NUM;
}

void lane_regs(const SInst &s, int reg[LANES], int nregs[LANES]) {
    for (int l = 0; l < LANES; l++) reg[l] = -1, nregs[l] = 0;
    Operand o[MAX_OPNDS];
    int no = operands(s.in, o, MAX_OPNDS);
    for (int j = 0; j < no; j++) {
        if (o[j].kind != O_GPR || o[j].role != R_USE || o[j].nregs == 0) continue;
        int sl = o[j].slot;
        int l = sl == S_SRCA ? 0 : sl == S_SRCB ? 1 : sl == S_SRCC ? 2 : sl == S_SRCE ? 3 : -1;
        if (l < 0) continue;
        reg[l] = o[j].reg;
        nregs[l] = o[j].nregs;
    }
}

}

void assign_reuse(SbProg &p) {
    Reuse r;
    for (int b = (int)p.blocks.size() - 1; b >= 0; b--) {
        r.reset();
        for (int k = p.last_node(b); k != p.blocks[b].lab; k = p.nodes[k].prev) {
            SInst &s = p.nodes[k].s;
            s.reuse = 0;
            if (us_is_end_group(s.uschedInfo) || s.uschedInfo == US_DRAIN || (s.flags & GF_PROHIBIT_REUSE)) {
                r.reset();
            } else {
                for (int q = 0; q < s.nregs; q++)
                    if (s.regs[q].def && s.regs[q].cls == RC_R) r.invalidate_reg(s.regs[q].no);
            }
            int unit = collector_unit(s);
            if (unit == U_NUM) continue;
            int reg[LANES], n[LANES];
            lane_regs(s, reg, n);
            Unit &u = r.units[unit];
            for (int l = 0; l < LANES && l < (int)u.size(); l++)
                if (reg[l] >= 0 && u[l].csize > 0 && Reuse::collected(u[l], reg[l], n[l])) s.reuse |= 1 << l;
            for (int l = 0; l < LANES && l < (int)u.size(); l++)
                if (reg[l] >= 0 && u[l].csize > 0) Reuse::collect(u[l], reg[l], n[l]);
        }
    }
}

void relocate(SbProg &p) {

    std::vector<int> pos(p.nodes.size(), -1), blockPos(p.blocks.size() + 1, 0);
    int at = 0;
    for (size_t b = 0; b < p.blocks.size(); b++) {
        blockPos[b] = at;
        for (int k = p.first_inst((int)b); k != p.blocks[b].eb; k = p.nodes[k].next) pos[k] = at++;
    }
    blockPos[p.blocks.size()] = at;
    for (size_t b = 0; b < p.blocks.size(); b++)
        for (int k = p.first_inst((int)b); k != p.blocks[b].eb; k = p.nodes[k].next) {
            SbNode &n = p.nodes[k];
            int t = n.relBlock;
            if (k == p.last_node((int)b) && sb_is_jmp(n.s) && p.blocks[b].target >= 0) t = p.blocks[b].target;
            if (t < 0) continue;
            Word w = with_rel(n.s.w, 16ll * (blockPos[t] - (pos[k] + 1)));
            if (w.lo != n.s.w.lo || w.hi != n.s.w.hi) {
                n.s.w = w;
                decode(w, &n.s.in);
            }
        }
}

int write_control(SbProg &p) {
    int bad = 0;
    for (size_t b = 0; b < p.blocks.size(); b++)
        for (int k = p.first_inst((int)b); k != p.blocks[b].eb; k = p.nodes[k].next) {
            SInst &s = p.nodes[k].s;
            Inst in;
            if (!decode(s.w, &in)) {
                bad++;
                continue;
            }
            int64_t v[MAX_VALS];
            get_all(in, v);
            auto put = [&](const char *name, int64_t x) {
                int i = val_index(in.cls, name);
                if (i >= 0) v[i] = x;
            };
            put("usched_info", s.uschedInfo);
            put("batch_t", s.batchT);
            put("req_bit_set", s.reqSB);
            put("src_rel_sb", s.opRdSB);
            put("dst_wr_sb", s.opWrSB);
            put("reuse_src_a", s.reuse & 1);
            put("reuse_src_b", (s.reuse >> 1) & 1);
            put("reuse_src_c", (s.reuse >> 2) & 1);
            put("reuse_src_e", (s.reuse >> 3) & 1);
            Word w, keep = unused_mask(in.cls);
            if (!encode(in.cls, v, &w)) {
                bad++;
                continue;
            }
            w.lo |= s.w.lo & keep.lo;
            w.hi |= s.w.hi & keep.hi;
            s.w = w;
        }
    return bad;
}

}
}
}
