
#include "emit.h"

namespace ub { extern long long g_r3_miss; }

extern "C" {
int uber_phase_b(unsigned char *bc, unsigned int constOff);
}

namespace ub {

static const u64 W_EXIT = 0xe30000000007000full;
static const u64 W_BRA_SELF = 0xe2400fffff87000full;
static const u64 W_NOP = 0x50b0000000070f00ull;
static const u64 MOV_TMPL = 0x5c9807800ff70000ull;

bool g_exitfold = false;
long long g_exitfold_hit = 0, g_exitfold_miss = 0;

bool g_copyprop = false;

bool g_lmem_compact = true;
bool g_lmem_promote = true;

bool g_lmem_copyprop = true;

void phase_b(std::vector<u8> &bc, u32 co) {
    int n = uber_phase_b(bc.data(), co);
    if (n < 0) fail("phase B failed");
}

static const u64 LDC_REMAT_TEMPLATE = 0x010000000000F000ull;

struct Ctx {
    Program *p;
    Spec *sp;
    const RunRes *R;
    Alloc *al;
    std::unordered_map<int, int> *wr;
    std::unordered_map<int, int> *lmparent;

    int regmap(int r, bool out_tbl, int i) const {
        int k;
        auto oit = al->ordn.find(i);
        if (oit == al->ordn.end()) return r;
        k = oit->second;
        const DefMap &tbl = out_tbl ? al->st_out[(size_t)k] : al->st_in[(size_t)k];
        auto it = tbl.find(r);
        if (it == tbl.end()) return r;
        int w = al->uf.find(it->second);
        auto lp = lmparent->find(w);
        if (lp != lmparent->end()) w = lp->second;
        auto wit = wr->find(w);
        return (wit != wr->end()) ? wit->second : r;
    }
};

static void true_src_regs(const Program &p, int i, std::set<int> &out) {
    const OpSets &T = S();
    int nm = p.op[i];
    out.clear();
    if (T.tex_bases[(size_t)nm]) {
        RSet t; tex_uses(p.q[i], nm, t);
        std::vector<int> v; t.list(v);
        out.insert(v.begin(), v.end());
        return;
    }
    int offs[8];
    int m = gpr_src_offsets(p.q[i], nm, p.props[i], offs);
    for (int k = 0; k < m; k++) out.insert((int)((p.q[i] >> offs[k]) & 0xFF));
    if (T.store_ops[(size_t)nm] && T.no_dest[(size_t)nm])
        out.insert((int)(p.q[i] & 0xFF));
}

static void check_operands(Ctx &C, int i, u64 q) {
    const Program &p = *C.p;
    Spec &sp = *C.sp;
    const RunRes &R = *C.R;
    int nm = p.op[i];

    int nm_e = decode_op(q);
    unsigned pr_e = decode_props(q);
    RSet d, md, u;
    Program::du_word(q, nm_e, pr_e, d, md, u);
    int spur = spurious_pred(nm_e, q);

    int spur_w = spurious_pred(nm, p.q[i]);

    std::set<int> got;
    {
        std::vector<int> v; u.list(v);
        for (int r : v) if (r < LMBIT && r != spur) got.insert(r);
    }

    Tri guard = R.guard[(size_t)i];
    const EMap &env = R.env[(size_t)i];
    const VMap &vals = R.vals[(size_t)i];
    bool rw = !sp.norw[(size_t)i];
    bool texop = sp.tex_rw[(size_t)i];
    int gp = -1;
    if (guard == TRI_T && !sp.nopred[(size_t)i] && sp.pnum[(size_t)i] != PT)
        gp = PREG + sp.pnum[(size_t)i];

    std::set<int> tsrc;
    bool tsrc_done = false;
    std::set<int> want;
    int cbslot = sp.cbfold_slot(i, env);
    int cbreg = (cbslot >= 0) ? (int)((p.q[i] >> cbslot) & 0xFF) : -1;
    std::vector<int> uses;

    if (!R.fmac.empty() && R.fmac[(size_t)i] >= 0) sp.fmac_uses(R, i, uses);
    else p.uses[i].list(uses);
    for (int r : uses) {
        if (r >= LMBIT || r == spur_w || r == gp) continue;
        if (r == cbreg) continue;
        if (r >= PREG) {
            if (guard != TRI_T && p.maydefs[i].has(r))
                want.insert(C.regmap(r, true, i));
            else if (!vmap_get(vals, r))
                want.insert(C.regmap(r, false, i));
            continue;
        }
        if (guard == TRI_T) {
            const std::vector<int> &ms = sp.maydef_set[(size_t)i];
            if (std::binary_search(ms.begin(), ms.end(), r)) continue;
        } else if (p.maydefs[i].has(r)) {
            want.insert(C.regmap(r, true, i));
            if (!tsrc_done) { true_src_regs(p, i, tsrc); tsrc_done = true; }
            if (!tsrc.count(r)) continue;
        }
        const u32 *x = vmap_get(vals, r);
        if (rw && !texop && x && *x == 0) continue;
        int32_t a = r;
        if (rw) {
            auto it = env.find(r);
            if (it != env.end()) a = it->second;
        }
        if (a < 0) a = r;
        if (a == RZ) {
            if (!texop) continue;
            a = r;
        }
        want.insert(C.regmap(a, false, i));
    }
    want.erase(RZ);
    if (got != want) {
        std::string gs, ws;
        for (int r : got) gs += std::to_string(r) + " ";
        for (int r : want) ws += std::to_string(r) + " ";
        fail("operand mismatch at %d (%s): emitted reads [%s], analysis "
             "assumed [%s]", i, op_name(nm), gs.c_str(), ws.c_str());
    }

    if (R.fmac.empty() || R.fmac[(size_t)i] < 0) {
        const OpSets &T = S();
        int poffs[8];
        int pm = pred_src_offsets(nm, p.props[i], poffs);
        for (int k = 0; k < pm; k++) {
            int off = poffs[k];
            int pn = (int)((p.q[i] >> off) & 7);
            if (pn == PT || PREG + pn == gp || T.pred39_spurious[(size_t)nm])
                continue;
            if (off == 39 && T.pred39_gpr[(size_t)nm]) continue;
            Tri val = sp.predval(vals, pn, (int)((p.q[i] >> (off + 3)) & 1));
            if (val == TRI_U) continue;
            int en = (int)((q >> off) & 7), einv = (int)((q >> (off + 3)) & 1);
            if (en != PT || einv != (val == TRI_F ? 1 : 0))
                fail("predicate literal at %d (%s) bit %d reads %s%s, the "
                     "analysis has %s", i, op_name(nm), off, einv ? "!" : "",
                     en == PT ? "PT" : "a register", val ? "true" : "false");
        }
    }

    std::set<int> gotd, wantd;
    {
        RSet dm = d; dm.unite(md);
        std::vector<int> v; dm.list(v);
        for (int r : v) if (r < LMBIT) gotd.insert(r);
    }
    {
        std::vector<int> v; sp.dall_mask[(size_t)i].bits(v);
        for (int r : v) if (r < LMBIT) wantd.insert(C.regmap(r, true, i));
    }
    if (gotd != wantd) {
        std::string gs, ws;
        for (int r : gotd) gs += std::to_string(r) + " ";
        for (int r : wantd) ws += std::to_string(r) + " ";
        fail("destination mismatch at %d (%s): emitted writes [%s], analysis "
             "assumed [%s]", i, op_name(nm), gs.c_str(), ws.c_str());
    }
}

typedef std::function<std::pair<int, int>(int, int)> OptMap;

static u64 rewrite(Ctx &C, int i, OptMap &optmap) {
    const OpSets &T = S();
    const Program &p = *C.p;
    Spec &sp = *C.sp;
    const RunRes &R = *C.R;
    u64 q = p.q[i];
    int nm = p.op[i];
    unsigned props = p.props[i];

    if (!R.fmac.empty() && R.fmac[(size_t)i] >= 0) {
        q = sp.fmac_word(R, i, R.fmac[(size_t)i], R.fmac_slot[(size_t)i]);
        nm = decode_op(q);
        props = decode_props(q);
    }
    Tri guard = R.guard[(size_t)i];
    const VMap &v = R.vals[(size_t)i];
    const EMap &env = R.env[(size_t)i];
    bool rw = !sp.norw[(size_t)i];

    int gp = -1;
    if (!T.no_pred[(size_t)nm]) {
        int pn = (int)((q >> 16) & 7);
        if (guard == TRI_T) {
            if (pn != PT || ((q >> 19) & 1)) {
                q = setbits(q, 16, 3, PT);
                q = setbits(q, 19, 1, 0);
            }
            if (pn != PT) gp = PREG + pn;
        } else if (guard == TRI_F) {
            fail("emitting a provably-dead instruction %d", i);
        } else {
            if (pn != PT) {
                int r = C.regmap(PREG + pn, false, i);
                if (r != PREG + pn) q = setbits(q, 16, 3, (u64)(r - PREG));
            }
        }
    }

    int cbslot = sp.cbfold_slot(i, env);
    if (!T.tex_bases[(size_t)nm]) {
        int offs[10];
        int m = gpr_src_offsets(q, nm, props, offs);
        if (T.store_ops[(size_t)nm] && T.no_dest[(size_t)nm]) offs[m++] = 0;
        for (int k = 0; k < m; k++) {
            int o = offs[k];
            if (o == cbslot) continue;
            int r = (int)((q >> o) & 0xFF);
            if (r == RZ) continue;
            const u32 *x = vmap_get(v, r);
            if (rw && x && *x == 0) { q = set_field8(q, o, RZ); continue; }
            int32_t a = r;
            if (rw) {
                auto it = env.find(r);
                if (it != env.end()) a = it->second;
            }
            if (a < 0) a = r;
            if (a == RZ) { q = set_field8(q, o, RZ); continue; }
            q = set_field8(q, o, C.regmap(a, false, i));
        }
        int poffs[8];
        int pm = pred_src_offsets(nm, props, poffs);
        for (int k = 0; k < pm; k++) {
            int off = poffs[k];
            int pn = (int)((q >> off) & 7);
            if (pn == PT) continue;
            int key = PREG + pn;
            if (key == gp || T.pred39_spurious[(size_t)nm]) continue;

            if (off == 39 && T.pred39_gpr[(size_t)nm]) continue;
            const u32 *x = vmap_get(v, key);
            if (x) {
                if (!T.pred_src_ok[(size_t)nm])
                    fail("%s reads a known predicate at bit %d and is not on "
                         "the literal-rewrite list", op_name(nm), off);

                bool inv = (q >> (off + 3)) & 1;
                bool val = (*x != 0) != inv;
                q = setbits(q, off, 3, PT);
                q = setbits(q, off + 3, 1, val ? 0 : 1);
            } else {
                q = setbits(q, off, 3, (u64)(C.regmap(key, false, i) - PREG));
            }
        }
    } else if (rw) {

        for (int o : {8, 20}) {
            int r = (int)((q >> o) & 0xFF);
            if (r == RZ) continue;
            int32_t a = r;
            auto it = env.find(r);
            if (it != env.end()) a = it->second;
            if (a < 0 || a == RZ) a = r;
            q = set_field8(q, o, C.regmap(a, false, i));
        }
    }

    if (!T.tex_bases[(size_t)nm] && rw) {
        RSet dset = p.defs[i];
        dset.unite(p.maydefs[i]);
        std::vector<int> all; dset.list(all);
        std::vector<int> dsts;
        for (int r : all) if (r < PREG) dsts.push_back(r);
        if (dsts.size() == 1) {
            int d = dsts[0];
            if ((int)(q & 0xFF) == d) q = set_field8(q, 0, C.regmap(d, true, i));
        } else if (dsts.size() > 1) {
            int base = (int)(q & 0xFF);
            bool consec = true;
            for (size_t k = 0; k < dsts.size(); k++)
                if (dsts[k] != base + (int)k) { consec = false; break; }
            if (!consec)
                fail("multi-register destination at %d is not a consecutive "
                     "group", i);
            int nb = C.regmap(base, true, i);
            if (nb != base)
                fail("consecutive destination group at %d was re-registered", i);
        }
    }

    if (cbslot >= 0) {
        int r0 = (int)((p.q[i] >> cbslot) & 0xFF);
        auto it = env.find(r0);
        if (it == env.end() || it->second >= 0)
            fail("cbfold: slot %d of instruction %d is not a cbuf marker",
                 cbslot, i);
        int32_t v = CBBASE - it->second;
        int b = (int)((u32)v >> 20), o = (int)(v & 0xFFFFF);
        if (b == sp.bank || b == 1) {
            std::pair<int, int> nn = optmap(b, o);
            b = nn.first; o = nn.second;
        }
        if (cbslot == 39) {
            int rb = (int)((q >> 20) & 0xFF);
            q = set_field8(q, 39, rb);
            q = setbits(q, 59, 5, CBUF_SRCC_TOP5);
        } else {
            q = setbits(q, 59, 5, CBUF_SRCB_TOP5);
        }
        q = setbits(q, 20, 14, (u64)(o >> 2));
        q = setbits(q, 34, 5, (u64)b);
    }

    if ((T.alu_cbuf[(size_t)nm] && srcb_form(q) == FORM_CBUF) ||
        (T.alu_cbuf_srcc[(size_t)nm] && srcc_form(q))) {
        int b = cbuf_bank(q), o = cbuf_off(q);
        if (b == sp.bank || b == 1) {
            std::pair<int, int> nn = optmap(b, o);
            q = setbits(q, 34, 5, (u64)nn.first);
            q = setbits(q, 20, 14, (u64)(nn.second >> 2));
        }
    }

    if (nm == T.O_Ldc) {
        LdcFields f = ldc_fields(q);
        if (f.bank == sp.bank || f.bank == 1) {
            LdcFields f0 = ldc_fields(p.q[i]);
            u32 base = 0, k = 0;
            bool have = (f0.mode == 0) && (((p.q[i] >> 48) & 7) == 4) &&
                        mem_data_regs(p.q[i], nm) == 1;
            if (have && f0.ra != RZ) {
                const u32 *x = vmap_get(R.vals[(size_t)i], f0.ra);
                if (x) base = *x; else have = false;
            }
            if (have)
                have = p.blob_u32((int)((base + (u32)f0.off) & M32), &k);
            if (!have)
                fail("LDC from bank %d survived at %d and its value is not "
                     "proved -- the computed jump is live", f.bank, i);
            check_operands(C, i, q);
            int rd = (int)(q & 0xFF);
            u64 pf = (q >> 16) & 0xF;
            return LDC_REMAT_TEMPLATE | (u64)(rd & 0xFF) | (pf << 16) |
                   ((u64)k << 20);
        }
    }

    check_operands(C, i, q);
    return q;
}

static void remat(Ctx &C, int i, std::vector<u64> &out) {
    const Program &p = *C.p;
    const RunRes &R = *C.R;
    if (R.guard[(size_t)i] == TRI_T) return;
    const EMap &e = R.env[(size_t)i];
    std::vector<int> mds; p.maydefs[i].list(mds);
    for (int r : mds) {
        if (r >= PREG) continue;
        int32_t a = r;
        auto it = e.find(r);
        if (it != e.end()) a = it->second;
        if (a < 0 || a == r) continue;
        int d = C.regmap(r, true, i), s = C.regmap((int)a, false, i);
        if (d == s) continue;
        u64 q = set_field8(set_field8(MOV_TMPL, 0, d), 20, s);
        RSet dd, mdd, uu;
        Program::du_word(q, decode_op(q), decode_props(q), dd, mdd, uu);
        RSet want;
        want.add(d);
        RSet wantu;
        if (s != RZ) wantu.add(s);
        if (!(dd == want) || !(uu == wantu))
            fail("rematerialising MOV R%d, R%d decoded wrong", d, s);
        out.push_back(q);
    }
}

static void check_cbuf(Spec &sp, const std::vector<u64> &words, size_t blobsz) {
    std::vector<std::string> bad;
    for (size_t k = 0; k < words.size(); k++) {
        u64 q = words[k];
        if (!q) continue;
        int nm = decode_op(q);
        int b, o;
        if (!cbuf_read_of(q, nm, &b, &o)) continue;
        char buf[256];
        if (b == sp.bank) {
            snprintf(buf, sizeof buf,
                     "slot %zu %s reads the option bank c[%#x][%#x]", k,
                     op_name(nm), b, o);
            bad.push_back(buf);
        } else if (b == 1 && (size_t)(o + 4) > blobsz) {
            snprintf(buf, sizeof buf,
                     "slot %zu %s reads c[0x1][%#x], past the %zu-byte "
                     "relocated blob", k, op_name(nm), o, blobsz);
            bad.push_back(buf);
        }
    }
    if (!bad.empty()) {
        std::string s;
        for (size_t k = 0; k < bad.size() && k < 8; k++) s += "\n  " + bad[k];
        fail("%zu unrelocated constant-buffer read(s):%s", bad.size(), s.c_str());
    }
}

struct LmFrame {
    std::unordered_map<int, int> map;
    int size_dw = 0;
};

static void lm_build_frame(Program &uber, Spec &sp,
                           const std::vector<int> &kept, LmFrame &F) {
    const OpSets &T = S();
    UF uf;
    std::map<int, int> widest;
    std::set<int> touched;
    for (int i : kept) {
        if (!T.local_ops[(size_t)uber.op[i]]) continue;
        const LmSlot &s = sp.lm[(size_t)i];
        if (!s.valid) fail("lmem: instruction %d has no constant slot", i);
        for (int k = 0; k < s.w; k++) {
            touched.insert(s.off + k);
            if (k) uf.unite(s.off, s.off + k);
            int &m = widest[s.off + k];
            if (s.w > m) m = s.w;
        }
    }
    std::map<int, std::vector<int>> cl;
    for (int d : touched) cl[uf.find(d)].push_back(d);

    struct Cluster { int lo, hi, align; std::vector<int> members; };
    std::vector<Cluster> cs;
    for (auto &pr : cl) {
        int lo = pr.second.front(), hi = pr.second.back(), a = 1;
        for (int d : pr.second) a = std::max(a, widest[d]);
        int p2 = 1;
        while (p2 < a) p2 <<= 1;
        cs.push_back({lo & ~(p2 - 1), hi, p2, pr.second});
    }
    std::sort(cs.begin(), cs.end(), [](const Cluster &a, const Cluster &b) {
        if (a.align != b.align) return a.align > b.align;
        return a.lo < b.lo;
    });
    int cur = 0;
    std::set<int> taken;
    for (const Cluster &c : cs) {
        int base = (cur + c.align - 1) & ~(c.align - 1);
        for (int d : c.members) {
            int nd = base + (d - c.lo);
            if (!taken.insert(nd).second)
                fail("lmem compaction: dword %d and another both map to %d",
                     d, nd);
            F.map[d] = nd;
        }
        cur = base + (c.hi - c.lo + 1);
    }
    F.size_dw = cur;
}

struct LmPatch { size_t slot; int off; int name; };

static void emit_lm_movs(Ctx &C, int i, u64 qr, std::vector<u64> &words,
                         std::vector<int> &owner, std::vector<LmPatch> &patch,
                         std::set<int> &names, int &elided) {
    const LmSlot &s = C.sp->lm[(size_t)i];
    int base = (int)(qr & 0xFF);
    u64 pn = (qr >> 16) & 7, pi = (qr >> 19) & 1;
    for (int k = 0; k < s.w; k++) {
        int dreg = (base == RZ) ? RZ : base + k;
        if (!s.store && dreg == RZ) continue;
        int name = C.regmap(LMBIT + s.off + k, s.store, i);

        if (g_lmem_copyprop && name < PREG && name == dreg) { elided++; continue; }
        u64 q = MOV_TMPL;
        size_t slot = words.size();
        int fld = s.store ? 0 : 20;
        int other = s.store ? 20 : 0;
        q = set_field8(q, other, dreg);
        if (name < PREG) {
            q = set_field8(q, fld, name);
        } else {
            q = set_field8(q, fld, RZ);
            patch.push_back({slot, fld, name});
            names.insert(name);
        }
        q = setbits(q, 16, 3, pn);
        q = setbits(q, 19, 1, pi);
        words.push_back(q);
        owner.push_back(-1);
    }
}

void emit(Program &uber, Spec &sp, const std::vector<u32> &c6,
          const std::string &name, EmitStats &out) {
    const OpSets &T = S();
    double t_emit0 = perf_now();

    const RunRes *Rp;
    { PerfScope ps_(&g_perf.t_run3); g_perf.n_run3++; Rp = &run3_cached(sp, c6); }
    const RunRes &R = *Rp;

    Alloc al;
    std::unordered_map<int, int> wr;
    std::set<int> removed;
    std::unordered_map<int, int> lmparent;
    {
        PerfScope ps_(&g_perf.t_alloc);
        g_perf.n_alloc++;
        static bool ac_valid = false;
        static long long ac_gen = -1;
        static bool ac_idfold = false;
        static Alloc ac_al;
        static std::unordered_map<int, int> ac_wr;
        static std::set<int> ac_removed;
        static std::unordered_map<int, int> ac_lmparent;
        if (ac_valid && ac_gen == g_r3_miss && ac_idfold == g_idfold) {
            al = ac_al;
            wr = ac_wr;
            removed = ac_removed;
            lmparent = ac_lmparent;
            g_perf.n_alloc_hit++;
        } else {
            allocate(sp, R, al);
            { PerfScope p2_(&g_perf.t_webreg); webreg(sp, al, wr); }

            { PerfScope p3_(&g_perf.t_postco);
              if (sp.folds || sp.texrw)
                  post_coalesce(sp, R, al, wr, removed, lmparent); }
            ac_al = al;
            ac_wr = wr;
            ac_removed = removed;
            ac_lmparent = lmparent;
            ac_gen = g_r3_miss;
            ac_idfold = g_idfold;
            ac_valid = true;
        }
    }

    int n_lm = 0;
    for (int i : R.kept)
        if (!removed.count(i) && T.local_ops[(size_t)uber.op[i]]) n_lm++;

    bool lm_usable = (n_lm > 0) && sp.lm_ok;
    bool do_promote = g_lmem_promote && lm_usable;
    bool do_compact = g_lmem_compact && lm_usable && !do_promote;

    {
        int kinds = g_copyprop ? 1 : 0;
        bool lmcp = do_promote && g_lmem_copyprop;
        if (lmcp) kinds |= 2;

        if (g_idfold) kinds |= 4;
        if (kinds) {
            PerfScope ps_(&g_perf.t_copyco);
            int rounds = (lmcp || g_idfold) ? 8 : 1;
            for (int r = 0; r < rounds; r++) {
                out.cp.lm_rounds = r + 1;
                if (copy_coalesce(sp, al, wr, removed, lmparent, out.cp,
                                  kinds) == 0) break;
            }
        }
    }

    Ctx C{&uber, &sp, &R, &al, &wr, &lmparent};

    std::vector<int> kept;
    for (int i : R.kept) if (!removed.count(i)) kept.push_back(i);
    if (kept.empty()) fail("nothing kept");

    for (int i : kept)
        if (uber.op[i] == T.O_Brx || uber.op[i] == T.O_Jmx)
            fail("BRX survived specialisation");

    {
        std::vector<int> em;
        sp.exit_mask.bits(em);
        if (!em.empty())
            for (int i : kept) {
                if (sp.cat[(size_t)i] != C_EXIT) continue;
                for (int r : em) {
                    if (r >= PREG) continue;
                    int got = C.regmap(r, true, i);
                    if (got != r)
                        fail("colour output R%d is carried by the web named "
                             "R%d at the EXIT in slot %d: that output would "
                             "never be written", r, got, i);
                }
            }
    }

    std::vector<u8> blob;
    std::map<std::pair<int, int>, std::pair<int, int>> optslots;
    OptMap optmap = [&](int b, int o) -> std::pair<int, int> {
        auto key = std::make_pair(b, o);
        auto it = optslots.find(key);
        if (it != optslots.end()) return it->second;
        u32 val;
        if (b == 1) {
            if (!uber.blob_u32(o, &val)) fail("blob read past the end at %#x", o);
        } else {
            size_t dw = (size_t)(o / 4);
            val = (dw < c6.size()) ? c6[dw] : 0u;
        }
        std::pair<int, int> slot(1, (int)blob.size());
        optslots[key] = slot;
        for (int k = 0; k < 4; k++) blob.push_back((u8)((val >> (8 * k)) & 0xFF));
        return slot;
    };

    LmFrame frame;
    if (do_compact) lm_build_frame(uber, sp, kept, frame);

    std::vector<u64> words;
    std::vector<int> owner;
    std::unordered_map<int, int> first;
    std::vector<LmPatch> lmpatch;
    std::set<int> lmnames;
    int n_remat = 0, n_lm_movs = 0, n_lm_promoted = 0, n_lm_compacted = 0;
    std::vector<u64> mv;
    for (int i : kept) {
        first[i] = (int)words.size();
        mv.clear();
        remat(C, i, mv);
        for (u64 w : mv) { words.push_back(w); owner.push_back(-1); n_remat++; }
        u64 q = rewrite(C, i, optmap);
        if (lm_usable && T.local_ops[(size_t)uber.op[i]]) {
            if (do_promote) {
                size_t before = words.size();
                emit_lm_movs(C, i, q, words, owner, lmpatch, lmnames,
                             out.cp.lm_elided);
                n_lm_movs += (int)(words.size() - before);
                n_lm_promoted++;
                continue;
            }
            if (do_compact) {
                int nd = frame.map.at(sp.lm[(size_t)i].off);
                q = setbits(q, 20, 24, (u64)(nd * 4) & 0xFFFFFF);
                n_lm_compacted++;
            }
        }
        words.push_back(q);
        owner.push_back(i);
    }

    if (!lmpatch.empty()) {
        std::set<int> used;
        words_used_regs(words, used);
        std::vector<int> ex;
        exit_live_regs(uber.bc, ex);
        used.insert(ex.begin(), ex.end());
        std::unordered_map<int, int> assign;
        int next = 0;
        for (int nm : lmnames) {
            while (next < RZ && used.count(next)) next++;
            if (next >= RZ)
                fail("local-memory promotion: no free register for slot %d",
                     nm - LMBIT);
            assign[nm] = next;
            used.insert(next);
            next++;
        }
        for (const LmPatch &pp : lmpatch)
            words[pp.slot] = set_field8(words[pp.slot], pp.off,
                                        assign.at(pp.name));
    }

    for (const LmPatch &pp : lmpatch) {
        u64 q = words[pp.slot];
        RSet d, md, u;
        Program::du_word(q, decode_op(q), decode_props(q), d, md, u);
        int rd = (int)(q & 0xFF), rs = (int)((q >> 20) & 0xFF);
        int pn = (int)((q >> 16) & 7);
        bool guarded = (pn != PT) || (((q >> 19) & 1) != 0);
        RSet wantd, wantm, wantu;
        if (pn != PT) wantu.add(PREG + pn);
        if (rs != RZ) wantu.add(rs);
        if (rd != RZ) {
            (guarded ? wantm : wantd).add(rd);
            if (guarded) wantu.add(rd);
        }
        if (!(d == wantd) || !(md == wantm) || !(u == wantu))
            fail("promoted Mov R%d, R%d decoded wrong", rd, rs);
    }

    int exit_slot;
    if (g_exitfold && !words.empty() && words.back() == W_EXIT) {
        exit_slot = (int)words.size() - 1;
        g_exitfold_hit++;
    } else {
        if (g_exitfold) g_exitfold_miss++;
        exit_slot = (int)words.size();
        words.push_back(W_EXIT); owner.push_back(-1);
    }
    words.push_back(W_BRA_SELF); owner.push_back(-1);
    while (words.size() % 3) { words.push_back(W_NOP); owner.push_back(-1); }

    for (size_t k = 0; k < owner.size(); k++) {
        int i = owner[k];
        if (i < 0) continue;
        int nm = uber.op[i];
        if (!T.branchy_imm[(size_t)nm]) continue;
        int t = uber.target(i);
        int nk;
        if (t < 0) fail("unresolved branch at %d", i);
        size_t idx = (size_t)(std::lower_bound(kept.begin(), kept.end(), t) -
                              kept.begin());
        nk = (idx < kept.size()) ? first[kept[idx]] : exit_slot;
        int disp = slot_rel(nk) - (slot_rel((int)k) + 8);
        if (!branch_disp_ok(disp))
            fail("branch displacement out of range");
        words[k] = setbits(words[k], 20, 24, (u64)(u32)disp & 0xFFFFFF);
    }

    check_cbuf(sp, words, blob.size());

    size_t used_blob = blob.size();
    while (blob.size() % CBUF_ALIGN) blob.push_back(0);

    size_t nb = (words.size() + 2) / 3;
    u32 co = (u32)(INSTR_START + nb * 32);
    co = (co + CBUF_ALIGN - 1) / CBUF_ALIGN * CBUF_ALIGN;
    std::vector<u8> bc((size_t)co + blob.size(), 0);
    std::memcpy(bc.data(), uber.bc.data(), INSTR_START);
    for (size_t k = 0; k < words.size(); k++) {
        size_t off = slot_off(k);
        std::memcpy(bc.data() + off, &words[k], 8);
    }
    std::memcpy(bc.data() + co, blob.data(), blob.size());

    std::vector<u8> ct = uber.ct;
    NVNshaderControl *c = ctl(ct);
    c->mProgramSize = (u32)(SPH_SIZE + nb * 32);
    c->mConstBufSize = (u32)used_blob;
    c->mConstBufOffset = co;
    c->mShaderSize = (u32)bc.size();

    phase_b(bc, co);

    int n_slots = 3 * ((int)co - INSTR_START) / 32;
    if (!slots_ok(n_slots))
        fail("padded instruction count %d is not 12 mod 24", n_slots);

    out.name = name;
    out.bc = std::move(bc);
    out.ct = std::move(ct);
    out.padded = n_slots;
    out.words = (int)words.size();
    out.n_kept = (int)R.kept.size();
    out.n_emit = (int)kept.size();
    out.n_coalesced = (int)removed.size();
    out.opt_relocated = (int)optslots.size();
    out.n_remat = n_remat;
    out.lm_ops = n_lm;
    out.lm_promoted = n_lm_promoted;
    out.lm_movs = n_lm_movs;
    out.lm_slots = (int)lmnames.size();
    out.lm_frame_dw = do_compact ? frame.size_dw : 0;
    out.lm_compacted = n_lm_compacted;
    out.p5_after = al.n_after;
    out.co = co;
    out.size = out.bc.size();
    g_perf.n_emitbody++;
    g_perf.t_emitbody += (perf_now() - t_emit0) - 0;
}

}
