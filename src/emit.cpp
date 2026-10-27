
#include "emit.h"

namespace ub { extern long long g_r3_miss; }

extern "C" {
int uber_phase_b(unsigned char *bc, unsigned int constOff);
}

namespace ub {

bool g_copyprop = false;

bool g_lmem_compact = true;
bool g_lmem_promote = true;

bool g_lmem_copyprop = true;

void phase_b(std::vector<u8> &bc, u32 co) {
    int n = uber_phase_b(bc.data(), co);
    if (n < 0) fail("phase B failed");
}

template <class I>
struct CtxT {
    ProgramT<I> *p;
    SpecT<I> *sp;
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

void Sm50::true_srcs(u64 q, int nm, unsigned pr, std::set<int> &out) {
    const OpSets &T = S();
    out.clear();
    if (T.tex_bases[(size_t)nm]) {
        RSet t; tex_uses(q, nm, t);
        std::vector<int> v; t.list(v);
        out.insert(v.begin(), v.end());
        return;
    }
    int offs[8];
    int m = gpr_src_offsets(q, nm, pr, offs);
    for (int k = 0; k < m; k++) out.insert((int)((q >> offs[k]) & 0xFF));
    if (T.store_ops[(size_t)nm] && T.no_dest[(size_t)nm])
        out.insert((int)(q & 0xFF));
}

template <class I>
static void check_operands(CtxT<I> &C, int i, typename I::Word q) {
    const ProgramT<I> &p = *C.p;
    SpecT<I> &sp = *C.sp;
    const RunRes &R = *C.R;
    int nm = p.op[i];

    int nm_e = I::decode_op(q);
    unsigned pr_e = I::decode_props(q);
    typename I::RSet d, md, u;
    I::du(q, nm_e, pr_e, d, md, u);
    int spur = I::spurious_pred(nm_e, q);

    int spur_w = I::spurious_pred(nm, p.q[i]);

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
    int cbreg = (cbslot >= 0) ? I::field_reg(p.q[i], cbslot) : -1;
    std::vector<int> uses;

    if (!R.fmac.empty() && R.fmac[(size_t)i] >= 0) sp.fmac_uses(R, i, uses);
    else p.uses[i].list(uses);
    for (int r : uses) {
        if (r >= LMBIT || r == spur_w || r == gp) continue;
        if (r == cbreg) {

            if (guard != TRI_T && p.maydefs[i].has(r))
                want.insert(C.regmap(r, true, i));
            continue;
        }
        if (r >= PREG) {

            if (guard == TRI_T && p.maydefs[i].has(r)) continue;
            if (guard != TRI_T && p.maydefs[i].has(r))
                want.insert(C.regmap(r, true, i));
            else if (!vmap_get(vals, r) || !I::lit_read(p, i, r))
                want.insert(C.regmap(r, false, i));
            continue;
        }
        if (guard == TRI_T) {
            const std::vector<int> &ms = sp.maydef_set[(size_t)i];
            if (std::binary_search(ms.begin(), ms.end(), r)) continue;
        } else if (p.maydefs[i].has(r)) {
            want.insert(C.regmap(r, true, i));
            if (!tsrc_done) { I::true_srcs(p.q[i], p.op[i], p.props[i], tsrc); tsrc_done = true; }
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
             "assumed [%s]", i, I::op_name(nm), gs.c_str(), ws.c_str());
    }

    if (R.fmac.empty() || R.fmac[(size_t)i] < 0) {
        int poffs[8];
        int pm = I::pred_fields(q, nm, p.props[i], poffs);
        for (int k = 0; k < pm; k++) {
            int off = poffs[k];
            int pn = I::pred_field(p.q[i], off);
            if (pn == PT || PREG + pn == gp || !I::pred_field_live(nm, off))
                continue;
            Tri val = sp.predval(vals, pn, I::pred_field_inv(p.q[i], off));
            if (val == TRI_U) continue;
            int en = I::pred_field(q, off), einv = I::pred_field_inv(q, off);
            if (en != PT || einv != (val == TRI_F ? 1 : 0))
                fail("predicate literal at %d (%s) bit %d reads %s%s, the "
                     "analysis has %s", i, I::op_name(nm), off, einv ? "!" : "",
                     en == PT ? "PT" : "a register", val ? "true" : "false");
        }
    }

    std::set<int> gotd, wantd;
    {
        typename I::RSet dm = d; dm.unite(md);
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
             "assumed [%s]", i, I::op_name(nm), gs.c_str(), ws.c_str());
    }
}

typedef std::function<std::pair<int, int>(int, int, int)> OptMap;

template <class I>
static typename I::Word rewrite(CtxT<I> &C, int i, OptMap &optmap) {
    typedef typename I::Word Word;
    const OpSets &T = I::sets();
    const ProgramT<I> &p = *C.p;
    SpecT<I> &sp = *C.sp;
    const RunRes &R = *C.R;
    Word q = p.q[i];
    int nm = p.op[i];
    unsigned props = p.props[i];

    if (!R.fmac.empty() && R.fmac[(size_t)i] >= 0) {
        q = sp.fmac_word(R, i, R.fmac[(size_t)i], R.fmac_slot[(size_t)i]);
        nm = I::decode_op(q);
        props = I::decode_props(q);
    }
    Tri guard = R.guard[(size_t)i];
    const VMap &v = R.vals[(size_t)i];
    const EMap &env = R.env[(size_t)i];
    bool rw = !sp.norw[(size_t)i];

    int gp = -1;
    if (!T.no_pred[(size_t)nm]) {
        int pn = I::guard_pred(q);
        if (guard == TRI_T) {
            if (pn != PT || I::guard_inv(q)) I::set_guard(q, PT, 0);
            if (pn != PT) gp = PREG + pn;
        } else if (guard == TRI_F) {
            fail("emitting a provably-dead instruction %d", i);
        } else {

            const u32 *gx = pn != PT ? vmap_get(v, PREG + pn) : nullptr;
            if (gx) {
                if ((*gx != 0) == (I::guard_inv(q) != 0))
                    fail("instruction %d is guarded by a predicate known false", i);
                I::set_guard(q, PT, 0);
                gp = PREG + pn;
            } else if (pn != PT) {
                int r = C.regmap(PREG + pn, false, i);
                if (r != PREG + pn) I::set_guard(q, r - PREG, I::guard_inv(q));
            }
        }
    }

    int cbslot = sp.cbfold_slot(i, env);
    if (!T.tex_bases[(size_t)nm]) {
        int offs[10];
        int m = I::src_fields(q, nm, props, offs);
        if (T.store_ops[(size_t)nm] && T.no_dest[(size_t)nm]) offs[m++] = I::dest_field();
        for (int k = 0; k < m; k++) {
            int o = offs[k];
            if (o == cbslot) continue;
            int r = I::field_reg(q, o);
            if (r == RZ) continue;
            const u32 *x = vmap_get(v, r);
            if (rw && x && *x == 0) { I::set_field(q, o, RZ); continue; }
            int32_t a = r;
            if (rw) {
                auto it = env.find(r);
                if (it != env.end()) a = it->second;
            }
            if (a < 0) a = r;
            if (a == RZ) { I::set_field(q, o, RZ); continue; }
            I::set_field(q, o, C.regmap(a, false, i));
        }
        int poffs[8];
        int pm = I::pred_fields(q, nm, props, poffs);
        for (int k = 0; k < pm; k++) {
            int off = poffs[k];
            int pn = I::pred_field(q, off);
            if (pn == PT) continue;
            int key = PREG + pn;

            if (key == gp || !I::pred_field_live(nm, off)) continue;
            const u32 *x = vmap_get(v, key);
            if (x) {
                if (!I::pred_literal_ok(nm))
                    fail("%s reads a known predicate at bit %d and is not on "
                         "the literal-rewrite list", I::op_name(nm), off);

                bool inv = I::pred_field_inv(q, off);
                bool val = (*x != 0) != inv;
                I::set_pred_field(q, off, PT, val ? 0 : 1);
            } else {
                I::set_pred_field(q, off, C.regmap(key, false, i) - PREG,
                                  I::pred_field_inv(q, off));
            }
        }
    } else if (rw) {

        int toffs[4];
        int tm = I::tex_src_fields(q, nm, toffs);
        for (int k = 0; k < tm; k++) {
            int o = toffs[k];
            int r = I::field_reg(q, o);
            if (r == RZ) continue;
            int32_t a = r;
            auto it = env.find(r);
            if (it != env.end()) a = it->second;
            if (a < 0 || a == RZ) a = r;
            I::set_field(q, o, C.regmap(a, false, i));
        }
    }

    if (!T.tex_bases[(size_t)nm] && rw) {
        typename I::RSet dset = p.defs[i];
        dset.unite(p.maydefs[i]);
        std::vector<int> all; dset.list(all);
        std::vector<int> dsts;
        for (int r : all) if (r < PREG) dsts.push_back(r);
        if (dsts.size() == 1) {
            int d = dsts[0];
            if (I::dest_reg(q) == d) I::set_field(q, I::dest_field(), C.regmap(d, true, i));
        } else if (dsts.size() > 1) {
            int base = I::dest_reg(q);
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
        int r0 = I::field_reg(p.q[i], cbslot);
        auto it = env.find(r0);
        if (it == env.end() || it->second >= 0)
            fail("cbfold: slot %d of instruction %d is not a cbuf marker",
                 cbslot, i);
        int32_t v = CBBASE - it->second;
        int b = (int)((u32)v >> 20), o = (int)(v & 0xFFFFF);
        if (b == sp.bank || b == 1) {
            std::pair<int, int> nn = optmap(b, o, 1);
            b = nn.first; o = nn.second;
        }
        I::fold_cbuf_operand(q, cbslot, b, o);
    }

    {
        int b, o;
        if (I::cbuf_operand(q, nm, &b, &o) && (b == sp.bank || b == 1)) {
            std::pair<int, int> nn = optmap(b, o, I::cbuf_dwords(q, nm));
            I::set_cbuf_operand(q, nn.first, nn.second);
        }
    }

    if (nm == T.O_Ldc) {
        int fbank = I::ldc_bank(q);
        if (fbank == sp.bank || fbank == 1) {
            int ra0, off0;
            u32 base = 0, k = 0;
            bool have = I::ldc_plain(p.q[i], nm, &ra0, &off0);
            if (have && ra0 != RZ) {
                const u32 *x = vmap_get(R.vals[(size_t)i], ra0);
                if (x) base = *x; else have = false;
            }
            if (have)
                have = p.blob_u32((int)((base + (u32)off0) & M32), &k);
            if (!have)
                fail("LDC from bank %d survived at %d and its value is not "
                     "proved -- the computed jump is live", fbank, i);
            check_operands(C, i, q);
            Word w = I::make_mov_imm(I::dest_reg(q), k);
            I::set_guard(w, I::guard_pred(q), I::guard_inv(q));
            return w;
        }
    }

    check_operands(C, i, q);
    return q;
}

template <class I>
static void remat(CtxT<I> &C, int i, std::vector<typename I::Word> &out) {
    const ProgramT<I> &p = *C.p;
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
        typename I::Word q = I::make_mov(d, s);
        typename I::RSet dd, mdd, uu;
        I::du(q, I::decode_op(q), I::decode_props(q), dd, mdd, uu);
        typename I::RSet want;
        want.add(d);
        typename I::RSet wantu;
        if (s != RZ) wantu.add(s);
        if (!(dd == want) || !(uu == wantu))
            fail("rematerialising MOV R%d, R%d decoded wrong", d, s);
        out.push_back(q);
    }
}

template <class I>
static void check_cbuf(SpecT<I> &sp, const std::vector<typename I::Word> &words,
                       size_t blobsz) {
    std::vector<std::string> bad;
    for (size_t k = 0; k < words.size(); k++) {
        const typename I::Word &q = words[k];
        if (I::empty(q)) continue;
        int nm = I::decode_op(q);
        int b, o;
        if (!I::cbuf_read(q, nm, &b, &o)) continue;
        char buf[256];
        if (b == sp.bank) {
            snprintf(buf, sizeof buf,
                     "slot %zu %s reads the option bank c[%#x][%#x]", k,
                     I::op_name(nm), b, o);
            bad.push_back(buf);
        } else if (b == 1 && (size_t)o + 4 * (size_t)I::cbuf_dwords(q, nm) > blobsz) {
            snprintf(buf, sizeof buf,
                     "slot %zu %s reads c[0x1][%#x], past the %zu-byte "
                     "relocated blob", k, I::op_name(nm), o, blobsz);
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
};

template <class I>
static void lm_build_frame(ProgramT<I> &uber, SpecT<I> &sp,
                           const std::vector<int> &kept, LmFrame &F) {
    const OpSets &T = I::sets();
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
}

struct LmPatch { size_t slot; int off; int name; };

template <class I>
static void emit_lm_movs(CtxT<I> &C, int i, typename I::Word qr,
                         std::vector<typename I::Word> &words,
                         std::vector<int> &owner, std::vector<LmPatch> &patch,
                         std::set<int> &names) {
    const LmSlot &s = C.sp->lm[(size_t)i];
    int base = I::dest_reg(qr);
    int pn = I::guard_pred(qr), pi = I::guard_inv(qr);
    for (int k = 0; k < s.w; k++) {
        int dreg = (base == RZ) ? RZ : base + k;
        if (!s.store && dreg == RZ) continue;
        int name = C.regmap(LMBIT + s.off + k, s.store, i);

        if (g_lmem_copyprop && name < PREG && name == dreg) continue;
        size_t slot = words.size();

        int fld = s.store ? I::mov_dst_field() : I::mov_src_field();
        int dw = name < PREG ? name : RZ;
        typename I::Word q = s.store ? I::make_mov(dw, dreg) : I::make_mov(dreg, dw);
        if (name >= PREG) {
            patch.push_back({slot, fld, name});
            names.insert(name);
        }
        I::set_guard(q, pn, pi);
        words.push_back(q);
        owner.push_back(-1);
    }
}

template <class I>
void emit(ProgramT<I> &uber, SpecT<I> &sp, const std::vector<u32> &c6,
          const std::string &name, EmitStats &out) {
    typedef typename I::Word Word;
    const OpSets &T = I::sets();

    const RunRes &R = run3_cached(sp, c6);

    Alloc al;
    std::unordered_map<int, int> wr;
    std::set<int> removed;
    std::unordered_map<int, int> lmparent;
    {
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
        } else {
            allocate(sp, R, al);
            webreg(sp, al, wr);

            if (sp.folds || sp.texrw)
                post_coalesce(sp, R, al, wr, removed, lmparent);
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
            int rounds = (lmcp || g_idfold) ? 8 : 1;
            for (int r = 0; r < rounds; r++) {
                if (copy_coalesce(sp, al, wr, removed, lmparent, kinds) == 0) break;
            }
        }
    }

    CtxT<I> C{&uber, &sp, &R, &al, &wr, &lmparent};

    std::vector<int> kept;
    for (int i : R.kept) if (!removed.count(i)) kept.push_back(i);
    if (kept.empty()) fail("nothing kept");

    std::unordered_map<int, int> brx_to;
    for (int i : kept) {
        if (sp.cat[(size_t)i] != C_BRX) continue;
        Word w = uber.q[i];
        if (R.guard[(size_t)i] != TRI_T || R.succ[(size_t)i].size() != 1 ||
            !I::make_bra(uber.q[i], w))
            fail("BRX survived specialisation");
        brx_to[i] = R.succ[(size_t)i][0];
    }

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

    std::map<std::pair<std::pair<int, int>, int>, std::pair<int, int>> optwide;
    OptMap optmap = [&](int b, int o, int nd) -> std::pair<int, int> {
        auto value = [&](int off) -> u32 {
            u32 val;
            if (b == 1) {
                if (!uber.blob_u32(off, &val)) fail("blob read past the end at %#x", off);
            } else {
                size_t dw = (size_t)(off / 4);
                val = (dw < c6.size()) ? c6[dw] : 0u;
            }
            return val;
        };
        if (nd > 1) {
            auto wkey = std::make_pair(std::make_pair(b, o), nd);
            auto wit = optwide.find(wkey);
            if (wit != optwide.end()) return wit->second;
            while (blob.size() % (size_t)(4 * nd)) blob.push_back(0);
            std::pair<int, int> slot(1, (int)blob.size());
            optwide[wkey] = slot;
            for (int d = 0; d < nd; d++) {
                u32 val = value(o + 4 * d);
                for (int k = 0; k < 4; k++) blob.push_back((u8)((val >> (8 * k)) & 0xFF));
            }
            return slot;
        }
        auto key = std::make_pair(b, o);
        auto it = optslots.find(key);
        if (it != optslots.end()) return it->second;
        u32 val = value(o);
        std::pair<int, int> slot(1, (int)blob.size());
        optslots[key] = slot;
        for (int k = 0; k < 4; k++) blob.push_back((u8)((val >> (8 * k)) & 0xFF));
        return slot;
    };

    LmFrame frame;
    if (do_compact) lm_build_frame(uber, sp, kept, frame);

    std::vector<Word> words;
    std::vector<int> owner;
    std::unordered_map<int, int> first;
    std::vector<LmPatch> lmpatch;
    std::set<int> lmnames;
    std::vector<Word> mv;
    for (int i : kept) {
        first[i] = (int)words.size();
        mv.clear();
        remat(C, i, mv);
        for (const Word &w : mv) { words.push_back(w); owner.push_back(-1); }
        if (brx_to.count(i)) {
            Word w = uber.q[i];
            I::make_bra(uber.q[i], w);
            I::set_guard(w, PT, 0);
            words.push_back(w);
            owner.push_back(i);
            continue;
        }
        Word q = rewrite(C, i, optmap);
        if (lm_usable && T.local_ops[(size_t)uber.op[i]]) {
            if (do_promote) {
                emit_lm_movs(C, i, q, words, owner, lmpatch, lmnames);
                continue;
            }
            if (do_compact) {
                int nd = frame.map.at(sp.lm[(size_t)i].off);
                I::set_lmem_off(q, nd * 4);
            }
        }
        words.push_back(q);
        owner.push_back(i);
    }

    if (!lmpatch.empty()) {
        std::set<int> used;
        words_used_regs<I>(words, used);
        std::vector<int> ex;
        I::exit_live_regs(uber.bc, ex);
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
            I::set_field(words[pp.slot], pp.off, assign.at(pp.name));
    }

    for (const LmPatch &pp : lmpatch) {
        const Word &q = words[pp.slot];
        typename I::RSet d, md, u;
        I::du(q, I::decode_op(q), I::decode_props(q), d, md, u);
        int rd = I::field_reg(q, I::mov_dst_field()), rs = I::field_reg(q, I::mov_src_field());
        int pn = I::guard_pred(q);
        bool guarded = (pn != PT) || (I::guard_inv(q) != 0);
        typename I::RSet wantd, wantm, wantu;
        if (pn != PT) wantu.add(PREG + pn);
        if (rs != RZ) wantu.add(rs);
        if (rd != RZ) {
            (guarded ? wantm : wantd).add(rd);
            if (guarded) wantu.add(rd);
        }
        if (!(d == wantd) || !(md == wantm) || !(u == wantu))
            fail("promoted Mov R%d, R%d decoded wrong", rd, rs);
    }

    int exit_slot = (int)words.size();
    words.push_back(I::exit_word()); owner.push_back(-1);
    words.push_back(I::bra_self_word()); owner.push_back(-1);
    I::pad(words, owner);

    for (size_t k = 0; k < owner.size(); k++) {
        int i = owner[k];
        if (i < 0) continue;
        int nm = uber.op[i];
        auto bx = brx_to.find(i);
        if (bx == brx_to.end() && !T.branchy_imm[(size_t)nm]) continue;
        int t = bx != brx_to.end() ? bx->second : uber.target(i);
        int nk;
        if (t < 0) fail("unresolved branch at %d", i);
        size_t idx = (size_t)(std::lower_bound(kept.begin(), kept.end(), t) -
                              kept.begin());
        nk = (idx < kept.size()) ? first[kept[idx]] : exit_slot;
        if (!I::set_branch(words[k], (int)k, nk))
            fail("branch displacement out of range");
    }
    I::fix_calls(words);

    check_cbuf(sp, words, blob.size());

    std::vector<u8> bc;
    std::vector<u8> ct = uber.ct;
    u32 co = I::emit_layout(uber.bc, words, blob, bc, ct);

    I::phase_b(bc, co);

    I::layout_check(co, nullptr);

    out.name = name;
    out.bc = std::move(bc);
    out.ct = std::move(ct);
    out.n_emit = (int)kept.size();
}
template void emit<Sm50>(ProgramT<Sm50> &, SpecT<Sm50> &, const std::vector<u32> &,
                         const std::string &, EmitStats &);
template void emit<Sm86>(ProgramT<Sm86> &, SpecT<Sm86> &, const std::vector<u32> &,
                         const std::string &, EmitStats &);

u32 Sm50::emit_layout(const std::vector<u8> &hdr, const std::vector<u64> &words,
                      std::vector<u8> &blob, std::vector<u8> &bc, std::vector<u8> &ct) {
    size_t used_blob = blob.size();
    while (blob.size() % CBUF_ALIGN) blob.push_back(0);

    size_t nb = (words.size() + 2) / 3;
    u32 co = (u32)(INSTR_START + nb * 32);
    co = (co + CBUF_ALIGN - 1) / CBUF_ALIGN * CBUF_ALIGN;
    bc.assign((size_t)co + blob.size(), 0);
    std::memcpy(bc.data(), hdr.data(), INSTR_START);
    for (size_t k = 0; k < words.size(); k++) {
        size_t off = slot_off(k);
        std::memcpy(bc.data() + off, &words[k], 8);
    }
    std::memcpy(bc.data() + co, blob.data(), blob.size());

    NVNshaderControl *c = ctl(ct);
    c->mProgramSize = (u32)(SPH_SIZE + nb * 32);
    c->mConstBufSize = (u32)used_blob;
    c->mConstBufOffset = co;
    c->mShaderSize = (u32)bc.size();
    return co;
}

}
