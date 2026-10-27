
#include <chrono>
#include <climits>
#include "emit.h"
#include "sm50/nv_sched_ctl.h"

extern "C" {
int uber_validate(unsigned char *bc, unsigned int constOff);
int ub_vote_latency(unsigned long long q);
extern int uber_vote_floor_fail;
}

namespace ub {

void tex_src_widths(u64 q, int nm, int &nA, int &nB) {
    static const int TEXS_SRC[14][2] = {
        {1,0},{1,1},{1,1},{2,1},{2,1},{2,2},{2,1},{2,1},{2,1},{2,2},{2,1},
        {2,1},{2,1},{2,2}};
    const OpSets &T = S();
    const char *s = op_name(nm);
    nA = 0;
    nB = 0;
    if (T.texs_fam[(size_t)nm]) {
        if (std::strncmp(s, "Tld4s", 5) == 0) { nA = 2; nB = 1; return; }
        int tg = (int)((q >> 53) & 0xF);
        if (std::strncmp(s, "Texs", 4) == 0) {
            int k = tg < 13 ? tg : 13;
            nA = TEXS_SRC[k][0];
            nB = TEXS_SRC[k][1];
            return;
        }
        switch (tg) {
        case 0x0: nA = 1; nB = 0; break;
        case 0x1: nA = 1; nB = 1; break;
        case 0x2: nA = 1; nB = 1; break;
        case 0x4: nA = 1; nB = 2; break;
        case 0x5: nA = 2; nB = 1; break;
        case 0x6: nA = 1; nB = 2; break;
        case 0x7: nA = 2; nB = 1; break;
        case 0x8: nA = 2; nB = 1; break;
        case 0xc: nA = 2; nB = 2; break;
        default:  nA = 2; nB = 2; break;
        }
        return;
    }
    if (!T.tex_fam[(size_t)nm]) return;
    if (!std::strcmp(s, "Txq") || !std::strcmp(s, "TxqB")) { nA = 1; return; }
    if (!std::strcmp(s, "Tmml") || !std::strcmp(s, "TmmlB")) { nA = 2; return; }
    bool is_b = !std::strcmp(s, "TexB") || !std::strcmp(s, "TldB") ||
                !std::strcmp(s, "Tld4B") || !std::strcmp(s, "TxdB");
    static const int dim_coords[8] = {1, 2, 2, 3, 3, 3, 3, 4};
    nA = dim_coords[(q >> 28) & 7];
    if ((q >> 50) & 1) nA++;
    int lod = (int)((is_b ? (q >> 37) : (q >> 55)) & 7);
    if (lod == 2 || lod == 3) nA++;
    nB = 1;
}

static void fieldmap(u64 q, int nm, unsigned pr, std::vector<Field> &out) {
    const OpSets &T = S();
    out.clear();
    if (q == 0 || nm == T.O_Nop) return;

    static const int TEXS_MASKLUT[2][8] = {
        {0x1, 0x2, 0x4, 0x8, 0x3, 0x9, 0xA, 0xC},
        {0x7, 0xB, 0xD, 0xE, 0xF, 0x0, 0x0, 0x0}};
    const char *s = op_name(nm);
    auto pc4 = [](int x) { int c = 0; while (x) { c += x & 1; x >>= 1; } return c; };

    if (T.texs_fam[(size_t)nm]) {
        int dest = (int)(q & 0xFF), dest2 = (int)((q >> 28) & 0xFF);
        bool t4s = std::strncmp(s, "Tld4s", 5) == 0;
        int wm = t4s ? 4 : (int)((q >> 50) & 7);
        int comp = pc4(TEXS_MASKLUT[dest2 == 255 ? 0 : 1][wm]);
        int w0 = std::min(comp, 2), w1 = std::max(0, comp - 2);
        if (dest != RZ && w0) out.push_back({0, dest, w0, 'd'});
        if (dest2 != RZ && w1) out.push_back({28, dest2, w1, 'd'});
        int srcA = (int)((q >> 8) & 0xFF), srcB = (int)((q >> 20) & 0xFF);
        int nA, nB;
        tex_src_widths(q, nm, nA, nB);
        if (srcA != RZ && nA) out.push_back({8, srcA, nA, 'u'});
        if (srcB != RZ && nB) out.push_back({20, srcB, nB, 'u'});
        return;
    }

    if (T.tex_fam[(size_t)nm]) {
        int dest = (int)(q & 0xFF), wm = (int)((q >> 31) & 0xF);
        int nd = pc4(wm);
        if (dest != RZ && nd) out.push_back({0, dest, nd, 'd'});
        int srcA = (int)((q >> 8) & 0xFF), nA, nB;
        tex_src_widths(q, nm, nA, nB);
        int srcB = nB ? (int)((q >> 20) & 0xFF) : RZ;
        if (srcA != RZ) out.push_back({8, srcA, nA, 'u'});
        if (srcB != RZ) out.push_back({20, srcB, nB, 'u'});
        return;
    }

    if (!T.safe_ops[(size_t)nm])
        fail("%s is not on the renumberable allowlist", s);
    if ((nm == T.O_F2f || nm == T.O_F2i || nm == T.O_I2f || nm == T.O_I2i) &&
        ((((q >> 8) & 3) == 3) || (((q >> 10) & 3) == 3)))
        fail("%s with a 64-bit operand is not modelled", s);
    if ((nm == T.O_Ald || nm == T.O_Ast || nm == T.O_Al2p) && ((q >> 47) & 3))
        fail("%s with size field %d is not modelled", s, (int)((q >> 47) & 3));
    if (nm == T.O_Shfl)
        fail("Shfl is not modelled (bit-39 operand is an immediate)");

    int offs[8];
    int m = gpr_src_offsets(q, nm, pr, offs);
    for (int k = 0; k < m; k++) {
        int r = (int)((q >> offs[k]) & 0xFF);
        if (r != RZ) out.push_back({offs[k], r, 1, 'u'});
    }
    bool no_dest = T.no_dest[(size_t)nm];
    if (!no_dest && (pr & P_RD)) {
        int rd = (int)(q & 0xFF);
        if (rd != RZ) out.push_back({0, rd, mem_data_regs(q, nm), 'd'});
    } else if (no_dest && T.store_ops[(size_t)nm]) {
        int rd = (int)(q & 0xFF);
        if (rd != RZ) out.push_back({0, rd, mem_data_regs(q, nm), 'u'});
        int ra = (int)((q >> 8) & 0xFF);
        bool have8 = false;
        for (const Field &f : out) if (f.off == 8) { have8 = true; break; }
        if (ra != RZ && !have8) out.push_back({8, ra, 1, 'u'});
    }
}

void Sm50::fieldmap(Word q, int nm, unsigned pr, std::vector<Field> &out) {
    ub::fieldmap(q, nm, pr, out);
}

u64 renumber_mask(u64 q) {
    std::vector<Field> fm;
    u64 m = 0;
    try {
        fieldmap(q, decode_op(q), decode_props(q), fm);
        for (const Field &f : fm) m |= ((u64)0xFF << f.off);
    } catch (const UbError &) { return 0; }
    return m;
}

static void fm_regs(const std::vector<Field> &fm, std::set<int> &s) {
    for (const Field &f : fm)
        for (int k = 0; k < f.w; k++)
            if (f.base + k < RZ) s.insert(f.base + k);
}

template <class I>
void words_used_regs(const std::vector<typename I::Word> &words, std::set<int> &out) {
    std::vector<Field> fm;
    for (const typename I::Word &q : words) {
        if (I::empty(q)) continue;
        I::fieldmap(q, I::decode_op(q), I::decode_props(q), fm);
        fm_regs(fm, out);
    }
}
template void words_used_regs<Sm50>(const std::vector<u64> &, std::set<int> &);
template void words_used_regs<Sm86>(const std::vector<sm86::Word> &, std::set<int> &);

template <class I>
static void check_fieldmap(const ProgramT<I> &p) {
    std::vector<Field> fm;
    for (int i = 0; i < p.n; i++) {
        if (I::empty(p.q[i])) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fm);
        std::set<int> got;
        fm_regs(fm, got);
        typename I::RSet u = p.defs[i];
        u.unite(p.maydefs[i]);
        u.unite(p.uses[i]);
        std::vector<int> lst; u.list(lst);
        std::set<int> want;
        for (int r : lst) if (r < RZ) want.insert(r);
        if (got != want)
            fail("field map disagrees with _du at instruction %d (%s)", i,
                 I::op_name(p.op[i]));
    }
}

struct Live {
    std::vector<Mask> live, dmask, umask;
};

template <class I>
static void liveness(const ProgramT<I> &p, const CFGraph &c,
                     const std::vector<char> &reach,
                     const std::vector<int> &exit_live, Live &L) {
    int n = p.n;
    Mask seed;
    for (int r : exit_live) seed.set(r);
    L.live.assign((size_t)n, Mask());
    L.dmask.assign((size_t)n, Mask());
    L.umask.assign((size_t)n, Mask());
    std::vector<int> order;
    for (int i = 0; i < n; i++) if (reach[(size_t)i]) order.push_back(i);
    for (int i : order) {
        std::vector<int> v;
        p.defs[i].list(v);
        for (int r : v) if (is_gpr_key(r)) L.dmask[(size_t)i].set(r);
        int spur = I::spurious_pred(p.op[i], p.q[i]);
        p.uses[i].list(v);
        for (int r : v) if (is_gpr_key(r) && r != spur) L.umask[(size_t)i].set(r);
    }
    std::vector<int> rorder(order.rbegin(), order.rend());
    bool conv = false;
    Mask lo, li;
    for (int round = 0; round < 4096; round++) {
        bool ch = false;
        for (int i : rorder) {
            lo.clear();
            if (c.succ[(size_t)i].empty()) lo = seed;
            else
                for (int t : c.succ[(size_t)i])
                    if (reach[(size_t)t]) lo |= L.live[(size_t)t];
            if (c.cat[(size_t)i] == C_EXIT) lo |= seed;
            li = lo;
            li.andnot_or(L.dmask[(size_t)i], L.umask[(size_t)i]);
            if (li != L.live[(size_t)i]) { L.live[(size_t)i] = li; ch = true; }
        }
        if (!ch) { conv = true; break; }
    }
    if (!conv) fail("liveness did not converge");
}

template <class I>
static void live_entry(const ProgramT<I> &p, const CFGraph &c,
                       const std::vector<char> &reach, Mask &ent) {
    int n = p.n;
    std::vector<Mask> live((size_t)n), dm((size_t)n), um((size_t)n);
    std::vector<int> order;
    for (int i = 0; i < n; i++) if (reach[(size_t)i]) order.push_back(i);
    std::vector<int> v;
    for (int i : order) {
        p.defs[i].list(v);
        for (int r : v) dm[(size_t)i].set(r);
        int spur = I::spurious_pred(p.op[i], p.q[i]);
        p.uses[i].list(v);
        for (int r : v) if (r != spur) um[(size_t)i].set(r);
    }
    std::vector<int> rorder(order.rbegin(), order.rend());
    Mask lo, li;
    for (int round = 0; round < 512; round++) {
        bool ch = false;
        for (int i : rorder) {
            lo.clear();
            for (int t : c.succ[(size_t)i]) if (reach[(size_t)t]) lo |= live[(size_t)t];
            li = lo;
            li.andnot_or(dm[(size_t)i], um[(size_t)i]);
            if (li != live[(size_t)i]) { live[(size_t)i] = li; ch = true; }
        }
        if (!ch) break;
    }
    ent = live.empty() ? Mask() : live[0];
}

typedef std::unordered_map<int, std::vector<int>> Adj;

template <class I>
static void interference(const ProgramT<I> &p, const std::vector<char> &reach,
                         Live &L, Adj &adj, bool defpairs = false) {
    const int NR = RZ, W = (RZ + 63) / 64;
    std::vector<u64> M((size_t)NR * W, 0);
    std::vector<char> present((size_t)NR, 0);

    std::vector<int> bs, lb, dd, md;
    Mask li, both;
    for (int i = 0; i < p.n; i++) {
        if (!reach[(size_t)i]) continue;
        const Mask &lo = L.live[(size_t)i];
        li = lo;
        li.andnot_or(L.dmask[(size_t)i], L.umask[(size_t)i]);
        for (int pass = 0; pass < 2; pass++) {
            const Mask &S = pass ? li : lo;
            S.bits(bs);

            if (bs.size() >= 2)
                for (int r : bs) {
                    u64 *row = &M[(size_t)r * W];
                    row[0] |= S.w[0]; row[1] |= S.w[1];
                    row[2] |= S.w[2]; row[3] |= S.w[3];
                    present[(size_t)r] = 1;
                }
        }
        L.dmask[(size_t)i].bits(dd);
        p.maydefs[i].list(md);
        both = lo;
        both |= li;
        int ndef = 0;
        for (int pass = 0; pass < 2; pass++) {
            const std::vector<int> &V = pass ? md : dd;
            for (int d : V) {
                if (pass && !is_gpr_key(d)) continue;
                present[(size_t)d] = 1;
                ndef++;
                u64 *row = &M[(size_t)d * W];
                row[0] |= both.w[0]; row[1] |= both.w[1];
                row[2] |= both.w[2]; row[3] |= both.w[3];
            }
        }

        if (ndef) {
            both.bits(lb);
            for (int r : lb) present[(size_t)r] = 1;
        }
        if (defpairs && ndef >= 2) {
            Mask dm = L.dmask[(size_t)i];
            for (int d : md) if (is_gpr_key(d)) dm.set(d);
            for (int pass = 0; pass < 2; pass++)
                for (int d : pass ? md : dd) {
                    if (pass && !is_gpr_key(d)) continue;
                    u64 *row = &M[(size_t)d * W];
                    row[0] |= dm.w[0]; row[1] |= dm.w[1];
                    row[2] |= dm.w[2]; row[3] |= dm.w[3];
                }
        }
    }

    for (int a = 0; a < NR; a++)
        M[(size_t)a * W + (a >> 6)] &= ~((u64)1 << (a & 63));

    {
        std::vector<u64> T((size_t)NR * W, 0);
        for (int a = 0; a < NR; a++)
            for (int w = 0; w < W; w++) {
                u64 x = M[(size_t)a * W + w];
                while (x) {
                    int b = w * 64 + __builtin_ctzll(x);
                    x &= x - 1;
                    T[(size_t)b * W + (a >> 6)] |= (u64)1 << (a & 63);
                }
            }
        for (size_t k = 0; k < M.size(); k++) M[k] |= T[k];
    }
    adj.clear();
    for (int a = 0; a < NR; a++) {
        if (!present[(size_t)a]) continue;
        std::vector<int> &row = adj[a];
        for (int w = 0; w < W; w++) {
            u64 x = M[(size_t)a * W + w];
            while (x) {
                int b = __builtin_ctzll(x);
                x &= x - 1;
                row.insert(row.end(), w * 64 + b);
            }
        }
    }
}

template <class I>
static void runs_of(const ProgramT<I> &p, const std::set<int> &used,
                    std::vector<std::vector<int>> &runs) {
    std::set<int> follows;
    std::vector<Field> fm;
    for (int i = 0; i < p.n; i++) {
        if (I::empty(p.q[i])) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fm);
        for (const Field &f : fm) {
            if (f.w <= 1) continue;
            if (f.base + f.w - 1 >= RZ)
                fail("group %d..%d runs into RZ", f.base, f.base + f.w - 1);
            for (int k = 1; k < f.w; k++) follows.insert(f.base + k);
        }
    }
    runs.clear();
    std::vector<int> cur;
    for (int r : used) {
        if (!cur.empty() && r == cur.back() + 1 && follows.count(r)) cur.push_back(r);
        else { if (!cur.empty()) runs.push_back(cur); cur.assign(1, r); }
    }
    if (!cur.empty()) runs.push_back(cur);
    std::unordered_map<int, int> pos;
    for (size_t ri = 0; ri < runs.size(); ri++)
        for (int r : runs[ri]) pos[r] = (int)ri;
    for (int r : follows) {
        auto it = pos.find(r);
        if (it == pos.end()) continue;
        auto jt = pos.find(r - 1);
        if (jt == pos.end() || jt->second != it->second)
            fail("R%d must follow R%d but they are in different runs", r, r - 1);
    }
}

typedef std::map<std::pair<int, int>, int> BConf;

extern "C" int ub_inst_class(const unsigned char *bc, unsigned int constOff,
                            int nreal, unsigned char *cls, unsigned short *rsb,
                            unsigned short *wsb, int *nslots);

int Sm50::inst_class(const std::vector<u8> &bc, u32 co, int nsl, u8 *cls) {
    std::vector<uint16_t> rsb((size_t)nsl + 8, 0), wsb((size_t)nsl + 8, 0);
    int got = 0;
    if (ub_inst_class(bc.data(), co, nsl, cls, rsb.data(), wsb.data(), &got) < 0)
        return -1;
    return got;
}

template <class I> struct SplitMapT;
typedef SplitMapT<Sm50> SplitMap;
template <class I>
static void bank_conflicts_nodes(const ProgramT<I> &p, const std::vector<char> &reach,
                                 const SplitMapT<I> &S, BConf &bc);

template <class I>
static void bank_conflicts(const ProgramT<I> &p, BConf &bc) {
    std::vector<Field> fm;
    for (int i = 0; i < p.n; i++) {
        if (I::empty(p.q[i])) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fm);
        std::set<int> srcs;
        for (const Field &f : fm) {
            if (f.kind != 'u') continue;
            for (int j = 0; j < f.w; j++) if (f.base + j < RZ) srcs.insert(f.base + j);
        }
        std::vector<int> v(srcs.begin(), srcs.end());
        for (size_t x = 0; x < v.size(); x++)
            for (size_t y = x + 1; y < v.size(); y++) bc[{v[x], v[y]}]++;
    }
}

struct NoFit {};

enum ColourOrder { ORD_DEG = 0, ORD_SMALLEST_LAST, ORD_DEG_ASC, ORD_NAME,
                   ORD_NAME_DESC, ORD_DEF, ORD_N };

typedef std::vector<std::pair<int, int>> Affinity;

typedef std::vector<std::pair<int, int>> RunAlign;

template <class I>
static void colour(const std::vector<std::vector<int>> &runs, Adj &adj,
                   const std::set<int> &pinned, const BConf *bconf, int limit,
                   std::unordered_map<int, int> &cmap, int corder = ORD_DEG,
                   const Affinity *aff = nullptr, const RunAlign *ral = nullptr,
                   const std::vector<int> *rpos = nullptr);

template <class I>
static void colour(const std::vector<std::vector<int>> &runs, Adj &adj,
                   const std::set<int> &pinned, const BConf *bconf, int limit,
                   std::unordered_map<int, int> &cmap, int corder,
                   const Affinity *aff, const RunAlign *ral,
                   const std::vector<int> *rpos) {
    const int align_mod = I::run_align();
    cmap.clear();

    int maxid_ = 0;
    for (const auto &rn_ : runs)
        for (int r : rn_) if (r > maxid_) maxid_ = r;
    std::vector<int> cidx((size_t)maxid_ + 1, -1);
    int NU = 0;
    for (const auto &rn_ : runs)
        for (int r : rn_) if (cidx[(size_t)r] < 0) cidx[(size_t)r] = NU++;
    const int W = (NU + 63) / 64;
    std::vector<u64> ADJ((size_t)NU * W, 0);
    for (const auto &rn_ : runs)
        for (int r : rn_) {
            auto ait = adj.find(r);
            if (ait == adj.end()) continue;
            u64 *row = &ADJ[(size_t)cidx[(size_t)r] * W];
            for (int o : ait->second)
                if (o >= 0 && o <= maxid_ && cidx[(size_t)o] >= 0)
                    row[cidx[(size_t)o] >> 6] |= (u64)1 << (cidx[(size_t)o] & 63);
        }
    const int NCOL = RZ + 8;
    std::vector<u64> TK((size_t)NCOL * W, 0);

    auto fits = [&](const std::vector<int> &run, int base) {
        for (size_t k = 0; k < run.size(); k++) {
            int c = base + (int)k;
            if (c >= NCOL) continue;
            const u64 *tk = &TK[(size_t)c * W];
            const u64 *row = &ADJ[(size_t)cidx[(size_t)run[k]] * W];
            for (int w = 0; w < W; w++) if (tk[w] & row[w]) return false;
        }
        return true;
    };

    std::unordered_map<int, std::vector<std::pair<int, int>>> bcadj;
    if (bconf)
        for (const auto &pr : *bconf) {
            bcadj[pr.first.first].push_back({pr.first.second, pr.second});
            bcadj[pr.first.second].push_back({pr.first.first, pr.second});
        }
    auto cost = [&](const std::vector<int> &run, int base) {
        long long n = 0;
        for (size_t k = 0; k < run.size(); k++) {
            int r = run[k], bank = I::reg_bank(base + (int)k);
            auto it = bcadj.find(r);
            if (it == bcadj.end()) continue;
            for (const auto &pc : it->second) {
                auto ct = cmap.find(pc.first);
                if (ct != cmap.end() && I::reg_bank(ct->second) == bank) n += pc.second;
            }
        }
        return n;
    };
    auto place = [&](const std::vector<int> &run, int base) {
        for (size_t k = 0; k < run.size(); k++) {
            cmap[run[k]] = base + (int)k;
            int c = base + (int)k;
            if (c >= NCOL) fail("colour %d out of the taken table", c);
            int x = cidx[(size_t)run[k]];
            TK[(size_t)c * W + (x >> 6)] |= (u64)1 << (x & 63);
        }
    };

    size_t nr = runs.size();
    std::vector<char> constrained(nr), pin(nr);
    std::vector<long long> deg(nr, 0);
    for (size_t i = 0; i < nr; i++) {
        constrained[i] = runs[i].size() > 1;
        bool pn = false;
        long long d = 0;
        for (int r : runs[i]) {
            if (pinned.count(r)) pn = true;
            auto it = adj.find(r);
            if (it != adj.end()) d += (long long)it->second.size();
        }
        pin[i] = pn;
        deg[i] = d;
    }

    std::vector<long long> rank(nr, 0);
    if (corder == ORD_SMALLEST_LAST) {

        std::vector<std::set<size_t>> rg(nr);
        std::unordered_map<int, size_t> owner;
        for (size_t i = 0; i < nr; i++) for (int r : runs[i]) owner[r] = i;
        for (size_t i = 0; i < nr; i++)
            for (int r : runs[i]) {
                auto it = adj.find(r);
                if (it == adj.end()) continue;
                for (int o : it->second) {
                    auto ot = owner.find(o);
                    if (ot != owner.end() && ot->second != i) rg[i].insert(ot->second);
                }
            }
        std::vector<char> gone(nr, 0);
        std::vector<long long> d(nr, 0);
        for (size_t i = 0; i < nr; i++) d[i] = (long long)rg[i].size();
        std::vector<size_t> stack;
        for (size_t step = 0; step < nr; step++) {
            size_t best = nr;
            for (size_t i = 0; i < nr; i++)
                if (!gone[i] && (best == nr || d[i] < d[best])) best = i;
            gone[best] = 1;
            stack.push_back(best);
            for (size_t o : rg[best]) if (!gone[o]) d[o]--;
        }

        for (size_t k = 0; k < stack.size(); k++)
            rank[stack[k]] = (long long)(stack.size() - k);
    }
    std::vector<size_t> order(nr);
    for (size_t i = 0; i < nr; i++) order[i] = i;
    std::stable_sort(order.begin(), order.end(), [&](size_t a, size_t b) {
        if ((int)!pin[a] != (int)!pin[b]) return (int)!pin[a] < (int)!pin[b];
        if (corder == ORD_DEF && rpos) {
            if ((*rpos)[a] != (*rpos)[b]) return (*rpos)[a] < (*rpos)[b];
            return runs[a][0] < runs[b][0];
        }
        if (runs[a].size() != runs[b].size()) return runs[a].size() > runs[b].size();
        switch (corder) {
        case ORD_SMALLEST_LAST:
            if (rank[a] != rank[b]) return rank[a] < rank[b];
            break;
        case ORD_DEG_ASC:
            if (deg[a] != deg[b]) return deg[a] < deg[b];
            break;
        case ORD_NAME:
            break;
        case ORD_NAME_DESC:
            return runs[a][0] > runs[b][0];
        default:
            if (deg[a] != deg[b]) return deg[a] > deg[b];
            break;
        }
        return runs[a][0] < runs[b][0];
    });

    std::unordered_map<int, std::vector<int>> affadj;
    if (aff)
        for (const auto &pr : *aff) {
            affadj[pr.first].push_back(pr.second);
            affadj[pr.second].push_back(pr.first);
        }

    for (size_t idx : order) {
        const std::vector<int> &run = runs[idx];
        if (pin[idx]) {
            for (int r : run)
                if (!pinned.count(r)) fail("run is only partly pinned");
            if (!fits(run, run[0])) fail("pinned run does not fit at its own base");
            place(run, run[0]);
            continue;
        }
        if (aff && run.size() == 1) {

            auto ait = affadj.find(run[0]);
            if (ait != affadj.end()) {
                std::map<int, int> want;
                for (int o : ait->second) {
                    auto ct = cmap.find(o);
                    if (ct != cmap.end()) want[ct->second]++;
                }
                std::vector<std::pair<int, int>> cs(want.begin(), want.end());
                std::stable_sort(cs.begin(), cs.end(),
                                 [](const std::pair<int, int> &a,
                                    const std::pair<int, int> &b) {
                                     return a.second > b.second;
                                 });
                int hi1 = (limit < 0 ? RZ : limit) - 1;
                bool placed = false;
                for (const auto &pr : cs) {
                    int c = pr.first;
                    if (c < 0 || c > hi1 || !fits(run, c)) continue;
                    place(run, c);
                    placed = true;
                    break;
                }
                if (placed) continue;
            }
        }
        int step = constrained[idx] ? align_mod : 1;
        int start = constrained[idx] ? (run[0] % align_mod) : 0;
        if (ral) {
            step = (*ral)[idx].first;
            start = (*ral)[idx].second;
        }
        int hi = (limit < 0 ? RZ : limit) - (int)run.size();
        std::vector<int> cands;
        for (int b = start; b <= hi; b += step) {
            if (fits(run, b)) {
                if (limit < 0) { cands.assign(1, b); break; }
                cands.push_back(b);
            }
        }
        if (cands.empty()) {
            if (limit >= 0) throw NoFit();
            fail("no colour for a run");
        }
        if (limit < 0 || !bconf || bconf->empty()) place(run, cands[0]);
        else {
            int best = cands[0];
            long long bestc = cost(run, cands[0]);
            for (size_t k = 1; k < cands.size(); k++) {
                long long c = cost(run, cands[k]);
                if (c < bestc || (c == bestc && cands[k] < best)) { bestc = c; best = cands[k]; }
            }
            place(run, best);
        }
    }
}

int occupancy_of(int regs) {
    if (regs <= 0) return 64;
    int per = ((regs * 32 + 255) / 256) * 256;
    int w = (65536 / per) / 4 * 4;
    return w > 64 ? 64 : w;
}

static const int SPLIT_NODE0 = 4096;

template <class I>
struct SplitMapT {
    std::vector<int> fnode;
    std::set<int> nodes;

    struct TRun { int base, span, step, start, name; };
    std::vector<TRun> truns;
    enum { FSTRIDE = FIELD_SLOTS };
    static int offix(int off) { return I::field_index(off); }
    void slots(int n) { fnode.assign((size_t)n * FSTRIDE, -1); }
    void set(int i, int off, int v) {
        int x = offix(off);
        if (x < 0) fail("split: field offset %d is not a register slot", off);
        fnode[(size_t)i * FSTRIDE + (size_t)x] = v;
    }
    int at(int i, int off) const {
        int x = offix(off);
        if (x < 0) return -1;
        size_t k = (size_t)i * FSTRIDE + (size_t)x;
        return k < fnode.size() ? fnode[k] : -1;
    }
};

static bool dominators(const CFGraph &c, const std::vector<char> &reach,
                       int nreal, int &W, std::vector<u64> &dom) {
    W = (nreal + 63) / 64;
    dom.assign((size_t)nreal * W, 0);
    for (int i = 0; i < nreal; i++) {
        if (!reach[(size_t)i]) continue;
        if (i == 0) { dom[0] |= 1; continue; }
        for (int w = 0; w < W; w++) dom[(size_t)i * W + w] = ~(u64)0;
    }
    std::vector<u64> tmp((size_t)W);
    for (int round = 0; round < 64; round++) {
        bool ch = false;
        for (int i = 1; i < nreal; i++) {
            if (!reach[(size_t)i]) continue;
            for (int w = 0; w < W; w++) tmp[(size_t)w] = ~(u64)0;
            bool any = false;
            for (int pr : c.pred[(size_t)i]) {
                if (pr < 0 || pr >= nreal || !reach[(size_t)pr]) continue;
                any = true;
                for (int w = 0; w < W; w++) tmp[(size_t)w] &= dom[(size_t)pr * W + w];
            }
            if (!any) for (int w = 0; w < W; w++) tmp[(size_t)w] = 0;
            tmp[(size_t)(i >> 6)] |= (u64)1 << (i & 63);
            for (int w = 0; w < W; w++)
                if (dom[(size_t)i * W + w] != tmp[(size_t)w]) {
                    dom[(size_t)i * W + w] = tmp[(size_t)w];
                    ch = true;
                }
        }
        if (!ch) return true;
    }
    return false;
}

static void cycle_nodes(const CFGraph &c, const std::vector<char> &reach,
                        int nreal, std::vector<char> &in_cycle) {
    in_cycle.assign((size_t)nreal, 0);
    std::vector<int> index((size_t)nreal, -1), low((size_t)nreal, 0);
    std::vector<char> onstk((size_t)nreal, 0);
    std::vector<int> stk;
    int idx = 0;

    struct Frame { int v; size_t k; };
    for (int s = 0; s < nreal; s++) {
        if (!reach[(size_t)s] || index[(size_t)s] >= 0) continue;
        std::vector<Frame> call;
        call.push_back({s, 0});
        index[(size_t)s] = low[(size_t)s] = idx++;
        stk.push_back(s); onstk[(size_t)s] = 1;
        while (!call.empty()) {
            Frame &f = call.back();
            int v = f.v;
            const std::vector<int> &sv = c.succ[(size_t)v];
            if (f.k < sv.size()) {
                int w = sv[f.k++];
                if (w < 0 || w >= nreal || !reach[(size_t)w]) continue;
                if (index[(size_t)w] < 0) {
                    index[(size_t)w] = low[(size_t)w] = idx++;
                    stk.push_back(w); onstk[(size_t)w] = 1;
                    call.push_back({w, 0});
                } else if (onstk[(size_t)w]) {
                    if (index[(size_t)w] < low[(size_t)v]) low[(size_t)v] = index[(size_t)w];
                }
                continue;
            }
            if (low[(size_t)v] == index[(size_t)v]) {
                std::vector<int> comp;
                for (;;) {
                    int w = stk.back(); stk.pop_back(); onstk[(size_t)w] = 0;
                    comp.push_back(w);
                    if (w == v) break;
                }
                bool cyc = comp.size() > 1;
                if (!cyc)
                    for (int t : c.succ[(size_t)v]) if (t == v) cyc = true;
                if (cyc) for (int w : comp) in_cycle[(size_t)w] = 1;
            }
            call.pop_back();
            if (!call.empty()) {
                int u = call.back().v;
                if (low[(size_t)v] < low[(size_t)u]) low[(size_t)u] = low[(size_t)v];
            }
        }
    }
}

template <class I>
static bool build_split(const ProgramT<I> &p, const CFGraph &c,
                        const std::vector<char> &reach, const Live &L,
                        const std::vector<int> &exit_live, SplitMapT<I> &S,
                        Adj &nadj, bool want_adj = true,
                        std::vector<std::vector<int>> *innode_out = nullptr,
                        bool split_all = false,
                        std::vector<std::vector<int>> *outnode_out = nullptr,
                        int tmode = 0, const std::vector<char> *nosplit = nullptr,
                        std::vector<int> *tconf = nullptr) {
    const OpSets &T = I::sets();
    int n = p.n;
    std::vector<Field> fm;

    const bool tsplit = (tmode & RN_SPLIT) != 0;
    std::vector<std::pair<int, int>> tfields;

    std::vector<char> wide((size_t)RZ, 0), usedf((size_t)RZ, 0);
    for (int i = 0; i < n; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fm);
        for (const Field &f : fm) {
            for (int k = 0; k < f.w; k++) {
                int r = f.base + k;
                if (r >= RZ) continue;
                usedf[(size_t)r] = 1;
                if (f.w > 1) wide[(size_t)r] = 1;
            }
            if (tsplit && f.w > 1 && f.base < RZ) tfields.push_back({f.base, f.w});
        }
    }
    std::vector<char> pinset((size_t)RZ, 0);
    for (int r : exit_live) if (r >= 0 && r < RZ) pinset[(size_t)r] = 1;
    if (nosplit)
        for (int r = 0; r < RZ && r < (int)nosplit->size(); r++)
            if ((*nosplit)[(size_t)r]) pinset[(size_t)r] = 1;
    if (tsplit) {

        for (bool ch = true; ch;) {
            ch = false;
            for (const auto &tf : tfields) {
                bool any = false, all = true;
                for (int k = 0; k < tf.second; k++) {
                    bool pz = tf.first + k >= RZ || pinset[(size_t)(tf.first + k)];
                    any |= pz;
                    all &= pz;
                }
                if (!any || all) continue;
                for (int k = 0; k < tf.second && tf.first + k < RZ; k++)
                    pinset[(size_t)(tf.first + k)] = 1;
                ch = true;
            }
        }
    }

    std::vector<char> splitok((size_t)RZ, 0);
    std::vector<int> used;
    used.reserve((size_t)RZ);
    for (int r = 0; r < RZ; r++) {
        if (!usedf[(size_t)r]) continue;
        used.push_back(r);
        if (split_all || ((tsplit || !wide[(size_t)r]) && !pinset[(size_t)r]))
            splitok[(size_t)r] = 1;
    }
    auto splittable = [&](int r) { return r >= 0 && r < RZ && splitok[(size_t)r]; };

    const std::vector<Mask> &lin = L.live;
    std::vector<Mask> lout((size_t)n);
    Mask seed;
    for (int r : exit_live) seed.set(r);
    for (int i = 0; i < n; i++) {
        if (!reach[(size_t)i]) continue;
        if (c.succ[(size_t)i].empty()) lout[(size_t)i] = seed;
        else
            for (int t : c.succ[(size_t)i])
                if (reach[(size_t)t]) lout[(size_t)i] |= lin[(size_t)t];

        if (p.op[i] == T.O_Exit || p.op[i] == T.O_Ret) lout[(size_t)i] |= seed;
    }

    static std::vector<std::vector<int>> s_innode, s_outnode;
    std::vector<std::vector<int>> &innode = innode_out ? *innode_out : s_innode;
    std::vector<std::vector<int>> &outnode = outnode_out ? *outnode_out : s_outnode;
    if ((int)innode.size() < RZ) innode.resize((size_t)RZ);
    if ((int)outnode.size() < RZ) outnode.resize((size_t)RZ);
    for (auto &v : innode) v.clear();
    for (auto &v : outnode) v.clear();
    static std::vector<int> uf;
    if (uf.size() < 2 * (size_t)n) uf.resize(2 * (size_t)n);

    auto find = [](int x) {
        while (uf[(size_t)x] != x) {
            uf[(size_t)x] = uf[(size_t)uf[(size_t)x]];
            x = uf[(size_t)x];
        }
        return x;
    };

    static std::vector<std::vector<int>> lipt, lopt, dfpt;
    if ((int)lipt.size() < RZ) {
        lipt.resize((size_t)RZ); lopt.resize((size_t)RZ); dfpt.resize((size_t)RZ);
    }
    for (auto &v : lipt) v.clear();
    for (auto &v : lopt) v.clear();
    for (auto &v : dfpt) v.clear();

    static std::vector<int> soff, sarr;
    {
        soff.assign((size_t)n + 1, 0);
        sarr.clear();

        const int RW = (RZ + 63) / 64;
        for (int i = 0; i < n; i++) {
            soff[(size_t)i] = (int)sarr.size();
            if (!reach[(size_t)i]) continue;
            for (int t : c.succ[(size_t)i]) if (reach[(size_t)t]) sarr.push_back(t);
            const u64 *wi = lin[(size_t)i].w, *wo = lout[(size_t)i].w;
            const u64 *wd = L.dmask[(size_t)i].w;
            for (int k = 0; k < RW; k++) {
                u64 x = wi[k];
                while (x) {
                    int r = k * 64 + (int)__builtin_ctzll(x);
                    x &= x - 1;
                    if (r < RZ && splitok[(size_t)r]) lipt[(size_t)r].push_back(i);
                }
                u64 y = wo[k];
                while (y) {
                    int r = k * 64 + (int)__builtin_ctzll(y);
                    y &= y - 1;
                    if (r < RZ && splitok[(size_t)r]) lopt[(size_t)r].push_back(i);
                }
                u64 z = wd[k];
                while (z) {
                    int r = k * 64 + (int)__builtin_ctzll(z);
                    z &= z - 1;
                    if (r < RZ && splitok[(size_t)r]) dfpt[(size_t)r].push_back(i);
                }
            }
        }
        soff[(size_t)n] = (int)sarr.size();
    }

    static std::vector<int> instamp, outstamp, defstamp;
    static int pstamp = 0;
    if ((int)instamp.size() < n) {
        instamp.assign((size_t)n, -1);
        outstamp.assign((size_t)n, -1);
        defstamp.assign((size_t)n, -1);
        pstamp = 0;
    }

    static std::vector<int> repnode, repstamp;
    static int stamp = 0;
    if (repnode.size() < 2 * (size_t)n) {
        repnode.assign(2 * (size_t)n, 0);
        repstamp.assign(2 * (size_t)n, -1);
        stamp = 0;
    }
    int next = SPLIT_NODE0;
    int nsplit = 0;

    static std::vector<int> nname;
    nname.clear();
    for (int r : used) {
        if (!splittable(r)) continue;
        const std::vector<int> &LIp = lipt[(size_t)r], &LOp = lopt[(size_t)r];
        pstamp++;
        for (int i : LIp) { uf[(size_t)(2 * i)] = 2 * i; instamp[(size_t)i] = pstamp; }
        for (int i : LOp) { uf[(size_t)(2 * i + 1)] = 2 * i + 1; outstamp[(size_t)i] = pstamp; }
        for (int i : dfpt[(size_t)r]) defstamp[(size_t)i] = pstamp;
        for (int i : LIp) {
            if (outstamp[(size_t)i] != pstamp) continue;
            if (defstamp[(size_t)i] == pstamp && !p.maydefs[i].has(r)) continue;
            int a = find(2 * i), b = find(2 * i + 1);
            if (a != b) uf[(size_t)b] = a;
        }
        for (int i : LOp) {
            const int e0 = soff[(size_t)i], e1 = soff[(size_t)i + 1];
            for (int e = e0; e < e1; e++) {
                int t = sarr[(size_t)e];
                if (instamp[(size_t)t] != pstamp) continue;
                int a = find(2 * i + 1), b = find(2 * t);
                if (a != b) uf[(size_t)b] = a;
            }
        }
        int nnode = 0;
        stamp++;
        std::vector<int> &vi = innode[r], &vo = outnode[r];
        vi.assign((size_t)n, -1);
        vo.assign((size_t)n, -1);

        size_t ai = 0, ao = 0;
        while (ai < LIp.size() || ao < LOp.size()) {
            int i = ai < LIp.size()
                        ? (ao < LOp.size() ? std::min(LIp[ai], LOp[ao]) : LIp[ai])
                        : LOp[ao];
            if (ai < LIp.size() && LIp[ai] == i) {
                int rp = find(2 * i);
                if (repstamp[(size_t)rp] != stamp) {
                    repstamp[(size_t)rp] = stamp;
                    repnode[(size_t)rp] = next++;
                    if (tsplit) nname.push_back(r);
                    nnode++;
                }
                vi[(size_t)i] = repnode[(size_t)rp];
                ai++;
            }
            if (ao < LOp.size() && LOp[ao] == i) {
                int rp = find(2 * i + 1);
                if (repstamp[(size_t)rp] != stamp) {
                    repstamp[(size_t)rp] = stamp;
                    repnode[(size_t)rp] = next++;
                    if (tsplit) nname.push_back(r);
                    nnode++;
                }
                vo[(size_t)i] = repnode[(size_t)rp];
                ao++;
            }
        }
        if (nnode > 1) nsplit++;
    }
    if (!nsplit) return false;

    std::unordered_map<long long, int> deadnode;
    auto defnode = [&](int i, int r) {
        if (!splittable(r)) return r;
        int v = outnode[r][(size_t)i];
        if (v >= 0) return v;
        v = lin[(size_t)i].test(r) ? innode[r][(size_t)i] : -1;
        if (v >= 0) return v;
        long long k = (long long)i * WEB_STRIDE + r;
        auto it = deadnode.find(k);
        if (it != deadnode.end()) return it->second;
        int id = next++;
        if (tsplit) nname.push_back(r);
        deadnode[k] = id;
        return id;
    };
    auto usenode = [&](int i, int r) {
        if (!splittable(r)) return r;
        int v = innode[r][(size_t)i];
        if (v < 0) fail("split: use of R%d at %d is not live-in", r, i);
        return v;
    };

    S.slots(n);
    std::vector<int> ndlist;

    std::vector<std::pair<int, int>> tfirst, tjoin;
    for (int i = 0; i < n; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fm);
        for (const Field &f : fm) {
            int nd = (f.kind == 'd') ? defnode(i, f.base) : usenode(i, f.base);
            S.set(i, f.off, nd);
            if (tsplit && f.w > 1 && splittable(f.base)) {

                tfirst.push_back({nd, f.w});
                for (int k = 0; k < f.w; k++) {
                    int r = f.base + k;
                    int nk = (f.kind == 'd') ? defnode(i, r) : usenode(i, r);
                    if (nk < SPLIT_NODE0) fail("split: tuple R%d..R%d is split in part", f.base,
                                               f.base + f.w - 1);
                    ndlist.push_back(nk);
                    if (k) tjoin.push_back({nd, nk});
                }
                continue;
            }

            for (int k = 0; k < f.w; k++) ndlist.push_back(nd + k);
        }
    }

    std::sort(ndlist.begin(), ndlist.end());
    ndlist.erase(std::unique(ndlist.begin(), ndlist.end()), ndlist.end());
    S.nodes.insert(ndlist.begin(), ndlist.end());
    if (!want_adj) return true;

    nadj.clear();
    {
        std::vector<int> dd0, md0;
        for (int i = 0; i < n; i++) {
            if (!reach[(size_t)i]) continue;
            L.dmask[(size_t)i].bits(dd0);
            p.maydefs[i].list(md0);
            for (int pass = 0; pass < 2; pass++) {
                const std::vector<int> &V = pass ? md0 : dd0;
                for (int d : V) { if (d >= RZ) continue; (void)defnode(i, d); }
            }
        }
    }
    const int NN = RZ + (next - SPLIT_NODE0);
    const int NW = (NN + 63) / 64;
    auto nidx = [&](int id) { return id < RZ ? id : RZ + (id - SPLIT_NODE0); };
    std::vector<u64> NM((size_t)NN * NW, 0);
    std::vector<char> npres((size_t)NN, 0);

    auto link = [&](int a, int b) {
        if (a == b) return;
        int x = nidx(a), y = nidx(b);
        NM[(size_t)x * NW + (y >> 6)] |= (u64)1 << (y & 63);
        NM[(size_t)y * NW + (x >> 6)] |= (u64)1 << (x & 63);
        npres[(size_t)x] = 1;
        npres[(size_t)y] = 1;
    };

    std::vector<u64> LOm((size_t)NW, 0), LIm((size_t)NW, 0);
    std::vector<int> LOx, LIx;
    std::vector<int> bs, dd, md, LO, LI;
    std::vector<int> dns;
    for (int i = 0; i < n; i++) {
        if (!reach[(size_t)i]) continue;
        LO.clear(); LI.clear();
        lout[(size_t)i].bits(bs);
        for (int r : bs) if (r < RZ) LO.push_back(splittable(r) ? outnode[r][(size_t)i] : r);
        lin[(size_t)i].bits(bs);
        for (int r : bs) if (r < RZ) LI.push_back(splittable(r) ? innode[r][(size_t)i] : r);
        LOx.clear(); LIx.clear();
        for (int id : LO) LOx.push_back(nidx(id));
        for (int id : LI) LIx.push_back(nidx(id));
        for (int x : LOx) LOm[(size_t)(x >> 6)] |= (u64)1 << (x & 63);
        for (int x : LIx) LIm[(size_t)(x >> 6)] |= (u64)1 << (x & 63);
        if (LOx.size() >= 2)
            for (int x : LOx) {
                u64 *row = &NM[(size_t)x * NW];
                for (int w = 0; w < NW; w++) row[w] |= LOm[(size_t)w];
                npres[(size_t)x] = 1;
            }
        if (LIx.size() >= 2)
            for (int x : LIx) {
                u64 *row = &NM[(size_t)x * NW];
                for (int w = 0; w < NW; w++) row[w] |= LIm[(size_t)w];
                npres[(size_t)x] = 1;
            }
        L.dmask[(size_t)i].bits(dd);
        p.maydefs[i].list(md);

        bool wideop = I::wide_dest(p.q[i], p.op[i]);

        if (wideop && (tmode & RN_OVERLAP) && I::dest_overlap_ok(p.q[i], p.op[i]))
            wideop = false;
        dns.clear();
        bool any_def = false, any_li_def = false;
        for (int pass = 0; pass < 2; pass++) {
            const std::vector<int> &V = pass ? md : dd;
            for (int d : V) {
                if (d >= RZ) continue;
                int dn = defnode(i, d);
                int dx = nidx(dn);
                npres[(size_t)dx] = 1;
                dns.push_back(dn);
                any_def = true;
                u64 *row = &NM[(size_t)dx * NW];
                for (int w = 0; w < NW; w++) row[w] |= LOm[(size_t)w];

                bool may = (pass == 1) || p.maydefs[i].has(d);
                if (wideop || may) {
                    for (int w = 0; w < NW; w++) row[w] |= LIm[(size_t)w];
                    any_li_def = true;
                }
            }
        }

        if (any_def) for (int x : LOx) npres[(size_t)x] = 1;
        if (any_li_def) for (int x : LIx) npres[(size_t)x] = 1;
        for (size_t x = 0; x < dns.size(); x++)
            for (size_t y = x + 1; y < dns.size(); y++) link(dns[x], dns[y]);
        for (int x : LOx) LOm[(size_t)(x >> 6)] = 0;
        for (int x : LIx) LIm[(size_t)(x >> 6)] = 0;
    }
    for (int a = 0; a < NN; a++)
        NM[(size_t)a * NW + (a >> 6)] &= ~((u64)1 << (a & 63));
    {
        std::vector<u64> Tm((size_t)NN * NW, 0);
        for (int a = 0; a < NN; a++)
            for (int w = 0; w < NW; w++) {
                u64 x = NM[(size_t)a * NW + w];
                while (x) {
                    int b = w * 64 + __builtin_ctzll(x);
                    x &= x - 1;
                    Tm[(size_t)b * NW + (a >> 6)] |= (u64)1 << (a & 63);
                }
            }
        for (size_t k = 0; k < NM.size(); k++) NM[k] |= Tm[k];
    }
    for (int a = 0; a < NN; a++) {
        if (!npres[(size_t)a]) continue;
        std::vector<int> &row = nadj[a < RZ ? a : SPLIT_NODE0 + (a - RZ)];
        for (int w = 0; w < NW; w++) {
            u64 x = NM[(size_t)a * NW + w];
            while (x) {
                int b = __builtin_ctzll(x);
                x &= x - 1;
                int id = w * 64 + b;
                row.insert(row.end(), id < RZ ? id : SPLIT_NODE0 + (id - RZ));
            }
        }
    }
    if (!tsplit || tfirst.empty()) return true;

    const int NS = next - SPLIT_NODE0;
    if ((int)nname.size() != NS) fail("split: %d split nodes, %zu names", NS, nname.size());
    std::vector<int> tu((size_t)NS);
    for (int x = 0; x < NS; x++) tu[(size_t)x] = x;
    auto tfind = [&tu](int x) {
        while (tu[(size_t)x] != x) {
            tu[(size_t)x] = tu[(size_t)tu[(size_t)x]];
            x = tu[(size_t)x];
        }
        return x;
    };
    std::vector<char> intup((size_t)NS, 0);
    for (const auto &pr : tfirst) intup[(size_t)(pr.first - SPLIT_NODE0)] = 1;
    for (const auto &pr : tjoin) {
        int a = tfind(pr.first - SPLIT_NODE0), b = pr.second - SPLIT_NODE0;
        intup[(size_t)b] = 1;
        b = tfind(b);
        if (a != b) tu[(size_t)b] = a;
    }
    std::vector<int> lo((size_t)NS, RZ), hi((size_t)NS, -1), al((size_t)NS, 1);
    for (int x = 0; x < NS; x++) {
        if (!intup[(size_t)x]) continue;
        int r = tfind(x), nm = nname[(size_t)x];
        lo[(size_t)r] = std::min(lo[(size_t)r], nm);
        hi[(size_t)r] = std::max(hi[(size_t)r], nm);
    }
    for (const auto &pr : tfirst) {
        int x = pr.first - SPLIT_NODE0, a = I::tuple_align(pr.second);
        if (nname[(size_t)x] % a)
            fail("split: tuple at R%d is not aligned for %d registers", nname[(size_t)x],
                 pr.second);
        int r = tfind(x);
        al[(size_t)r] = std::max(al[(size_t)r], a);
    }
    std::vector<int> remap((size_t)NS, -1), cbase((size_t)NS, -1);
    int nx = next;
    S.truns.clear();
    for (int x = 0; x < NS; x++) {
        if (!intup[(size_t)x]) continue;
        int r = tfind(x);
        if (cbase[(size_t)r] < 0) {
            cbase[(size_t)r] = nx;
            int span = hi[(size_t)r] - lo[(size_t)r] + 1;
            nx += span;
            S.truns.push_back({cbase[(size_t)r], span, al[(size_t)r], lo[(size_t)r] % al[(size_t)r],
                               lo[(size_t)r]});
        }
        remap[(size_t)x] = cbase[(size_t)r] + nname[(size_t)x] - lo[(size_t)r];
    }

    std::unordered_map<int, std::vector<int>> same;
    for (int x = 0; x < NS; x++)
        if (intup[(size_t)x]) same[remap[(size_t)x]].push_back(x);
    std::set<int> bad;
    for (const auto &kv : same) {
        const std::vector<int> &v = kv.second;
        for (size_t a = 0; a < v.size(); a++)
            for (size_t b = a + 1; b < v.size(); b++) {
                int xa = RZ + v[a], xb = RZ + v[b];
                if (NM[(size_t)xa * NW + (xb >> 6)] & ((u64)1 << (xb & 63)))
                    bad.insert(tfind(v[a]));
            }
    }
    if (!bad.empty()) {
        if (tconf)
            for (int r : bad)
                for (int nm = lo[(size_t)r]; nm <= hi[(size_t)r]; nm++) tconf->push_back(nm);
        S.truns.clear();
        return false;
    }
    auto rm = [&](int id) {
        if (id < SPLIT_NODE0 || id >= next) return id;
        int v = remap[(size_t)(id - SPLIT_NODE0)];
        return v >= 0 ? v : id;
    };
    for (int &v : S.fnode) if (v >= 0) v = rm(v);
    std::set<int> nn;
    for (int id : S.nodes) nn.insert(rm(id));
    S.nodes.swap(nn);
    Adj na;
    for (const auto &kv : nadj) {
        int a = rm(kv.first);
        std::vector<int> &row = na[a];
        for (int b : kv.second) {
            int b2 = rm(b);
            if (b2 != a) row.push_back(b2);
        }
    }
    for (auto &kv : na) {
        std::sort(kv.second.begin(), kv.second.end());
        kv.second.erase(std::unique(kv.second.begin(), kv.second.end()), kv.second.end());
    }
    nadj.swap(na);
    return true;
}

template <class I>
static void apply_split(const ProgramT<I> &p, const std::vector<char> &reach,
                        const SplitMapT<I> &S,
                        const std::unordered_map<int, int> &cmap,
                        std::vector<typename I::Word> &words) {
    typedef typename I::Word Word;
    typedef typename I::RSet RSet;
    words.assign((size_t)p.n, Word());
    std::vector<Field> fm;
    auto C = [&](int nd) {
        auto it = cmap.find(nd);
        return it == cmap.end() ? nd : it->second;
    };

    std::vector<std::pair<int, int>> defcol, usecol;
    auto colget = [](const std::vector<std::pair<int, int>> &m, int k) {
        for (const auto &pr : m) if (pr.first == k) return pr.second;
        return -1;
    };
    for (int i = 0; i < p.n; i++) {
        Word q = p.q[i];
        words[(size_t)i] = q;
        if (I::empty(q) || !reach[(size_t)i]) continue;
        I::fieldmap(q, p.op[i], p.props[i], fm);
        Word nq = q;
        defcol.clear();
        usecol.clear();
        for (const Field &f : fm) {
            int nd = S.at(i, f.off);
            if (nd < 0) fail("split: no node for field %d at %d", f.off, i);
            int nb = C(nd);
            if (nb < 0 || nb >= RZ) fail("split: colour %d out of range at %d", nb, i);
            if (f.w > 1) {

                for (int k = 1; k < f.w; k++) {
                    auto it = cmap.find(nd + k);
                    int ck = (it == cmap.end()) ? nd + k : it->second;
                    if (ck != nb + k) fail("split: group at %d broken", i);
                }
            }
            for (int k = 0; k < f.w; k++)
                (f.kind == 'd' ? defcol : usecol)
                    .push_back(std::make_pair(f.base + k, nb + k));
            I::set_field(nq, f.off, nb);
        }
        words[(size_t)i] = nq;

        RSet d, md, u;
        ProgramT<I>::du_word(nq, p.op[i], p.props[i], d, md, u);
        int spur_g = I::spurious_pred(p.op[i], nq);
        int spur_w = I::spurious_pred(p.op[i], q);
        if (spur_g >= 0 || spur_w >= 0) {
            RSet uf2;
            std::vector<int> v; u.list(v);
            for (int r : v) if (r != spur_g) uf2.add(r);
            u = uf2;
        }
        const RSet *gots[3] = {&d, &md, &u};
        const RSet *wants[3] = {&p.defs[i], &p.maydefs[i], &p.uses[i]};
        for (int k = 0; k < 3; k++) {
            RSet mapped;
            std::vector<int> v; wants[k]->list(v);
            for (int r : v) {
                if (k == 2 && r == spur_w) continue;
                if (r >= RZ) { mapped.add(r); continue; }

                int col = colget((k == 2) ? usecol : defcol, r);
                if (col < 0) col = colget((k == 2) ? defcol : usecol, r);
                if (col < 0)
                    fail("split: unmapped %s R%d at %d (%s)",
                         k == 2 ? "use" : "def", r, i, I::op_name(p.op[i]));
                mapped.add(col);
            }
            if (!(*gots[k] == mapped))
                fail("split: operand mismatch after renumbering at %d (%s)", i,
                     I::op_name(p.op[i]));
        }
    }
}

template <class I>
static void bank_conflicts_nodes(const ProgramT<I> &p, const std::vector<char> &reach,
                                 const SplitMapT<I> &S, BConf &bc) {
    std::vector<Field> fm;
    for (int i = 0; i < p.n; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fm);
        std::set<int> srcs;
        for (const Field &f : fm) {
            if (f.kind != 'u') continue;
            int nd = S.at(i, f.off);
            if (nd < 0) continue;
            for (int j = 0; j < f.w; j++)
                if (f.base + j < RZ) srcs.insert(nd + j);
        }
        std::vector<int> v(srcs.begin(), srcs.end());
        for (size_t x = 0; x < v.size(); x++)
            for (size_t y = x + 1; y < v.size(); y++) bc[{v[x], v[y]}]++;
    }
}

template <class I>
static void run_aligns(const ProgramT<I> &p, const std::vector<std::vector<int>> &runs,
                       const SplitMapT<I> *S, bool bywidth, RunAlign &ral) {
    const int ra = I::run_align();
    ral.assign(runs.size(), std::make_pair(1, 0));
    std::unordered_map<int, size_t> pos;
    for (size_t ri = 0; ri < runs.size(); ri++)
        if (runs[ri].size() > 1)
            for (int r : runs[ri]) pos[r] = ri;
    std::vector<int> need(runs.size(), 0);
    if (bywidth) {
        std::vector<Field> fm;
        for (int i = 0; i < p.n; i++) {
            if (I::empty(p.q[i])) continue;
            I::fieldmap(p.q[i], p.op[i], p.props[i], fm);
            for (const Field &f : fm) {
                if (f.w <= 1 || f.base >= RZ) continue;
                auto it = pos.find(f.base);
                if (it == pos.end()) continue;
                int a = I::tuple_align(f.w);
                if (f.base % a)
                    fail("tuple at R%d is not aligned for %d registers", f.base, f.w);
                need[it->second] = std::max(need[it->second], a);
            }
        }
    }
    std::unordered_map<int, const typename SplitMapT<I>::TRun *> tr;
    if (S)
        for (const auto &t : S->truns) tr[t.base] = &t;
    for (size_t ri = 0; ri < runs.size(); ri++) {
        const std::vector<int> &run = runs[ri];
        if (run.size() <= 1) continue;
        auto t = tr.find(run[0]);
        if (t != tr.end()) {
            ral[ri] = bywidth ? std::make_pair(t->second->step, t->second->start)
                              : std::make_pair(ra, t->second->name % ra);
            continue;
        }
        int m = (bywidth && need[ri]) ? need[ri] : ra;
        ral[ri] = std::make_pair(m, run[0] % m);
    }
}

template <class I>
static void apply_map(const ProgramT<I> &p, const std::unordered_map<int, int> &cmap,
                      std::vector<typename I::Word> &words) {
    typedef typename I::Word Word;
    words.assign((size_t)p.n, Word());
    std::vector<Field> fm;
    auto M = [&](int r) {
        auto it = cmap.find(r);
        return it == cmap.end() ? r : it->second;
    };
    for (int i = 0; i < p.n; i++) {
        Word q = p.q[i];
        if (I::empty(q)) { words[(size_t)i] = q; continue; }
        I::fieldmap(q, p.op[i], p.props[i], fm);
        Word nq = q;
        for (const Field &f : fm) {
            int nb = M(f.base);
            for (int k = 0; k < f.w; k++)
                if (M(f.base + k) != nb + k)
                    fail("group at %d (%s) broken", i, I::op_name(p.op[i]));
            I::set_field(nq, f.off, nb);
        }
        words[(size_t)i] = nq;
    }
}

template <class I>
static void gate_operands(const ProgramT<I> &p, const std::vector<typename I::Word> &words,
                          const std::unordered_map<int, int> &cmap) {
    typedef typename I::RSet RSet;
    auto M = [&](int r) {
        if (r >= RZ) return r;
        auto it = cmap.find(r);
        return it == cmap.end() ? r : it->second;
    };
    for (int i = 0; i < p.n; i++) {
        if (I::empty(p.q[i])) continue;
        RSet d, md, u;
        ProgramT<I>::du_word(words[(size_t)i], p.op[i], p.props[i], d, md, u);

        int spur_g = I::spurious_pred(p.op[i], words[(size_t)i]);
        int spur_w = I::spurious_pred(p.op[i], p.q[i]);
        RSet uf;
        if (spur_g >= 0 || spur_w >= 0) {
            std::vector<int> v; u.list(v);
            for (int r : v) if (r != spur_g) uf.add(r);
            u = uf;
        }
        const RSet *gots[3] = {&d, &md, &u};
        const RSet *wants[3] = {&p.defs[i], &p.maydefs[i], &p.uses[i]};
        for (int k = 0; k < 3; k++) {
            RSet mapped;
            std::vector<int> v; wants[k]->list(v);
            for (int r : v) {
                if (k == 2 && r == spur_w) continue;
                mapped.add(M(r));
            }
            if (!(*gots[k] == mapped))
                fail("operand mismatch after renumbering at %d (%s)", i,
                     I::op_name(p.op[i]));
        }
    }
}

bool g_bank = false;

template <class I>
static long long bank_cost_of(const BConf &bconf,
                              const std::unordered_map<int, int> &cmap) {
    long long n = 0;
    for (const auto &pr : bconf) {
        auto a = cmap.find(pr.first.first);
        auto b = cmap.find(pr.first.second);
        if (a == cmap.end() || b == cmap.end()) continue;

        if (a->second == b->second) continue;
        if (I::reg_bank(a->second) == I::reg_bank(b->second)) n += pr.second;
    }
    return n;
}

template <class I>
static long long bank_repair(const std::vector<std::vector<int>> &runs,
                             const Adj &adj, const std::set<int> &pinned,
                             const BConf &bconf, int limit,
                             std::unordered_map<int, int> &cmap,
                             const RunAlign *ral = nullptr) {
    if (bconf.empty() || cmap.empty()) return 0;
    long long before = bank_cost_of<I>(bconf, cmap);
    if (!before) return 0;

    int maxid_ = 0;
    for (const auto &rn_ : runs)
        for (int r : rn_) if (r > maxid_) maxid_ = r;
    std::vector<int> cidx((size_t)maxid_ + 1, -1);
    int NU = 0;
    for (const auto &rn_ : runs)
        for (int r : rn_) if (cidx[(size_t)r] < 0) cidx[(size_t)r] = NU++;
    const int W = (NU + 63) / 64;
    std::vector<u64> ADJ((size_t)NU * W, 0);
    for (const auto &rn_ : runs)
        for (int r : rn_) {
            auto ait = adj.find(r);
            if (ait == adj.end()) continue;
            u64 *row = &ADJ[(size_t)cidx[(size_t)r] * W];
            for (int o : ait->second)
                if (o >= 0 && o <= maxid_ && cidx[(size_t)o] >= 0)
                    row[cidx[(size_t)o] >> 6] |= (u64)1 << (cidx[(size_t)o] & 63);
        }
    const int NCOL = RZ + 8;
    std::vector<u64> TK((size_t)NCOL * W, 0);
    std::vector<int> col((size_t)maxid_ + 1, -1);
    for (const auto &pr : cmap) {
        if (pr.first < 0 || pr.first > maxid_ || cidx[(size_t)pr.first] < 0)
            fail("bank repair: coloured node %d is not in any run", pr.first);
        if (pr.second < 0 || pr.second >= NCOL)
            fail("bank repair: colour %d out of the taken table", pr.second);
        col[(size_t)pr.first] = pr.second;
        int x = cidx[(size_t)pr.first];
        TK[(size_t)pr.second * W + (x >> 6)] |= (u64)1 << (x & 63);
    }
    auto colof = [&](int node) {
        return (node >= 0 && node <= maxid_) ? col[(size_t)node] : -1;
    };

    std::unordered_map<int, std::vector<std::pair<int, int>>> bcadj;
    for (const auto &pr : bconf) {
        bcadj[pr.first.first].push_back({pr.first.second, pr.second});
        bcadj[pr.first.second].push_back({pr.first.first, pr.second});
    }

    std::vector<char> pin(runs.size(), 0);
    for (size_t i = 0; i < runs.size(); i++)
        for (int r : runs[i]) if (pinned.count(r)) pin[i] = 1;

    auto member = [&](const std::vector<int> &run, int node) {
        for (int r : run) if (r == node) return true;
        return false;
    };

    auto cost_at = [&](const std::vector<int> &run, int base) {
        long long n = 0;
        for (size_t k = 0; k < run.size(); k++) {
            auto it = bcadj.find(run[k]);
            if (it == bcadj.end()) continue;
            int c = base + (int)k;
            for (const auto &pw : it->second) {
                if (member(run, pw.first)) continue;
                int cp = colof(pw.first);
                if (cp < 0) continue;
                if (cp == c) continue;
                if (I::reg_bank(cp) == I::reg_bank(c)) n += pw.second;
            }
        }
        return n;
    };

    std::vector<u64> runm((size_t)W, 0);
    auto fits = [&](const std::vector<int> &run, int base) {
        for (int r : run) {
            int x = cidx[(size_t)r];
            runm[(size_t)(x >> 6)] |= (u64)1 << (x & 63);
        }
        bool ok = true;
        for (size_t k = 0; k < run.size() && ok; k++) {
            int c = base + (int)k;
            if (c >= NCOL) continue;
            const u64 *tk = &TK[(size_t)c * W];
            const u64 *row = &ADJ[(size_t)cidx[(size_t)run[k]] * W];
            for (int w = 0; w < W; w++)
                if (tk[w] & row[w] & ~runm[(size_t)w]) { ok = false; break; }
        }
        for (int r : run) {
            int x = cidx[(size_t)r];
            runm[(size_t)(x >> 6)] = 0;
        }
        return ok;
    };

    std::vector<char> colfixed((size_t)limit + 1, 0);
    for (size_t i = 0; i < runs.size(); i++) {
        if (runs[i].size() > 1 || pin[i]) {
            for (int r : runs[i]) {
                int c = cmap.at(r);
                if (c >= 0 && c <= limit) colfixed[(size_t)c] = 1;
            }
        }
    }
    std::vector<std::vector<int>> cls((size_t)limit + 1);
    for (const auto &pr : cmap)
        if (pr.second >= 0 && pr.second <= limit)
            cls[(size_t)pr.second].push_back(pr.first);

    std::vector<int> tstamp((size_t)NU, 0);
    int tepoch = 0;
    auto local_cost = [&](int c1, int c2) {
        long long n = 0;
        tepoch++;
        for (int u : cls[(size_t)c1]) tstamp[(size_t)cidx[(size_t)u]] = tepoch;
        for (int u : cls[(size_t)c2]) tstamp[(size_t)cidx[(size_t)u]] = tepoch;
        for (int pass = 0; pass < 2; pass++) {
            for (int u : cls[(size_t)(pass ? c2 : c1)]) {
                auto it = bcadj.find(u);
                if (it == bcadj.end()) continue;
                int cu = col[(size_t)u];
                for (const auto &pw : it->second) {
                    bool touched = pw.first >= 0 && pw.first <= maxid_ &&
                                   cidx[(size_t)pw.first] >= 0 &&
                                   tstamp[(size_t)cidx[(size_t)pw.first]] == tepoch;
                    if (touched && pw.first < u) continue;
                    int cp = colof(pw.first);
                    if (cp < 0) continue;
                    if (cp == cu) continue;
                    if (I::reg_bank(cp) != I::reg_bank(cu)) continue;
                    n += pw.second;
                }
            }
        }
        return n;
    };

    auto colour_cost = [&](int c) {
        long long n = 0;
        for (int u : cls[(size_t)c]) {
            auto it = bcadj.find(u);
            if (it == bcadj.end()) continue;
            int cu = col[(size_t)u];
            for (const auto &pw : it->second) {
                int cp = colof(pw.first);
                if (cp < 0 || cp == cu) continue;
                if (I::reg_bank(cp) == I::reg_bank(cu)) n += pw.second;
            }
        }
        return n;
    };
    auto swap_classes = [&](int c1, int c2) {
        for (int u : cls[(size_t)c1]) { cmap[u] = c2; col[(size_t)u] = c2; }
        for (int u : cls[(size_t)c2]) { cmap[u] = c1; col[(size_t)u] = c1; }
        cls[(size_t)c1].swap(cls[(size_t)c2]);
        std::swap_ranges(TK.begin() + (size_t)c1 * W,
                         TK.begin() + (size_t)(c1 + 1) * W,
                         TK.begin() + (size_t)c2 * W);
    };

    long long budget = 40000;
    for (int round = 0; round < 3; round++) {
        bool any = false;
        for (int sweep = 0; sweep < 6 && budget > 0; sweep++) {
            bool moved = false;
            for (int c1 = 0; c1 < limit && budget > 0; c1++) {
                if (colfixed[(size_t)c1] || cls[(size_t)c1].empty()) continue;
                if (!colour_cost(c1)) continue;
                for (int c2 = c1 + 1; c2 < limit && budget > 0; c2++) {
                    if (colfixed[(size_t)c2]) continue;
                    if (I::reg_bank(c1) == I::reg_bank(c2)) continue;
                    budget--;
                    long long b2 = local_cost(c1, c2);
                    swap_classes(c1, c2);
                    long long a2 = local_cost(c1, c2);
                    if (a2 < b2) { moved = true; break; }
                    swap_classes(c1, c2);
                }
            }
            if (!moved) break;
            any = true;
        }

        for (int sweep = 0; sweep < 4; sweep++) {
            bool moved = false;
            for (size_t i = 0; i < runs.size(); i++) {
                if (pin[i]) continue;
                const std::vector<int> &run = runs[i];
                int cur = cmap.at(run[0]);
                long long c0 = cost_at(run, cur);
                if (!c0) continue;

                int step = run.size() > 1 ? I::run_align() : 1;
                int start = run.size() > 1 ? (run[0] % I::run_align()) : 0;
                if (ral) { step = (*ral)[i].first; start = (*ral)[i].second; }
                int hi = limit - (int)run.size();
                int best = cur;
                long long bestc = c0;
                for (int b = start; b <= hi; b += step) {
                    if (b == cur) continue;
                    if (!fits(run, b)) continue;
                    long long c = cost_at(run, b);
                    if (c < bestc || (c == bestc && b < best)) { bestc = c; best = b; }
                }
                if (best != cur) {
                    for (size_t k = 0; k < run.size(); k++) {
                        int x = cidx[(size_t)run[k]];
                        u64 bit = (u64)1 << (x & 63);
                        TK[(size_t)(cur + (int)k) * W + (x >> 6)] &= ~bit;
                        cmap[run[k]] = best + (int)k;
                        col[(size_t)run[k]] = best + (int)k;
                        if (best + (int)k >= NCOL)
                            fail("bank repair: colour %d out of the taken "
                                 "table", best + (int)k);
                        TK[(size_t)(best + (int)k) * W + (x >> 6)] |= bit;
                    }
                    moved = true;
                }
            }
            if (!moved) break;
            any = true;

            for (auto &v : cls) v.clear();
            for (const auto &pr : cmap)
                if (pr.second >= 0 && pr.second <= limit)
                    cls[(size_t)pr.second].push_back(pr.first);
        }
        if (!any) break;
    }
    long long after = bank_cost_of<I>(bconf, cmap);
    return before - after;
}

struct AntiModel {
    std::map<std::pair<int, int>, int> w;
    long long total = 0;
    void add(int a, int b, int v) {
        if (a == b || v <= 0) return;
        if (a > b) std::swap(a, b);
        w[{a, b}] += v;
        total += v;
    }
};

static long long anti_cost_of(const AntiModel &A,
                              const std::unordered_map<int, int> &cmap) {
    long long n = 0;
    for (const auto &pr : A.w) {
        auto a = cmap.find(pr.first.first);
        auto b = cmap.find(pr.first.second);
        if (a == cmap.end() || b == cmap.end()) continue;
        if (a->second == b->second) n += pr.second;
    }
    return n;
}

template <class I>
static void build_anti(const ProgramT<I> &p, const std::vector<char> &reach,
                       const std::vector<u8> &cls,
                       const std::vector<char> &leader,
                       const std::function<int(int, int)> &nodeof,
                       AntiModel &A) {
    const int WINDOW = 10;
    int n = p.n;
    std::vector<Field> fm;
    std::vector<std::vector<int>> rd((size_t)n), wr((size_t)n);
    std::vector<int> nsrc((size_t)n, 0);
    for (int i = 0; i < n; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fm);
        for (const Field &f : fm) {
            if (f.base >= RZ) continue;
            int nd = nodeof(i, f.off);
            if (nd < 0) continue;
            if (f.kind == 'd') wr[(size_t)i].push_back(nd);
            else { rd[(size_t)i].push_back(nd); nsrc[(size_t)i] += f.w; }
        }
    }
    for (int i = 0; i < n; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;

        if (!(cls[(size_t)i] & 1)) continue;
        if (!(cls[(size_t)i] & 6)) continue;
        if (rd[(size_t)i].empty() && wr[(size_t)i].empty()) continue;
        int w = 5 + (nsrc[(size_t)i] >> 1);
        for (int j = i + 1; j < n && j - i <= WINDOW; j++) {
            if (leader[(size_t)j]) break;
            if (I::empty(p.q[j]) || !reach[(size_t)j]) continue;
            for (int v : wr[(size_t)j]) {
                for (int u : rd[(size_t)i]) A.add(u, v, w);
                for (int u : wr[(size_t)i]) A.add(u, v, 5);
            }
        }
    }
}

template <class I>
static long long anti_repair(const std::vector<std::vector<int>> &runs,
                             const Adj &adj, const std::set<int> &pinned,
                             const AntiModel &A, int limit,
                             std::unordered_map<int, int> &cmap,
                             const RunAlign *ral = nullptr) {
    if (A.w.empty() || cmap.empty()) return 0;
    long long before = anti_cost_of(A, cmap);
    if (!before) return 0;

    int maxid_ = 0;
    for (const auto &rn_ : runs)
        for (int r : rn_) if (r > maxid_) maxid_ = r;
    std::vector<int> cidx((size_t)maxid_ + 1, -1);
    int NU = 0;
    for (const auto &rn_ : runs)
        for (int r : rn_) if (cidx[(size_t)r] < 0) cidx[(size_t)r] = NU++;
    const int W = (NU + 63) / 64;
    std::vector<u64> ADJ((size_t)NU * W, 0);
    for (const auto &rn_ : runs)
        for (int r : rn_) {
            auto ait = adj.find(r);
            if (ait == adj.end()) continue;
            u64 *row = &ADJ[(size_t)cidx[(size_t)r] * W];
            for (int o : ait->second)
                if (o >= 0 && o <= maxid_ && cidx[(size_t)o] >= 0)
                    row[cidx[(size_t)o] >> 6] |= (u64)1 << (cidx[(size_t)o] & 63);
        }
    const int NCOL = RZ + 8;
    std::vector<u64> TK((size_t)NCOL * W, 0);
    std::vector<int> col((size_t)maxid_ + 1, -1);
    for (const auto &pr : cmap) {
        if (pr.first < 0 || pr.first > maxid_ || cidx[(size_t)pr.first] < 0)
            fail("anti repair: coloured node %d is not in any run", pr.first);
        if (pr.second < 0 || pr.second >= NCOL)
            fail("anti repair: colour %d out of the taken table", pr.second);
        col[(size_t)pr.first] = pr.second;
        int x = cidx[(size_t)pr.first];
        TK[(size_t)pr.second * W + (x >> 6)] |= (u64)1 << (x & 63);
    }
    auto colof = [&](int node) {
        return (node >= 0 && node <= maxid_) ? col[(size_t)node] : -1;
    };
    std::unordered_map<int, std::vector<std::pair<int, int>>> aadj;
    for (const auto &pr : A.w) {
        aadj[pr.first.first].push_back({pr.first.second, pr.second});
        aadj[pr.first.second].push_back({pr.first.first, pr.second});
    }
    std::vector<char> pin(runs.size(), 0);
    for (size_t i = 0; i < runs.size(); i++)
        for (int r : runs[i]) if (pinned.count(r)) pin[i] = 1;

    auto member = [&](const std::vector<int> &run, int node) {
        for (int r : run) if (r == node) return true;
        return false;
    };
    auto cost_at = [&](const std::vector<int> &run, int base) {
        long long n = 0;
        for (size_t k = 0; k < run.size(); k++) {
            auto it = aadj.find(run[k]);
            if (it == aadj.end()) continue;
            int c = base + (int)k;
            for (const auto &pw : it->second) {
                if (member(run, pw.first)) continue;
                int cp = colof(pw.first);
                if (cp < 0) continue;
                if (cp == c) n += pw.second;
            }
        }
        return n;
    };
    std::vector<u64> runm((size_t)W, 0);
    auto fits = [&](const std::vector<int> &run, int base) {
        for (int r : run) {
            int x = cidx[(size_t)r];
            runm[(size_t)(x >> 6)] |= (u64)1 << (x & 63);
        }
        bool ok = true;
        for (size_t k = 0; k < run.size() && ok; k++) {
            int c = base + (int)k;
            if (c >= NCOL) continue;
            const u64 *tk = &TK[(size_t)c * W];
            const u64 *row = &ADJ[(size_t)cidx[(size_t)run[k]] * W];
            for (int w = 0; w < W; w++)
                if (tk[w] & row[w] & ~runm[(size_t)w]) { ok = false; break; }
        }
        for (int r : run) {
            int x = cidx[(size_t)r];
            runm[(size_t)(x >> 6)] = 0;
        }
        return ok;
    };

    for (int sweep = 0; sweep < 6; sweep++) {
        bool moved = false;
        for (size_t i = 0; i < runs.size(); i++) {
            if (pin[i]) continue;
            const std::vector<int> &run = runs[i];
            int cur = cmap.at(run[0]);
            long long c0 = cost_at(run, cur);
            if (!c0) continue;
            int step = run.size() > 1 ? I::run_align() : 1;
            int start = run.size() > 1 ? (run[0] % I::run_align()) : 0;
            if (ral) { step = (*ral)[i].first; start = (*ral)[i].second; }
            int hi = limit - (int)run.size();
            int best = cur;
            long long bestc = c0;
            for (int b = start; b <= hi; b += step) {
                if (b == cur) continue;
                if (!fits(run, b)) continue;
                long long c = cost_at(run, b);
                if (c < bestc || (c == bestc && b < best)) { bestc = c; best = b; }
            }
            if (best != cur) {
                for (size_t k = 0; k < run.size(); k++) {
                    int x = cidx[(size_t)run[k]];
                    u64 bit = (u64)1 << (x & 63);
                    TK[(size_t)(cur + (int)k) * W + (x >> 6)] &= ~bit;
                    cmap[run[k]] = best + (int)k;
                    col[(size_t)run[k]] = best + (int)k;
                    if (best + (int)k >= NCOL)
                        fail("anti repair: colour %d out of the taken table",
                             best + (int)k);
                    TK[(size_t)(best + (int)k) * W + (x >> 6)] |= bit;
                }
                moved = true;
            }
        }
        if (!moved) break;
    }
    return before - anti_cost_of(A, cmap);
}

template <class I>
bool web_map(const std::vector<u8> &bc_in, const std::vector<u8> &ct_in,
             bool fragment, std::vector<int> &wuse, std::vector<int> &wdef,
             int &nslots) {
    const OpSets &T = I::sets();
    ProgramT<I> p;
    p.load_bytes(bc_in, ct_in);
    CFGraph c;
    std::vector<char> reach;
    c.build(p, false);
    reach = c.reachable_from_entry();
    std::vector<int> exit_live;
    if (fragment) I::exit_live_regs(bc_in, exit_live);
    Live L;
    liveness(p, c, reach, exit_live, L);

    int n = p.n;
    nslots = n;
    wuse.assign((size_t)n * WEB_STRIDE, -1);
    wdef.assign((size_t)n * WEB_STRIDE, -1);

    std::vector<Field> fm;
    std::set<int> wide, used;
    for (int i = 0; i < n; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fm);
        fm_regs(fm, used);
        for (const Field &f : fm)
            if (f.w > 1)
                for (int k = 0; k < f.w; k++) wide.insert(f.base + k);
    }
    std::set<int> pinset(exit_live.begin(), exit_live.end());

    std::vector<char> splitok((size_t)RZ, 0);
    for (int r : used)
        if (r >= 0 && r < RZ && !wide.count(r) && !pinset.count(r))
            splitok[(size_t)r] = 1;
    auto splittable = [&](int r) { return r >= 0 && r < RZ && splitok[(size_t)r]; };

    const std::vector<Mask> &lin = L.live;
    std::vector<Mask> lout((size_t)n);
    Mask seed;
    for (int r : exit_live) seed.set(r);
    for (int i = 0; i < n; i++) {
        if (!reach[(size_t)i]) continue;
        if (c.succ[(size_t)i].empty()) lout[(size_t)i] = seed;
        else
            for (int t : c.succ[(size_t)i])
                if (reach[(size_t)t]) lout[(size_t)i] |= lin[(size_t)t];
        if (p.op[i] == T.O_Exit || p.op[i] == T.O_Ret) lout[(size_t)i] |= seed;
    }

    std::vector<std::vector<int>> innode((size_t)RZ), outnode((size_t)RZ);
    std::vector<int> uf(2 * (size_t)n);

    auto find = [&uf](int x) {
        while (uf[(size_t)x] != x) {
            uf[(size_t)x] = uf[(size_t)uf[(size_t)x]];
            x = uf[(size_t)x];
        }
        return x;
    };
    int next = SPLIT_NODE0;
    for (int r : used) {
        if (!splittable(r)) continue;
        for (int i = 0; i < 2 * n; i++) uf[(size_t)i] = i;
        for (int i = 0; i < n; i++) {
            if (!reach[(size_t)i]) continue;
            bool li = lin[(size_t)i].test(r), lo = lout[(size_t)i].test(r);
            bool killed = L.dmask[(size_t)i].test(r) && !p.maydefs[i].has(r);
            if (li && lo && !killed) {
                int a = find(2 * i), b = find(2 * i + 1);
                if (a != b) uf[(size_t)b] = a;
            }
        }
        for (int i = 0; i < n; i++) {
            if (!reach[(size_t)i] || !lout[(size_t)i].test(r)) continue;
            for (int t : c.succ[(size_t)i]) {
                if (!reach[(size_t)t] || !lin[(size_t)t].test(r)) continue;
                int a = find(2 * i + 1), b = find(2 * t);
                if (a != b) uf[(size_t)b] = a;
            }
        }
        std::unordered_map<int, int> rep2node;
        std::vector<int> &vi = innode[r], &vo = outnode[r];
        vi.assign((size_t)n, -1);
        vo.assign((size_t)n, -1);
        for (int i = 0; i < n; i++) {
            if (!reach[(size_t)i]) continue;
            if (lin[(size_t)i].test(r)) {
                int rp = find(2 * i);
                auto it = rep2node.find(rp);
                if (it == rep2node.end()) it = rep2node.emplace(rp, next++).first;
                vi[(size_t)i] = it->second;
            }
            if (lout[(size_t)i].test(r)) {
                int rp = find(2 * i + 1);
                auto it = rep2node.find(rp);
                if (it == rep2node.end()) it = rep2node.emplace(rp, next++).first;
                vo[(size_t)i] = it->second;
            }
        }
    }

    std::unordered_map<long long, int> deadnode;
    auto defnode = [&](int i, int r) {
        if (!splittable(r)) return r;
        int v = outnode[r][(size_t)i];
        if (v >= 0) return v;
        v = lin[(size_t)i].test(r) ? innode[r][(size_t)i] : -1;
        if (v >= 0) return v;
        long long k = (long long)i * WEB_STRIDE + r;
        auto it = deadnode.find(k);
        if (it != deadnode.end()) return it->second;
        int id = next++;
        deadnode[k] = id;
        return id;
    };
    auto usenode = [&](int i, int r) {
        if (!splittable(r)) return r;
        int v = innode[r][(size_t)i];
        return v;
    };

    for (int i = 0; i < n; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fm);
        for (const Field &f : fm) {
            for (int k = 0; k < f.w; k++) {
                int r = f.base + k;
                if (r < 0 || r >= WEB_STRIDE) continue;
                int nd = (f.w > 1) ? r
                       : (f.kind == 'd' ? defnode(i, r) : usenode(i, r));
                if (nd < 0) continue;
                if (f.kind == 'd') {
                    wdef[(size_t)i * WEB_STRIDE + r] = nd;

                    if (!splittable(r))
                        wuse[(size_t)i * WEB_STRIDE + r] = r;
                    else if (lin[(size_t)i].test(r))
                        wuse[(size_t)i * WEB_STRIDE + r] = innode[r][(size_t)i];
                } else {
                    wuse[(size_t)i * WEB_STRIDE + r] = nd;
                }
            }
        }
    }
    return true;
}
template bool web_map<Sm50>(const std::vector<u8> &, const std::vector<u8> &, bool,
                            std::vector<int> &, std::vector<int> &, int &);
template bool web_map<Sm86>(const std::vector<u8> &, const std::vector<u8> &, bool,
                            std::vector<int> &, std::vector<int> &, int &);

template <class I>
static void rename_check(const ProgramT<I> &p, const CFGraph &c, const std::vector<char> &reach,
                         const std::vector<int> &exit_live,
                         const std::vector<typename I::Word> &nw) {
    const int n = p.n;
    std::vector<Field> fa, fb;
    std::vector<int> dfirst((size_t)n + 1, 0), regA, regB;
    std::vector<char> dmay;
    std::vector<std::vector<int>> defsA((size_t)RZ), defsB((size_t)RZ);
    for (int i = 0; i < n; i++) {
        dfirst[(size_t)i] = (int)regA.size();
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fa);
        I::fieldmap(nw[(size_t)i], I::decode_op(nw[(size_t)i]), I::decode_props(nw[(size_t)i]), fb);
        if (fa.size() != fb.size()) fail("rename check: operands differ at %d", i);
        for (size_t f = 0; f < fa.size(); f++) {
            if (fa[f].kind != fb[f].kind || fa[f].w != fb[f].w || fa[f].off != fb[f].off)
                fail("rename check: operand %zu differs at %d", f, i);
            if (fa[f].kind != 'd') continue;
            for (int k = 0; k < fa[f].w; k++) {
                int ra = fa[f].base + k, rb = fb[f].base + k;
                if ((ra >= RZ) != (rb >= RZ)) fail("rename check: R%d at %d is now R%d", ra, i, rb);
                if (ra >= RZ) continue;
                int id = (int)regA.size();
                regA.push_back(ra);
                regB.push_back(rb);
                dmay.push_back(p.maydefs[i].has(ra) ? 1 : 0);
                defsA[(size_t)ra].push_back(id);
                defsB[(size_t)rb].push_back(id);
            }
        }
    }
    dfirst[(size_t)n] = (int)regA.size();
    const int ND = (int)regA.size(), NB = ND + RZ;
    const int W = (NB + 63) / 64;
    auto solve = [&](const std::vector<int> &reg, const std::vector<std::vector<int>> &defs,
                     std::vector<u64> &in) {
        in.assign((size_t)n * W, 0);
        std::vector<u64> out((size_t)n * W, 0), t((size_t)W);
        for (bool ch = true; ch;) {
            ch = false;
            for (int i = 0; i < n; i++) {
                if (!reach[(size_t)i]) continue;
                std::fill(t.begin(), t.end(), 0);
                if (i == 0)
                    for (int r = 0; r < RZ; r++)
                        t[(size_t)((ND + r) >> 6)] |= (u64)1 << ((ND + r) & 63);
                for (int q : c.pred[(size_t)i])
                    if (reach[(size_t)q])
                        for (int w = 0; w < W; w++) t[(size_t)w] |= out[(size_t)q * W + w];
                u64 *iw = &in[(size_t)i * W];
                for (int w = 0; w < W; w++) iw[w] = t[(size_t)w];
                for (int d = dfirst[(size_t)i]; d < dfirst[(size_t)i + 1]; d++) {
                    if (dmay[(size_t)d]) continue;
                    int r = reg[(size_t)d];
                    for (int o : defs[(size_t)r]) t[(size_t)(o >> 6)] &= ~((u64)1 << (o & 63));
                    t[(size_t)((ND + r) >> 6)] &= ~((u64)1 << ((ND + r) & 63));
                }
                for (int d = dfirst[(size_t)i]; d < dfirst[(size_t)i + 1]; d++)
                    t[(size_t)(d >> 6)] |= (u64)1 << (d & 63);
                u64 *ow = &out[(size_t)i * W];
                for (int w = 0; w < W; w++)
                    if (ow[w] != t[(size_t)w]) { ow[w] = t[(size_t)w]; ch = true; }
            }
        }
    };
    std::vector<u64> inA, inB;
    solve(regA, defsA, inA);
    solve(regB, defsB, inB);
    std::vector<int> sa, sb;
    auto reached = [&](const std::vector<u64> &in, const std::vector<std::vector<int>> &defs,
                       int i, int r, std::vector<int> &s) {
        s.clear();
        const u64 *iw = &in[(size_t)i * W];
        for (int d : defs[(size_t)r]) if (iw[d >> 6] & ((u64)1 << (d & 63))) s.push_back(d);
        if (iw[(ND + r) >> 6] & ((u64)1 << ((ND + r) & 63))) s.push_back(-1);
        std::sort(s.begin(), s.end());
    };
    auto same = [&](int i, int ra, int rb) {
        reached(inA, defsA, i, ra, sa);
        reached(inB, defsB, i, rb, sb);
        if (sa != sb)
            fail("rename check: R%d at %d (%s, now R%d) is reached by other writes", ra, i,
                 I::op_name(p.op[i]), rb);
    };
    for (int i = 0; i < n; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fa);
        I::fieldmap(nw[(size_t)i], I::decode_op(nw[(size_t)i]), I::decode_props(nw[(size_t)i]), fb);
        for (size_t f = 0; f < fa.size(); f++)
            for (int k = 0; k < fa[f].w; k++) {
                int ra = fa[f].base + k, rb = fb[f].base + k;
                if ((ra >= RZ) != (rb >= RZ)) fail("rename check: R%d at %d is now R%d", ra, i, rb);
                if (ra >= RZ) continue;

                if (fa[f].kind == 'd' && !p.maydefs[i].has(ra)) continue;
                same(i, ra, rb);
            }

        if (c.succ[(size_t)i].empty() || c.cat[(size_t)i] == C_EXIT)
            for (int r : exit_live) same(i, r, r);
    }
}

struct RnEntry {
    std::vector<u8> bc, ct;
    RegStats st;
};
template <class I> static std::map<std::string, RnEntry> g_rn_cache;
template <class I> void renumber_cache_clear() { g_rn_cache<I>.clear(); }
template void renumber_cache_clear<Sm50>();
template void renumber_cache_clear<Sm86>();

template <class I>
static void renumber_uncached(std::vector<u8> &bc, std::vector<u8> &ct,
                              bool fragment, bool bank_aware, RegStats &st,
                              int need_warps);

template <class I>
void renumber(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
              bool bank_aware, RegStats &st, int need_warps) {
    std::string key;
    key.reserve(bc.size() + ct.size() + 2);
    key.push_back(fragment ? 'F' : 'V');
    key.push_back(bank_aware ? 'B' : 'b');
    key.append((const char *)bc.data(), bc.size());
    key.append((const char *)ct.data(), ct.size());
    auto it = g_rn_cache<I>.find(key);
    if (it != g_rn_cache<I>.end()) {
        bc = it->second.bc;
        ct = it->second.ct;
        st = it->second.st;
        return;
    }
    renumber_uncached<I>(bc, ct, fragment, bank_aware, st, need_warps);

    if (st.floored) return;
    RnEntry e;
    e.bc = bc;
    e.ct = ct;
    e.st = st;
    g_rn_cache<I>.emplace(std::move(key), std::move(e));
}

template <class I>
static void renumber_uncached_i(std::vector<u8> &bc, std::vector<u8> &ct,
                              bool fragment, bool bank_aware, RegStats &st,
                              int need_warps);
template <class I>
static void renumber_uncached(std::vector<u8> &bc, std::vector<u8> &ct,
                              bool fragment, bool bank_aware, RegStats &st,
                              int need_warps) {
    renumber_uncached_i<I>(bc, ct, fragment, bank_aware, st, need_warps);
}
template <class I>
static void renumber_uncached_i(std::vector<u8> &bc, std::vector<u8> &ct,
                              bool fragment, bool bank_aware, RegStats &st,
                              int need_warps) {
    ProgramT<I> p;
    p.load_bytes(bc, ct);
    u32 co = p.co;
    const int tmode = I::renumber_mode();

    std::vector<u8> g_icls;
    std::vector<char> g_bbleader;
    int nsl = I::nslots(co);
    if (nsl < 0) nsl = 0;
    g_icls.assign((size_t)nsl + 8, 0);
    int got = I::inst_class(bc, co, nsl, g_icls.data());
    if (got != nsl)
        fail("renumber: instruction classes returned %d for %d slots", got, nsl);

    check_fieldmap(p);

    CFGraph c;
    std::vector<char> reach;
    c.build(p, false);
    reach = c.reachable_from_entry();

    std::vector<int> exit_live;
    if (fragment) I::exit_live_regs(bc, exit_live);

    Live L;
    liveness(p, c, reach, exit_live, L);

    int old_maxlive = 0;
    for (int i = 0; i < p.n; i++)
        if (reach[(size_t)i])
            old_maxlive = std::max(old_maxlive, L.live[(size_t)i].popcount());
    if (need_warps > 0 && I::occupancy_of(old_maxlive) < need_warps) {
        st.floored = 1;
        return;
    }

    Adj adj;
    interference(p, reach, L, adj, (tmode & RN_DEFS) != 0);

    g_bbleader.assign((size_t)p.n + 8, 0);
    if (p.n) g_bbleader[0] = 1;
    for (int i = 0; i < p.n; i++) {
        if (I::empty(p.q[i])) continue;
        bool falls = false;
        for (int t : c.succ[(size_t)i]) {
            if (t == i + 1) falls = true;
            else if (t >= 0 && t < p.n) g_bbleader[(size_t)t] = 1;
        }
        if ((!falls || c.succ[(size_t)i].size() > 1) && i + 1 < p.n)
            g_bbleader[(size_t)i + 1] = 1;
    }

    std::set<int> used;
    std::vector<Field> fm;
    for (int i = 0; i < p.n; i++) {
        if (I::empty(p.q[i])) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fm);
        fm_regs(fm, used);
    }
    for (int r : used) adj[r];

    {
        std::vector<char> uset((size_t)RZ, 0);
        for (int r : used) uset[(size_t)r] = 1;
        auto uin = [&](int id) {
            return id >= 0 && id < RZ && uset[(size_t)id];
        };
        for (auto it = adj.begin(); it != adj.end();) {
            if (!uin(it->first)) it = adj.erase(it);
            else {
                std::vector<int> &row = it->second;
                row.erase(std::remove_if(row.begin(), row.end(),
                              [&](int r) { return !uin(r); }),
                          row.end());
                ++it;
            }
        }
    }
    std::set<int> pinned;
    for (int r : exit_live) if (used.count(r)) pinned.insert(r);

    auto maxc = [](const std::unordered_map<int, int> &m) {
        int mx = -1;
        for (auto &pr : m) mx = std::max(mx, pr.second);
        return mx;
    };

    struct Cand {
        std::vector<typename I::Word> words;
        u32 decl = 0;
        int maxcol = -1;
        std::vector<u8> bc, ct;
        int cycles = 0, warps = 0;
        std::unordered_map<int, int> cmap;
        bool have = false;
    };
    auto build = [&](bool usesplit, const SplitMapT<I> &S, std::set<int> &nodes,
                     Adj &cadj, Cand &out) {
        std::set<int> pin2;
        for (int r : exit_live) if (nodes.count(r)) pin2.insert(r);
        std::vector<std::vector<int>> runs;
        if (usesplit && !S.truns.empty()) {

            std::set<int> rest = nodes;
            for (const auto &t : S.truns)
                for (int k = 0; k < t.span; k++) rest.erase(t.base + k);
            runs_of(p, rest, runs);
            for (const auto &t : S.truns) {
                runs.emplace_back();
                for (int k = 0; k < t.span; k++) runs.back().push_back(t.base + k);
            }
        } else runs_of(p, nodes, runs);
        RunAlign ral;
        if ((tmode & RN_ALIGN) || (usesplit && !S.truns.empty()))
            run_aligns(p, runs, usesplit ? &S : nullptr, (tmode & RN_ALIGN) != 0, ral);
        const RunAlign *ralp = ral.empty() ? nullptr : &ral;

        std::vector<int> rpos;
        if (tmode & RN_ORDERS) {
            std::unordered_map<int, int> first;
            std::vector<Field> fm2;
            for (int i = 0; i < p.n; i++) {
                if (I::empty(p.q[i]) || (usesplit && !reach[(size_t)i])) continue;
                I::fieldmap(p.q[i], p.op[i], p.props[i], fm2);
                for (const Field &f : fm2) {
                    if (f.kind != 'd' || f.base >= RZ) continue;
                    int nd = usesplit ? S.at(i, f.off) : f.base;
                    if (nd < 0) continue;
                    for (int k = 0; k < f.w; k++) first.emplace(nd + k, i);
                }
            }
            rpos.assign(runs.size(), -1);
            for (size_t ri = 0; ri < runs.size(); ri++) {
                int pmin = INT_MAX;
                for (int r : runs[ri]) {
                    auto it = first.find(r);
                    pmin = std::min(pmin, it == first.end() ? -1 : it->second);
                }
                rpos[ri] = pmin;
            }
        }
        const std::vector<int> *rposp = rpos.empty() ? nullptr : &rpos;

        Affinity aff;
        for (int i = 0; i < p.n; i++) {
            if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
            typename I::Word q = p.q[i];
            int d, s;
            if (!I::reg_move(q, p.op[i], &d, &s) || !I::guard_is_pt(q)) continue;
            if (d >= RZ || s >= RZ || d == s) continue;
            int nd = usesplit ? S.at(i, I::mov_dst_field()) : d;
            int ns = usesplit ? S.at(i, I::mov_src_field()) : s;
            if (nd < 0 || ns < 0 || nd == ns) continue;
            if (!nodes.count(nd) || !nodes.count(ns)) continue;
            aff.push_back({nd, ns});
        }
        const Affinity *affp = aff.empty() ? nullptr : &aff;
        std::unordered_map<int, int> cmap;
        colour<I>(runs, cadj, pin2, nullptr, -1, cmap, ORD_DEG, affp, ralp, rposp);
        int corder = ORD_DEG;
        if ((tmode & RN_ORDERS)) {

            for (int o = ORD_DEG + 1; o < ORD_N; o++) {
                if (o == ORD_DEF && !rposp) continue;
                std::unordered_map<int, int> alt;
                try {
                    colour<I>(runs, cadj, pin2, nullptr, -1, alt, o, affp, ralp, rposp);
                } catch (NoFit &) { continue; }
                if (maxc(alt) < maxc(cmap)) { cmap.swap(alt); corder = o; }
            }
        }
        BConf bconf;
        if (bank_aware || g_bank) {
            if (usesplit) bank_conflicts_nodes(p, reach, S, bconf);
            else bank_conflicts(p, bconf);
        }

        AntiModel amod;
        std::function<int(int, int)> nodeof;
        if (usesplit) nodeof = [&S](int i, int off) { return S.at(i, off); };
        else nodeof = [&p](int i, int off) {
            return I::field_reg(p.q[(size_t)i], off);
        };
        build_anti(p, reach, g_icls, g_bbleader, nodeof, amod);
        if (bank_aware) {
            int lim = cmap.empty() ? 1 : maxc(cmap) + 1;
            std::unordered_map<int, int> cmap2;
            bool ok = true;
            try {
                colour<I>(runs, cadj, pin2, &bconf, lim, cmap2, corder, affp, ralp, rposp);
            } catch (NoFit &) { ok = false; }
            if (ok && (cmap2.empty() || maxc(cmap2) < lim)) {
                cmap.swap(cmap2);
            }
        }

        std::unordered_map<int, int> cmap_rep;
        long long removed = 0;
        if (g_bank && !cmap.empty()) {
            cmap_rep = cmap;

            int blim = maxc(cmap) + 1;
            removed = bank_repair<I>(runs, cadj, pin2, bconf, blim, cmap_rep, ralp);
        }
        std::vector<int> colof;
        auto emit_from = [&](std::unordered_map<int, int> &cm, Cand &o) {

            int maxid = 0;
            for (auto &pr : cm) maxid = std::max(maxid, pr.first);
            colof.assign((size_t)maxid + 1, -1);
            for (auto &pr : cm) colof[(size_t)pr.first] = pr.second;
            for (auto &pr : cadj) {
                int ca = pr.first <= maxid ? colof[(size_t)pr.first] : -1;
                if (ca < 0) { (void)cm.at(pr.first); continue; }
                for (int b : pr.second) {
                    int cb2 = b <= maxid ? colof[(size_t)b] : -1;
                    if (cb2 < 0) { (void)cm.at(b); continue; }
                    if (ca == cb2)
                        fail("invalid colouring: interfering pair shares a register");
                }
            }
            if (usesplit) apply_split(p, reach, S, cm, o.words);
            else {
                apply_map(p, cm, o.words);
                gate_operands(p, o.words, cm);
            }
            o.maxcol = maxc(cm);
            o.decl = I::decl_regs(o.maxcol);
            o.cmap = cm;
            o.bc = bc;
            o.ct = ct;
            for (int i = 0; i < p.n; i++)
                I::write_word(o.bc, i, o.words[(size_t)i]);
            I::set_reg_count(o.ct, o.decl);
            I::phase_b(o.bc, co);
            o.cycles = I::issue_cycles(o.bc, co);
            o.warps = I::occupancy_of((int)o.decl);
            o.have = true;
        };
        emit_from(cmap, out);
        if (removed > 0) {

            Cand R;
            emit_from(cmap_rep, R);
            out = std::move(R);
        }

        if (!amod.w.empty() && !out.cmap.empty()) {
            std::unordered_map<int, int> cm2 = out.cmap;
            int alim = maxc(out.cmap) + 1;
            long long got = anti_repair<I>(runs, cadj, pin2, amod, alim, cm2, ralp);
            if (got > 0) {
                Cand R2;
                emit_from(cm2, R2);

                for (int i2 = 0; i2 < p.n; i2++) {
                    typename I::Word m = I::renumber_mask(p.q[(size_t)i2]);
                    if (!I::eq_outside(R2.words[(size_t)i2], out.words[(size_t)i2], m)) {
                        char ha[48], hb[48], hm[48];
                        I::hex(out.words[(size_t)i2], ha, sizeof ha);
                        I::hex(R2.words[(size_t)i2], hb, sizeof hb);
                        I::hex(m, hm, sizeof hm);
                        fail("anti: instruction %d changed outside its register "
                             "fields (%s -> %s, mask %s)", i2, ha, hb, hm);
                    }
                }
                out = std::move(R2);
            }
        }
    };

    std::set<int> namenodes = used;
    SplitMapT<I> none;
    Cand A;
    build(false, none, namenodes, adj, A);

    Cand B, Bt;
    SplitMapT<I> S, St;
    Adj nadj, nadjt;
    auto colour_split = [&](SplitMapT<I> &S, Adj &nadj, Cand &B) {
        std::set<int> nodes = S.nodes;
        for (int r : nodes) nadj[r];

        int maxid_ = nodes.empty() ? 0 : *nodes.rbegin();
        std::vector<char> nset((size_t)maxid_ + 1, 0);
        for (int r : nodes) nset[(size_t)r] = 1;
        auto nin = [&](int id) {
            return id >= 0 && id <= maxid_ && nset[(size_t)id];
        };
        for (auto it = nadj.begin(); it != nadj.end();) {
            if (!nin(it->first)) it = nadj.erase(it);
            else {
                std::vector<int> &row = it->second;
                row.erase(std::remove_if(row.begin(), row.end(),
                              [&](int r) { return !nin(r); }),
                          row.end());
                ++it;
            }
        }
        build(true, S, nodes, nadj, B);
    };
    bool bs_;
    bs_ = build_split(p, c, reach, L, exit_live, S, nadj, true, nullptr, false,
                      nullptr, tmode & ~RN_SPLIT);
    if (bs_) colour_split(S, nadj, B);
    if (tmode & RN_SPLIT) {

        std::vector<char> nosplit;
        bool settled = false;
        for (int attempt = 0; attempt < 8 && !settled; attempt++) {
            std::vector<int> conf;
            St = SplitMapT<I>();
            nadjt.clear();
            bs_ = build_split(p, c, reach, L, exit_live, St, nadjt, true, nullptr, false,
                              nullptr, tmode, nosplit.empty() ? nullptr : &nosplit,
                              &conf);
            if (conf.empty()) settled = true;
            nosplit.resize((size_t)RZ, 0);
            for (int r : conf) nosplit[(size_t)r] = 1;
        }
        if (settled && bs_ && !St.truns.empty()) colour_split(St, nadjt, Bt);
    }

    Cand *pick = &A;
    if (B.have) {
        bool better = B.warps > A.warps ||
                      (B.warps == A.warps && B.cycles <= A.cycles);

        if ((tmode & RN_REGS) && !I::early_cycles())
            better = B.warps > A.warps || (B.warps == A.warps && B.maxcol <= A.maxcol);
        if (better) pick = &B;
    }

    const bool tpick = Bt.have && Bt.warps > pick->warps;
    if (tpick) pick = &Bt;
    st.rp_tuple = tpick ? 1 : 0;

    if (tmode & RN_CHECK) {
        try {
            rename_check(p, c, reach, exit_live, pick->words);
        } catch (const std::exception &e) {

            throw;
        }
    }

    bc.swap(pick->bc);
    ct.swap(pick->ct);

    st.new_decl = (int)pick->decl;
}
template void renumber<Sm50>(std::vector<u8> &, std::vector<u8> &, bool, bool, RegStats &,
                             int);
template void renumber<Sm86>(std::vector<u8> &, std::vector<u8> &, bool, bool, RegStats &,
                             int);

static u64 sph_get(const u8 *s, int hi, int lo) {
    int width = hi - lo + 1;
    u64 v = 0;
    int b0 = lo >> 3;
    for (int k = 0; k < 8; k++) {
        int by = b0 + k;
        if (by < SPH_SIZE) v |= (u64)s[by] << (8 * k);
    }
    v >>= (lo & 7);
    if (width < 64) v &= (((u64)1 << width) - 1);
    return v;
}
static void sph_set(u8 *s, int hi, int lo, u64 val) {
    int width = hi - lo + 1;
    if (width < 64 && val >= ((u64)1 << width))
        fail("value %llu does not fit in SPH bits %d:%d",
             (unsigned long long)val, hi, lo);
    int b0 = lo >> 3;
    u64 cur = 0;
    for (int k = 0; k < 8; k++) {
        int by = b0 + k;
        if (by < SPH_SIZE) cur |= (u64)s[by] << (8 * k);
    }
    u64 m = (width < 64) ? ((((u64)1 << width) - 1) << (lo & 7)) : ~(u64)0;
    cur = (cur & ~m) | ((val << (lo & 7)) & m);
    for (int k = 0; k < 8; k++) {
        int by = b0 + k;
        if (by < SPH_SIZE) s[by] = (u8)((cur >> (8 * k)) & 0xFF);
    }
}

void exit_live_regs(const std::vector<u8> &bc, std::vector<int> &out) {
    out.clear();
    if (bc.size() < (size_t)(SPH_OFF + SPH_SIZE)) return;
    const u8 *sph = bc.data() + SPH_OFF;
    if (sph_get(sph, SPH_BITS_TYPE) != 2) return;
    int reg = 0;
    for (int i = 0; i < 8; i++) {
        u64 m = sph_get(sph, SPH_BITS_OMAP_TARGET(i));
        for (int c = 0; c < 4; c++)
            if (m & ((u64)1 << c)) out.push_back(reg++);
    }
}

const OpSet &Sm50::dce_ops() {
    static OpSet allow;
    static bool init = false;
    if (!init) {
        init = true;
        allow = make_opset({
            "Mov", "Mov32i", "Sel", "Rro", "Mufu", "Ipa", "S2r", "Cs2r",
            "Fadd", "Fadd32i", "Ffma", "Fmul", "Fmul32i", "Fmnmx", "Fcmp",
            "Iadd", "Iadd3", "Iadd32i", "Imnmx", "Icmp", "Iscadd",
            "Lop", "Lop3", "Lop32i", "Shl", "Shr", "Shf", "Bfe", "Bfi",
            "Xmad", "Imad", "Flo", "Popc", "Prmt",
            "F2f", "F2i", "I2f", "I2i"});
    }
    return allow;
}

template <class I>
static bool dce2_deletable_op(const ProgramT<I> &p, int i) {
    const OpSets &T = I::sets();
    const OpSet &allow = I::dce_ops();
    int nm = p.op[i];
    if (nm < 0 || !allow[(size_t)nm]) return false;
    if (T.side_effect[(size_t)nm] || T.branchy[(size_t)nm] ||
        T.pushy[(size_t)nm] || T.tex_bases[(size_t)nm] ||
        T.load_or_store[(size_t)nm]) return false;

    std::vector<int> v;
    auto all = p.defs[i];
    all.unite(p.maydefs[i]);
    all.list(v);
    bool any = false;
    for (int r : v) {
        if (!is_gpr_key(r)) return false;
        any = true;
    }
    return any;
}

template <class I>
static bool dce2_self_copy(const ProgramT<I> &p, int i) {
    int rd, rs;
    if (!I::reg_move(p.q[i], p.op[i], &rd, &rs)) return false;
    if (p.guarded(i)) return false;
    return rd != RZ && rd == rs;
}

bool Sm50::reads_cc(const ProgramT<Sm50> &p) {
    const OpSets &T = S();
    for (int i = 0; i < p.n; i++) {
        u64 q = p.q[i];
        if (!q) continue;
        int nm = p.op[i];
        if ((nm == T.O_Iadd || nm == T.O_Isetp || nm == T.O_Iadd3) &&
            ((q >> 43) & 1)) return true;
        if (nm == T.O_Iadd32i && ((q >> 53) & 1)) return true;
    }
    return false;
}
template <class I>
static bool dce2_reads_cc(const ProgramT<I> &p) { return I::reads_cc(p); }

template <class I>
static u32 stream_rebuild(const ProgramT<I> &p, const std::vector<u8> &bc, u32 co,
                          std::vector<typename I::Word> &out, std::vector<int> &oldof,
                          const std::vector<int> &newpos, int nreal, const char *who,
                          bool run_phase_b, std::vector<u8> &obc,
                          std::vector<u8> &ct) {
    const OpSets &T = I::sets();
    I::pad(out, oldof);
    for (size_t k = 0; k < oldof.size(); k++) {
        int i2 = oldof[k];
        if (i2 < 0 || i2 >= p.n || I::empty(p.q[i2])) continue;
        if (!T.branchy_imm[(size_t)p.op[i2]]) continue;
        int t = p.target(i2);
        if (t < 0 || t > nreal) fail("%s: unresolved branch at slot %d", who, i2);
        if (!I::set_branch(out[k], (int)k, newpos[(size_t)t]))
            fail("%s: branch displacement out of range", who);
    }
    I::fix_calls(out);
    u32 co2 = I::assemble(bc, co, out, obc, ct);
    if (run_phase_b) I::phase_b(obc, co2);
    I::layout_check(co2, who);
    return co2;
}

template <class I>
static void dce2_liveout(const ProgramT<I> &p, const CFGraph &c,
                         const std::vector<char> &reach,
                         const std::vector<char> &killed,
                         const std::vector<int> &exit_live,
                         std::vector<Mask> &lout) {
    int n = p.n;
    Mask seed;
    for (int r : exit_live) seed.set(r);
    std::vector<Mask> lin((size_t)n), dm((size_t)n), um((size_t)n);
    std::vector<int> order;
    for (int i = 0; i < n; i++) if (reach[(size_t)i]) order.push_back(i);
    for (int i : order) {
        if (killed[(size_t)i]) continue;
        std::vector<int> v;
        p.defs[i].list(v);
        for (int r : v) if (is_gpr_key(r)) dm[(size_t)i].set(r);
        int spur = I::spurious_pred(p.op[i], p.q[i]);
        p.uses[i].list(v);
        for (int r : v) if (is_gpr_key(r) && r != spur) um[(size_t)i].set(r);
    }
    std::vector<int> rorder(order.rbegin(), order.rend());
    bool conv = false;
    Mask lo, li;
    for (int round = 0; round < 4096; round++) {
        bool ch = false;
        for (int i : rorder) {
            lo.clear();
            if (c.succ[(size_t)i].empty()) lo = seed;
            else
                for (int t : c.succ[(size_t)i])
                    if (reach[(size_t)t]) lo |= lin[(size_t)t];
            if (c.cat[(size_t)i] == C_EXIT) lo |= seed;
            li = lo;
            li.andnot_or(dm[(size_t)i], um[(size_t)i]);
            if (li != lin[(size_t)i]) { lin[(size_t)i] = li; ch = true; }
        }
        if (!ch) { conv = true; break; }
    }
    if (!conv) fail("dce2: liveness did not converge");
    lout.assign((size_t)n, Mask());
    for (int i : order) {
        Mask lo2;
        if (c.succ[(size_t)i].empty()) lo2 = seed;
        else
            for (int t : c.succ[(size_t)i])
                if (reach[(size_t)t]) lo2 |= lin[(size_t)t];
        if (c.cat[(size_t)i] == C_EXIT) lo2 |= seed;
        lout[(size_t)i] = lo2;
    }
}

template <class I>
static bool dce2_kill_valid(const ProgramT<I> &p, const CFGraph &c,
                            const std::vector<char> &reach,
                            const std::vector<char> &kill,
                            const std::vector<char> &ghost,
                            const std::vector<int> &exit_live) {
    std::vector<Mask> lout;
    dce2_liveout(p, c, reach, ghost, exit_live, lout);
    std::vector<int> v;
    for (int i = 0; i < p.n; i++) {
        if (!kill[(size_t)i] || !reach[(size_t)i]) continue;

        if (dce2_self_copy(p, i)) continue;
        auto all = p.defs[i];
        all.unite(p.maydefs[i]);
        all.list(v);
        for (int r : v)
            if (is_gpr_key(r) && lout[(size_t)i].test(r)) return false;
    }
    return true;
}

template <class I>
void dce2(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment) {
    typedef typename I::Word Word;
    u32 co = I::const_off(ct);
    if (co > bc.size()) fail("dce2: ConstBufOffset past the file");
    int n = I::nslots(co);
    if (n <= 0) return;

    ProgramT<I> p;
    p.load_bytes(bc, ct);
    if (dce2_reads_cc(p)) return;
    CFGraph c;
    c.build(p, false);
    std::vector<char> reach = c.reachable_from_entry();
    std::vector<int> exit_live;
    if (fragment) I::exit_live_regs(bc, exit_live);

    std::vector<char> killed((size_t)p.n, 0);
    std::vector<Mask> lout;
    int dead = 0, self = 0;
    for (int r = 0; r < 16; r++) {
        dce2_liveout(p, c, reach, killed, exit_live, lout);
        bool ch = false;
        for (int i = 0; i < p.n; i++) {
            if (!reach[(size_t)i] || killed[(size_t)i] || I::empty(p.q[i])) continue;
            if (dce2_self_copy(p, i)) {
                killed[(size_t)i] = 1; self++; ch = true; continue;
            }
            if (!dce2_deletable_op(p, i)) continue;
            auto all = p.defs[i];
            all.unite(p.maydefs[i]);
            std::vector<int> v;
            all.list(v);
            bool live = false;
            for (int rg : v)
                if (is_gpr_key(rg) && lout[(size_t)i].test(rg)) { live = true; break; }
            if (live) continue;
            killed[(size_t)i] = 1; dead++; ch = true;
        }
        if (!ch) break;
    }
    if (!dead && !self) return;

    int nreal = 0;
    std::vector<Word> words((size_t)n);
    for (int k = 0; k < n; k++) {
        words[(size_t)k] = I::read_word(bc, k);
        if (!I::empty(words[(size_t)k])) nreal = k + 1;
    }

    auto build = [&](const std::vector<char> &kill, std::vector<u8> &obc,
                     std::vector<u8> &oct, u32 *oco) -> bool {
        std::vector<int> newidx((size_t)nreal + 1, -1),
                         nextkept((size_t)nreal + 1, -1);
        std::vector<Word> out;
        std::vector<int> oldof;
        for (int k = 0; k < nreal; k++) {
            if (k < p.n && kill[(size_t)k]) continue;
            newidx[(size_t)k] = (int)out.size();
            out.push_back(words[(size_t)k]);
            oldof.push_back(k);
        }
        if (out.empty()) fail("dce2: nothing left");
        { int nk = (int)out.size();
          for (int k = nreal; k >= 0; k--) {
              if (k < nreal && newidx[(size_t)k] >= 0) nk = newidx[(size_t)k];
              nextkept[(size_t)k] = nk;
          } }
        oct = ct;
        *oco = stream_rebuild(p, bc, co, out, oldof, nextkept, nreal, "dce2",
                              true, obc, oct);
        return true;
    };

    std::vector<char> kill_trunc = killed;
    std::vector<char> ghost = killed;
    int extra = (dead + self) % I::kPad, trimmed = 0;
    if (extra) {
        std::vector<int> kills;
        for (int i = 0; i < p.n; i++) if (killed[(size_t)i]) kills.push_back(i);
        std::vector<typename I::RSet> kdef((size_t)kills.size());
        for (size_t k = 0; k < kills.size(); k++) {
            kdef[k] = p.defs[kills[k]];
            kdef[k].unite(p.maydefs[kills[k]]);
        }
        std::vector<int> uv;
        for (int ki = (int)kills.size() - 1; ki >= 0 && trimmed < extra; ki--) {
            int i = kills[(size_t)ki];
            if (!dce2_self_copy(p, i)) {
                p.uses[i].list(uv);
                bool fed = false;
                for (size_t k = 0; k < kills.size() && !fed; k++) {
                    if ((int)k == ki) continue;
                    for (int r : uv) if (kdef[k].has(r)) { fed = true; break; }
                }

                if (fed) continue;
                ghost[(size_t)i] = 0;
            }
            kill_trunc[(size_t)i] = 0; trimmed++;
        }
        if (trimmed != extra) {
            kill_trunc = killed; ghost = killed; trimmed = 0;
        }
    }

    int before = I::issue_cycles(bc, co);
    std::vector<u8> bcA, ctA, bcB, ctB;
    u32 coA = 0, coB = 0;
    build(killed, bcA, ctA, &coA);
    int cycA = I::issue_cycles(bcA, coA);
    int cycB = cycA;
    bool useB = false;
    if (trimmed &&
        !dce2_kill_valid(p, c, reach, kill_trunc, ghost, exit_live)) {

        trimmed = 0;
    }
    if (trimmed) {
        build(kill_trunc, bcB, ctB, &coB);
        cycB = I::issue_cycles(bcB, coB);
        if (cycB < cycA) useB = true;
    }
    int after = useB ? cycB : cycA;

    if (after > before) {
        return;
    }

    if (useB) { bc.swap(bcB); ct.swap(ctB); }
    else { bc.swap(bcA); ct.swap(ctA); }
}
template void dce2<Sm50>(std::vector<u8> &, std::vector<u8> &, bool);
template void dce2<Sm86>(std::vector<u8> &, std::vector<u8> &, bool);

bool g_texnarrow = false;

static const int TN_LUT[2][8] = {
    {0x1, 0x2, 0x4, 0x8, 0x3, 0x9, 0xA, 0xC},
    {0x7, 0xB, 0xD, 0xE, 0xF, 0x0, 0x0, 0x0}};

static int tn_pc(int m) { int c = 0; while (m) { c += m & 1; m >>= 1; } return c; }

static int tn_prefix(int m, int n) {
    int r = 0;
    for (int b = 0; b < 4 && n; b++) if (m & (1 << b)) { r |= 1 << b; n--; }
    return r;
}

bool Sm50::tex_mask(u64 q, int nm, TnShape &s) {
    const OpSets &T = S();
    if (nm < 0) return false;
    const char *nv = op_name(nm);
    if (T.texs_fam[(size_t)nm]) {
        if (std::strcmp(nv, "Texs") && std::strcmp(nv, "Tlds")) return false;
        int dest = (int)(q & 0xFF), dest2 = (int)((q >> 28) & 0xFF);
        int ch = TN_LUT[dest2 == RZ ? 0 : 1][(q >> 50) & 7];
        if (!ch || dest == RZ) return false;
        s.form = 1; s.ch = ch; s.n = tn_pc(ch);
        for (int k = 0; k < s.n; k++) {
            int rd = (k >> 1) ? dest2 : dest;
            s.reg[k] = (rd < RZ) ? rd + (k & 1) : RZ;
        }
        return true;
    }
    if (T.tex_fam[(size_t)nm]) {
        static const char *const ok[] = {"Tex", "TexB", "Tld", "TldB",
                                         "Tld4", "Tld4B", "Txd", "TxdB"};
        bool good = false;
        for (const char *o : ok) if (!std::strcmp(nv, o)) { good = true; break; }
        if (!good) return false;
        int dest = (int)(q & 0xFF), ch = (int)((q >> 31) & 0xF);
        if (!ch || dest == RZ) return false;
        s.form = 0; s.ch = ch; s.n = tn_pc(ch);
        for (int k = 0; k < s.n; k++)
            s.reg[k] = (dest + k < RZ) ? dest + k : RZ;
        return true;
    }
    return false;
}

bool Sm50::tex_mask_narrow(const TnShape &s, int keep, u64 &q) {
    int nch = tn_prefix(s.ch, keep);
    if (!nch) return false;
    if (s.form == 0) {
        q = (q & ~(0xFull << 31)) | ((u64)(unsigned)nch << 31);
        return true;
    }

    int row = keep > 2 ? 1 : 0;
    for (int wm = 0; wm < 8; wm++) {
        if (TN_LUT[row][wm] != nch) continue;
        q = (q & ~(7ull << 50)) | ((u64)(unsigned)wm << 50);
        if (row == 0) q = (q & ~(0xFFull << 28)) | (0xFFull << 28);
        return true;
    }
    return false;
}

template <class I>
void texnarrow(std::vector<u8> &bc, const std::vector<u8> &ct, bool fragment,
               TexNarrowStats &st) {
    u32 co = I::const_off(ct);
    if (co > bc.size()) fail("texnarrow: ConstBufOffset past the file");
    if (I::nslots(co) <= 0) return;

    ProgramT<I> p;
    p.load_bytes(bc, ct);
    CFGraph c;
    c.build(p, false);
    std::vector<char> reach = c.reachable_from_entry();
    std::vector<int> exit_live;
    if (fragment) I::exit_live_regs(bc, exit_live);

    std::vector<char> ghost((size_t)p.n, 0);
    if (!dce2_reads_cc(p)) {
        std::vector<Mask> gl;
        for (int rnd = 0; rnd < 16; rnd++) {
            dce2_liveout(p, c, reach, ghost, exit_live, gl);
            bool ch = false;
            for (int i = 0; i < p.n; i++) {
                if (!reach[(size_t)i] || ghost[(size_t)i] || I::empty(p.q[i])) continue;
                if (dce2_self_copy(p, i)) {
                    ghost[(size_t)i] = 1; ch = true; continue;
                }
                if (!dce2_deletable_op(p, i)) continue;
                typename I::RSet all = p.defs[i]; all.unite(p.maydefs[i]);
                std::vector<int> v; all.list(v);
                bool live = false;
                for (int rg : v)
                    if (rg < RZ && gl[(size_t)i].test(rg)) { live = true; break; }
                if (live) continue;
                ghost[(size_t)i] = 1; ch = true;
            }
            if (!ch) break;
        }
        if (!dce2_kill_valid(p, c, reach, ghost, ghost, exit_live)) {

            std::fill(ghost.begin(), ghost.end(), (char)0);
            for (int i = 0; i < p.n; i++)
                if (reach[(size_t)i] && !I::empty(p.q[i]) && dce2_self_copy(p, i)) {
                    ghost[(size_t)i] = 1;
                }
        }
    }
    std::vector<Mask> lout;
    dce2_liveout(p, c, reach, ghost, exit_live, lout);

    for (int i = 0; i < p.n; i++) {
        if (!reach[(size_t)i] || I::empty(p.q[i])) continue;
        TnShape s;
        if (!I::tex_mask(p.q[i], p.op[i], s)) {

            const OpSets &T = I::sets();
            if (T.tex_bases[(size_t)p.op[i]]) {
                typename I::RSet all = p.defs[i]; all.unite(p.maydefs[i]);
                std::vector<int> v; all.list(v);
                for (int r : v)
                    if (r < RZ && !lout[(size_t)i].test(r)) break;
            }
            continue;
        }
        int keep = s.n;
        while (keep > 0) {
            int r = s.reg[keep - 1];

            if (r != RZ && lout[(size_t)i].test(r)) break;
            keep--;
        }
        if (keep == s.n) continue;
        if (keep == 0) continue;
        typename I::Word q = p.q[i];
        if (!I::tex_mask_narrow(s, keep, q)) continue;
        I::write_word(bc, i, q);
        st.narrowed++;
    }
    if (!st.narrowed) return;

    for (int i = 0; i < p.n; i++) {
        if (!ghost[(size_t)i]) continue;
        I::write_word(bc, i, I::nop());
    }
}
template void texnarrow<Sm50>(std::vector<u8> &, const std::vector<u8> &, bool,
                              TexNarrowStats &);
template void texnarrow<Sm86>(std::vector<u8> &, const std::vector<u8> &, bool,
                              TexNarrowStats &);

static int max_sync_nesting(const Program &p) {
    const OpSets &T = S();
    int d = 0, mx = 0;
    for (int i = 0; i < p.n; i++) {
        int nm = p.op[i];
        if (nm == T.O_Ssy || nm == T.O_Pbk || nm == T.O_Pcnt) {
            d++;
            if (d > mx) mx = d;
        } else if (nm == T.O_Sync || nm == T.O_Brk || nm == T.O_Cont) {
            d = std::max(0, d - 1);
        }
    }
    return mx;
}

static void real_gprs(const Program &p, int i, std::vector<int> &out) {
    RSet s = p.defs[i];
    s.unite(p.maydefs[i]);
    s.unite(p.uses[i]);
    s.list(out);
    if (p.op[i] == S().O_Shfl) {
        u64 q = p.q[i];
        std::vector<int> keep;
        int drop1 = ((q >> 28) & 1) ? (int)((q >> 20) & 0xFF) : -1;
        int drop2 = ((q >> 29) & 1) ? (int)((q >> 39) & 0xFF) : -1;
        for (int r : out) if (r != drop1 && r != drop2) keep.push_back(r);
        out.swap(keep);
    }
}

bool bytecode_is_fragment(const std::vector<u8> &bc, const char *what) {
    if (bc.size() < (size_t)SPH_OFF + (size_t)SPH_SIZE)
        fail("%s: %zu bytes is too short to hold a shader program header",
             what, bc.size());
    u32 magic;
    std::memcpy(&magic, bc.data(), 4);
    if (magic != NVN_PROGRAM_MAGIC)
        fail("%s: bad program magic %08x (expected %08x) -- this is not an "
             "NVN `_bytecode.bin`", what, magic, NVN_PROGRAM_MAGIC);
    u64 t = sph_get(bc.data() + SPH_OFF, SPH_BITS_TYPE);
    if (t == NvSphType_PS) return true;
    if (t == NvSphType_VTG) return false;
    fail("%s: sph_type %llu is neither NvSphType_PS (%d) nor NvSphType_VTG "
         "(%d); this tool has no pipeline for it", what,
         (unsigned long long)t, (int)NvSphType_PS, (int)NvSphType_VTG);
    return false;
}

static void analyse(const Program &p, CtlFacts &f) {
    const OpSets &T = S();
    const u8 *sph = p.bc.data() + SPH_OFF;
    f.fragment = (sph_get(sph, SPH_BITS_TYPE) == 2);
    std::memset(f.imap_gen_read, 0, sizeof f.imap_gen_read);
    f.imap_sys_read = 0;
    f.imap_indexed = false;

    int max_gpr = -1, n_real = 0;
    bool kills = false, dls = false, dgs = false, fp64 = false;
    int local_max_byte = 0, local_count = 0;
    bool local_indexed = false;
    std::vector<int> tex_order;
    int bindless = 0, back_edges = 0;
    long long rate = 0;
    int n_ipa = 0, ipa_addrs = 0;
    u64 ipa_seen[16] = {0};
    std::vector<int> regs;

    for (int i = 0; i < p.n; i++) {
        int nm = p.op[i];
        if (nm == T.O_Invalid) continue;
        n_real++;
        real_gprs(p, i, regs);
        for (int r : regs) if (r < 255 && r > max_gpr) max_gpr = r;
        if (nm == T.O_Kil) kills = true;

        if (T.ctl_texs_fam[(size_t)nm] || T.ctl_tex_fam[(size_t)nm] ||
            T.ctl_tex_bindless[(size_t)nm]) rate += 16;
        else if (T.load_or_store[(size_t)nm]) rate += 8;
        else if (T.rate_quarter[(size_t)nm]) rate += 4;
        else if (T.rate_half[(size_t)nm]) rate += 2;
        else if (nm != T.O_Nop) rate += 1;
        if (nm == T.O_Ipa) {
            n_ipa++;
            int aa = (int)((p.q[i] >> 28) & 0x3FF);
            if (!((ipa_seen[aa >> 6] >> (aa & 63)) & 1)) {
                ipa_seen[aa >> 6] |= (u64)1 << (aa & 63);
                ipa_addrs++;
            }

            u64 q = p.q[i];
            int a = (int)((q >> 28) & 0x3FF);
            if (((q >> 8) & 0xFF) != (u64)RZ) f.imap_indexed = true;
            else if (a < IMAP_GENERIC_BASE) f.imap_sys_read |= (u32)1 << (a >> 2);
            else if (a < IMAP_GENERIC_BASE + 32 * 16)
                f.imap_gen_read[(size_t)((a - IMAP_GENERIC_BASE) >> 4)] |=
                    (u8)(1 << ((a & 15) >> 2));
            else f.imap_indexed = true;
        }
        if (T.load_or_store[(size_t)nm]) dls = true;
        if (T.global_store[(size_t)nm]) dgs = true;
        if (T.fp64[(size_t)nm]) fp64 = true;
        if (T.local_ops[(size_t)nm]) {
            u64 q = p.q[i];
            local_count++;
            if (((q >> 8) & 0xFF) != (u64)RZ) local_indexed = true;
            int32_t off = lmem_off(q);
            int width = mem_data_regs(q, nm) * 4;
            if (off < 0) local_indexed = true;
            else if (off + width > local_max_byte) local_max_byte = off + width;
        }
        if (T.ctl_texs_fam[(size_t)nm] || T.ctl_tex_fam[(size_t)nm]) {
            int h = tex_handle(p.q[i]);
            int slot = h / 2 - 4;
            if (std::find(tex_order.begin(), tex_order.end(), slot) == tex_order.end())
                tex_order.push_back(slot);
        } else if (T.ctl_tex_bindless[(size_t)nm]) bindless++;
        if (nm == T.O_Bra || nm == T.O_Jmp) {
            int t = p.target(i);
            if (t >= 0 && t < i) back_edges++;
        }
    }

    int src_low = (int)sph_get(sph, SPH_BITS_LOCAL_MEM_LO_SZ);
    int slm_low;
    if (local_count == 0) slm_low = 0;
    else if (local_indexed) slm_low = src_low;
    else slm_low = (local_max_byte + 15) & ~15;

    int msn = max_sync_nesting(p);
    int depth = back_edges ? (32 + msn) : msn;
    int slm_crs = (depth <= 16) ? 0 : ((depth * 16 + 512 + 511) & ~511);

    f.n_real = n_real;
    f.rate_weight = rate;
    f.ipa_redundant = n_ipa - ipa_addrs;
    f.gpr_count = max_gpr + 1;
    f.slm_low = slm_low;
    f.slm_high = 0;
    f.slm_crs = slm_crs;
    f.lmem_bytes = (u32)(32 * (slm_low + 0) + slm_crs);
    f.does_load_or_store = dls ? 1 : 0;
    f.does_global_store = dgs ? 1 : 0;
    f.does_fp64 = fp64 ? 1 : 0;
    f.kills_pixels = kills ? 1 : 0;
    f.tex_slots = tex_order;
    f.tex_bindless = bindless;
    f.ncolor_outputs = 0;
    if (f.fragment) {
        int n = 0;
        for (int i = 0; i < 8; i++)
            if (sph_get(sph, SPH_BITS_OMAP_TARGET(i))) n = i + 1;
        f.ncolor_outputs = n;
    }
}

void control_facts(const std::vector<u8> &bc, const std::vector<u8> &ct,
                   CtlFacts &f) {
    Program p;
    p.load_bytes(bc, ct);
    analyse(p, f);
}

static void imap_trim(u8 *sph, CtlFacts &f) {
    u8 *gv = sph + SPH_IMAP_GENERIC_OFF;
    u32 sv;
    std::memcpy(&sv, sph + SPH_IMAP_SYSVALS_OFF, 4);
    for (int loc = 0; loc < 32; loc++) {
        u8 keep = 0;
        for (int c = 0; c < 4; c++) {
            if ((f.imap_gen_read[(size_t)loc] >> c) & 1) keep |= (u8)(3 << (2 * c));
        }
        if (!f.imap_indexed) gv[loc] &= keep;
    }

    if (!f.imap_indexed) sv &= f.imap_sys_read | ((u32)1 << NvSysval_PositionW);
    std::memcpy(sph + SPH_IMAP_SYSVALS_OFF, &sv, 4);
}

void control_rewrite(std::vector<u8> &bc, std::vector<u8> &ct, CtlFacts &f) {
    Program p;
    p.load_bytes(bc, ct);
    analyse(p, f);

    u8 sph[SPH_SIZE];
    std::memcpy(sph, bc.data() + SPH_OFF, SPH_SIZE);
    if (f.fragment) sph_set(sph, SPH_BITS_KILLS_PIXELS, (u64)f.kills_pixels);
    sph_set(sph, SPH_BITS_DOES_GLOBAL_STORE, (u64)f.does_global_store);
    sph_set(sph, SPH_BITS_DOES_LOAD_OR_STORE, (u64)f.does_load_or_store);
    sph_set(sph, SPH_BITS_DOES_FP64, (u64)f.does_fp64);
    sph_set(sph, SPH_BITS_LOCAL_MEM_LO_SZ, (u64)f.slm_low);
    sph_set(sph, SPH_BITS_LOCAL_MEM_HI_SZ, (u64)f.slm_high);
    sph_set(sph, SPH_BITS_LOCAL_MEM_CRS_SZ, (u64)f.slm_crs);
    if (f.fragment) imap_trim(sph, f);

    NVNshaderControl *c = ctl(ct);
    c->debugBuildId[0] = UBERSPEC_STAMP_MAGIC;
    c->debugBuildId[1] = UBERSPEC_CODEGEN_VER;
    c->debugBuildId[2] = 0;
    c->debugBuildId[3] = 0;
    c->mProgramRegNum = (u32)f.gpr_count;
    c->mPerWarpScratchSize = f.lmem_bytes;
    if (f.fragment) c->numColourResults = (u32)f.ncolor_outputs;

    int old_n = c->numSamplerRefs;
    std::vector<int> src_order;
    for (int k = 0; k < old_n; k++)
        src_order.push_back(c->samplerUnitBindings[k]);
    std::vector<int> new_slots;
    if (f.tex_bindless) new_slots = src_order;
    else {
        std::set<int> used(f.tex_slots.begin(), f.tex_slots.end());
        for (int x : src_order) if (used.count(x)) new_slots.push_back(x);
        for (int x : f.tex_slots)
            if (std::find(src_order.begin(), src_order.end(), x) == src_order.end())
                new_slots.push_back(x);
    }
    if ((int)new_slots.size() > NVN_NUM_TEX_UNITS)
        fail("%zu sampler refs exceeds __NVN_NUM_TEX_UNITS", new_slots.size());
    c->numSamplerRefs = (u8)new_slots.size();
    for (int k = 0; k < NVN_NUM_TEX_UNITS; k++)
        c->samplerUnitBindings[k] =
            (u8)(k < (int)new_slots.size() ? new_slots[(size_t)k] : 0);

    std::memcpy(bc.data() + SPH_OFF, sph, SPH_SIZE);
}

void tex_samplers(const std::vector<u8> &bc, const std::vector<u8> &ct,
                  std::vector<int> &out) {
    const OpSets &T = S();
    Program p;
    p.load_bytes(bc, ct);
    std::set<int> s;
    for (int i = 0; i < p.n; i++) {
        if (!p.q[i]) continue;
        if (!T.tex_ops_audit[(size_t)p.op[i]]) continue;
        s.insert(tex_handle(p.q[i]));
    }
    out.assign(s.begin(), s.end());
}

void verify(const std::vector<u8> &bc, const std::vector<u8> &ct, bool run_v8,
            GateResult &R, const std::vector<u8> *shipped_bc,
            const std::vector<u8> *shipped_ct, const std::vector<u8> *ref_bc,
            const std::vector<u8> *ref_ct) {
    const OpSets &T = S();
    char buf[512];
    u32 co = const_off(ct);
    u32 magic; std::memcpy(&magic, bc.data(), 4);
    u32 ctmagic; std::memcpy(&ctmagic, ct.data(), 4);
    bool aligned = (co % CBUF_ALIGN == 0) && co > INSTR_START;
    int slots = 3 * ((int)co - INSTR_START) / 32;
    bool v1 = (magic == NVN_PROGRAM_MAGIC) && (ctmagic == NVN_CONTROL_MAGIC) &&
              aligned &&
              ct.size() == sizeof(NVNshaderControl) && slots_ok(slots);
    snprintf(buf, sizeof buf, "co=%#x slots=%d (mod24=%d) ctrl=%dB", co, slots,
             slots % 24, (int)ct.size());
    R.add("V1 layout", v1, buf);

    size_t blobsz = bc.size() - co;
    long last = -1;
    for (u32 off = INSTR_START; off + 8 <= co; off += 8) {
        if ((off - INSTR_START) % 32 == 0) continue;
        u64 w; std::memcpy(&w, bc.data() + off, 8);
        if (w) last = (long)off;
    }
    long nb = (last >= 0) ? ((last - INSTR_START) / 32 + 1) : 0;
    const NVNshaderControl *ctlp = ctl(ct);
    bool v2 = (ctlp->mShaderSize == bc.size()) &&
              (ctlp->mProgramSize == (u32)(SPH_SIZE + nb * 32)) &&
              (ctlp->mConstBufSize <= blobsz) &&
              (blobsz % CBUF_ALIGN == 0);
    snprintf(buf, sizeof buf,
             "ShaderSize=%#x(exp %#lx) total=%#x(exp %#zx) ConstBufSize=%#x blob=%#zx",
             ctlp->mProgramSize, SPH_SIZE + nb * 32,
             ctlp->mShaderSize, bc.size(),
             ctlp->mConstBufSize, blobsz);
    R.add("V2 control", v2, buf);

    Program p;
    p.load_bytes(bc, ct);
    bool v3 = ((int)p.n == slots);
    snprintf(buf, sizeof buf, "%d instruction slots", p.n);
    R.add("V3 roundtrip", v3, buf);

    std::vector<int> real;
    for (int i = 0; i < p.n; i++) if (p.q[i]) real.push_back(i);
    int ninv = 0;
    for (int i : real) if (p.op[i] == T.O_Invalid) ninv++;
    snprintf(buf, sizeof buf, "%zu real instrs, %d Invalid", real.size(), ninv);
    R.add("V4 decode", ninv == 0, buf);

    int nbrx = 0;
    for (int i : real) if (p.op[i] == T.O_Brx || p.op[i] == T.O_Jmx) nbrx++;
    snprintf(buf, sizeof buf, "%d computed jumps", nbrx);
    R.add("V5 no BRX", nbrx == 0, buf);

    CFGraph c;
    c.build(p, false);
    std::vector<char> reach = c.reachable_from_entry();
    int hi = -1;
    for (int i = 0; i < p.n; i++) if (reach[(size_t)i]) hi = i;
    int unreached = 0;
    for (int i : real) if (!reach[(size_t)i] && i < hi) unreached++;
    int badtgt = 0;
    for (int i : real) {
        if (!T.branchy_imm[(size_t)p.op[i]]) continue;
        int t = p.target(i);
        if (t < 0 || t >= p.n || !p.q[t]) badtgt++;
    }
    int noexit = 0, nreach = 0;
    for (int i = 0; i < p.n; i++) {
        if (!reach[(size_t)i]) continue;
        if (p.q[i]) nreach++;
        if (c.succ[(size_t)i].empty() && p.op[i] != T.O_Exit && p.op[i] != T.O_Ret)
            noexit++;
    }
    bool v6 = !unreached && !badtgt && !noexit && !c.overflow;
    snprintf(buf, sizeof buf,
             "reach=%d/%zu unreached=%d badtarget=%d dangling=%d overflow=%d",
             nreach, real.size(), unreached, badtgt, noexit, (int)c.overflow);
    R.add("V6 cfg", v6, buf);

    Mask ent;
    live_entry(p, c, reach, ent);
    std::vector<int> eb; ent.bits(eb);
    std::string egpr, epr;
    bool any = false;
    for (int r : eb) {
        if (r < PREG) { egpr += std::to_string(r) + " "; any = true; }
        else if (r < 512) { epr += std::to_string(r - PREG) + " "; any = true; }
    }
    snprintf(buf, sizeof buf, "entry live GPR=[%s] P=[%s]", egpr.c_str(), epr.c_str());
    R.add("V7 dataflow", !any, buf);

    if (run_v8) {
        std::vector<u8> tmp = bc;
        int a = uber_validate(tmp.data(), co);
        snprintf(buf, sizeof buf, "%d uncovered", a);
        R.add("V8 hazards", a == 0, buf);
    }

    u32 used = ctlp->mConstBufSize;
    int oob = 0;
    std::set<int> banks;
    for (int i : real) {
        u64 q = p.q[i];
        int nm = p.op[i], b, o;
        if (!cbuf_read_of(q, nm, &b, &o)) continue;
        if (nm == T.O_Ldc || T.alu_cbuf[(size_t)nm] || T.alu_cbuf_srcc[(size_t)nm])
            banks.insert(b);
        if (b == 1 && (u32)(o + 4) > used) oob++;
    }
    std::string bs;
    for (int b : banks) bs += std::to_string(b) + " ";

    if (shipped_bc && shipped_ct) {
        std::vector<int> ours, shipped, missing;
        tex_samplers(bc, ct, ours);
        tex_samplers(*shipped_bc, *shipped_ct, shipped);
        for (int h : shipped)
            if (std::find(ours.begin(), ours.end(), h) == ours.end())
                missing.push_back(h);
        std::string ms;
        for (int h : missing) ms += std::to_string(h) + " ";
        snprintf(buf, sizeof buf, "shipped %zu  ours %zu  missing [%s]",
                 shipped.size(), ours.size(), ms.c_str());
        R.add("V9 samplers", missing.empty(), buf);
    } else {
        R.add("V9 samplers", true,
              "NOT RUN -- no independently compiled program supplied");
    }

    snprintf(buf, sizeof buf,
             "banks read [%s] ConstBufSize=%#x  out-of-range bank-1 reads=%d",
             bs.c_str(), used, oob);
    R.add("V10 cbuf", oob == 0, buf);

    if (ref_bc && ref_ct) {
        std::string d;
        bool ok = gate_memorder(*ref_bc, *ref_ct, bc, ct, d);
        R.add("V11 memorder", ok, d);
    } else {
        R.add("V11 memorder", true,
              "NOT RUN -- no pre-reorder reference supplied");
    }

    {
        const u8 *sph = bc.data() + SPH_OFF;
        int slm_low = (int)sph_get(sph, SPH_BITS_LOCAL_MEM_LO_SZ);
        u32 decl = ctlp->mPerWarpScratchSize;
        int nlocal = 0, oob12 = 0, unbounded = 0, worst = 0;
        for (int i : real) {
            int nm = p.op[i];
            if (!T.local_ops[(size_t)nm]) continue;
            nlocal++;
            u64 q = p.q[i];
            if (((q >> 8) & 0xFF) != (u64)RZ) { unbounded++; continue; }
            int32_t off = lmem_off(q);
            int end = off + 4 * mem_data_regs(q, nm);
            if (off < 0 || end > slm_low) oob12++;
            if (end > worst) worst = end;
        }
        bool frame_ok = ((u32)(32 * slm_low) <= decl);

        bool v12 = (oob12 == 0) && frame_ok;
        snprintf(buf, sizeof buf,
                 "%d local op(s), highest byte %d, slm_low=%d, "
                 "mPerWarpScratchSize=%u; "
                 "outside=%d register-indexed=%d",
                 nlocal, worst, slm_low, decl, oob12, unbounded);
        R.add("V12 lmem frame", v12, buf);
    }

    {
        int nvote = 0, bad13 = 0, worstgot = 99, wantmax = 0;
        for (int i : real) {
            if (p.op[i] != T.O_Vote) continue;
            nvote++;
            int want = ub_vote_latency(p.q[i]);

            u32 rel = (u32)p.rel[i];
            u32 base = (u32)INSTR_START + (rel / 32) * 32;
            int slot = (int)((rel % 32) / 8) - 1;
            if (slot < 0 || slot > 2) { bad13++; continue; }
            u64 hdr = 0;
            if ((size_t)(base + 8) <= bc.size()) std::memcpy(&hdr, bc.data() + base, 8);
            int code = sched_wait_code(hdr, slot);
            int got = SCHED_WAIT_DEC[code];
            if (want > wantmax) wantmax = want;
            if (got < want) { bad13++; if (got < worstgot) worstgot = got; }
        }
        snprintf(buf, sizeof buf,
                 "%d VOTE(s), latency floor %d, %d below it%s%s",
                 nvote, wantmax, bad13,
                 bad13 ? (std::string(" (worst ") + std::to_string(worstgot) +
                          ")").c_str() : "",
                 uber_vote_floor_fail ? " (floor refused)" : "");
        R.add("V13 vote stall", bad13 == 0 && !uber_vote_floor_fail, buf);
    }

    {
        int ntex = 0, bad14 = 0, firstbad = -1;
        for (int i : real) {
            int nm = p.op[i];
            if (!T.tex_bases[(size_t)nm]) continue;
            ntex++;
            int nA = 0, nB = 0;
            tex_src_widths(p.q[i], nm, nA, nB);

            if (!T.texs_fam[(size_t)nm]) nB = 0;
            bool hit = (nA && (int)((p.q[i] >> 8) & 0xFF) == RZ) ||
                       (nB && (int)((p.q[i] >> 20) & 0xFF) == RZ);
            if (hit) { bad14++; if (firstbad < 0) firstbad = i; }
        }
        std::string where = bad14 ? (" (first at slot " +
                                     std::to_string(firstbad) + ")")
                                  : std::string();
        snprintf(buf, sizeof buf,
                 "%d texture op(s), %d with an RZ coordinate source%s",
                 ntex, bad14, where.c_str());
        R.add("V14 tex operands", bad14 == 0, buf);
    }

    {
        const u8 *sph = bc.data() + SPH_OFF;
        bool frag = sph_get(sph, SPH_BITS_TYPE) == NvSphType_PS;
        u32 sv;
        std::memcpy(&sv, sph + SPH_IMAP_SYSVALS_OFF, 4);
        int nipa = 0, undeclared = 0, indexed = 0, declared = 0;
        for (int i : real) {
            if (p.op[i] != T.O_Ipa) continue;
            nipa++;
            u64 q = p.q[i];
            int a = (int)((q >> 28) & 0x3FF);
            if (((q >> 8) & 0xFF) != (u64)RZ) { indexed++; continue; }
            bool ok = true;
            if (a < IMAP_GENERIC_BASE) ok = (sv >> (a >> 2)) & 1;
            else if (a < IMAP_GENERIC_BASE + 32 * 16)
                ok = (sph[SPH_IMAP_GENERIC_OFF + ((a - IMAP_GENERIC_BASE) >> 4)] >>
                      (2 * ((a & 15) >> 2))) & 3;
            if (!ok) undeclared++;
        }
        for (int loc = 0; loc < 32; loc++)
            for (int c = 0; c < 4; c++)
                if ((sph[SPH_IMAP_GENERIC_OFF + loc] >> (2 * c)) & 3) declared++;
        declared += __builtin_popcount(sv);

        bool posw = (sv >> NvSysval_PositionW) & 1;
        if (!frag) {
            R.add("V15 imap inputs", true, "NOT RUN -- not a pixel shader");
        } else {
            snprintf(buf, sizeof buf,
                     "%d IPA(s), %d declared component(s), %d read but undeclared, "
                     "%d register-indexed%s", nipa, declared, undeclared, indexed,
                     posw ? "" : ", PositionW undeclared");
            R.add("V15 imap inputs", undeclared == 0 && posw, buf);
        }
    }
}

bool g_anticopy = false;

long long g_ac_budget = -1;

extern "C" {
int ub_anticopy_probe(const unsigned char *bc, unsigned int constOff, int nreal,
                      int memdeps, const unsigned char *pdefs,
                      const unsigned char *puses, int *o_slot, int *o_reg,
                      int *o_bs, int *o_be, int *o_cnt, int maxo);
void ub_set_webs(const int *wuse, const int *wdef, int stride);
}

int Sm50::anticopy_sites(const Program &p, const std::vector<u8> &bc, u32 co, int n,
                         int nreal, const std::vector<int> &wuse,
                         const std::vector<int> &wdef, int *slot, int *reg, int *bs,
                         int *be, int *cnt) {
    std::vector<u8> pdefs, puses;
    pred_masks(p, n, pdefs, puses);
    ub_set_webs(wuse.data(), wdef.data(), WEB_STRIDE);
    int ns = ub_anticopy_probe(bc.data(), co, nreal, 1, pdefs.data(), puses.data(),
                               slot, reg, bs, be, cnt, n);
    ub_set_webs(nullptr, nullptr, 0);
    return ns;
}

template <class I>
void anticopy(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
              AnticopyStats &st) {
    typedef typename I::Word Word;
    u32 co = I::const_off(ct);
    if (co > bc.size()) fail("anticopy: ConstBufOffset past the file");
    int n = I::nslots(co);
    if (n <= 0) return;
    ProgramT<I> p;
    p.load_bytes(bc, ct);
    int nreal = 0;
    for (int k = 0; k < n && k < p.n; k++) if (!I::empty(p.q[k])) nreal = k + 1;
    if (nreal <= 0) return;

    std::vector<int> wuse, wdef;
    int wn = 0;
    if (!web_map<I>(bc, ct, fragment, wuse, wdef, wn) || wn != n) return;
    std::vector<int> o_slot((size_t)n), o_reg((size_t)n), o_bs((size_t)n),
                     o_be((size_t)n), o_cnt((size_t)n);
    int ns = I::anticopy_sites(p, bc, co, n, nreal, wuse, wdef, o_slot.data(),
                               o_reg.data(), o_bs.data(), o_be.data(), o_cnt.data());
    if (ns <= 0) return;

    CFGraph c;
    c.build(p, false);
    std::vector<char> reach = c.reachable_from_entry();
    std::vector<int> exit_live;
    if (fragment) I::exit_live_regs(bc, exit_live);
    Live L;
    liveness(p, c, reach, exit_live, L);
    std::set<int> pinset(exit_live.begin(), exit_live.end());

    std::vector<int> npred((size_t)p.n, 0), onepred((size_t)p.n, -1);
    for (int i = 0; i < p.n; i++) {
        if (!reach[(size_t)i]) continue;
        for (int t : c.succ[(size_t)i])
            if (t >= 0 && t < p.n) { npred[(size_t)t]++; onepred[(size_t)t] = i; }
    }
    std::vector<std::vector<Field>> fms((size_t)p.n);
    std::set<int> wide;
    for (int i = 0; i < p.n; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fms[(size_t)i]);
        for (const Field &f : fms[(size_t)i])
            if (f.w > 1)
                for (int k = 0; k < f.w; k++) wide.insert(f.base + k);
    }

    struct Site { int slot, cnt; };
    std::map<std::pair<int, int>, std::vector<Site>> groups;
    std::map<int, int> bend;
    for (int k = 0; k < ns; k++) {
        groups[std::make_pair(o_bs[(size_t)k], o_reg[(size_t)k])]
            .push_back({o_slot[(size_t)k], o_cnt[(size_t)k]});
        bend[o_bs[(size_t)k]] = o_be[(size_t)k];
    }

    struct Plan { int bs, lo, hi, reg, fresh, cnt; bool copy; };
    std::vector<Plan> plans;
    std::map<int, std::set<int>> taken;
    auto is_free = [&](int cand, int lo, int hi) {
        for (int i = lo; i <= hi; i++) {
            if (!reach[(size_t)i]) continue;
            if (L.live[(size_t)i].test(cand) || L.dmask[(size_t)i].test(cand) ||
                L.umask[(size_t)i].test(cand)) return false;
        }
        for (int sc : c.succ[(size_t)hi])
            if (sc >= 0 && sc < p.n && L.live[(size_t)sc].test(cand)) return false;
        return true;
    };
    for (auto &pr : groups) {
        int bs = pr.first.first, r = pr.first.second, be = bend[bs];
        std::vector<Site> &ss = pr.second;
        if (r < 0 || r >= RZ || bs < 0 || be > p.n || !reach[(size_t)bs]) {
            continue;
        }

        bool ok = true;
        for (int i = bs + 1; i < be && ok; i++) {
            if (I::empty(p.q[i])) continue;
            if (npred[(size_t)i] != 1 || onepred[(size_t)i] != i - 1) ok = false;
        }
        if (!ok) continue;

        std::vector<int> D;
        std::vector<char> widedef((size_t)p.n, 0), wideuse((size_t)p.n, 0);
        for (int i = bs; i < be; i++) {
            if (I::empty(p.q[i])) continue;
            for (const Field &f : fms[(size_t)i]) {
                bool hit = (r >= f.base && r < f.base + f.w);
                if (!hit) continue;
                if (f.w > 1) {
                    if (f.kind == 'd') widedef[(size_t)i] = 1; else wideuse[(size_t)i] = 1;
                }
                if (f.kind == 'd' && !p.guarded(i)) D.push_back(i);
            }
        }
        if (D.empty()) {
            continue;
        }
        int k = (int)D.size();

        auto narrow = [&](int lo, int hi, bool copy) {
            for (int i = lo; i <= hi; i++) {
                if (I::empty(p.q[i])) continue;
                if (i == lo && !copy) { if (widedef[(size_t)i]) return false; continue; }
                if (i == hi) { if (wideuse[(size_t)i]) return false; continue; }
                if (widedef[(size_t)i] || wideuse[(size_t)i]) return false;
            }
            return true;
        };

        std::map<int, int> want;
        for (const Site &sv : ss) {
            int j = -1;
            for (int q = 0; q < k; q++) if (D[(size_t)q] == sv.slot) { j = q + 1; break; }
            if (j < 0) continue;
            if (j == 1) want[k >= 2 ? 1 : 0] += sv.cnt;
            else want[j - 1] += sv.cnt;
        }
        for (auto &w : want) {
            int j = w.first, lo, hi;
            bool copy = (j == 0);
            if (copy) {
                if (!L.live[(size_t)bs].test(r)) continue;
                lo = bs; hi = D[0];
            } else {
                lo = D[(size_t)(j - 1)]; hi = D[(size_t)j];
            }
            if (!narrow(lo, hi, copy)) {
                continue;
            }
            std::set<int> &tk = taken[bs];
            int fresh = -1;
            for (int cand = 0; cand < RZ && fresh < 0; cand++) {
                if (pinset.count(cand) || wide.count(cand) || tk.count(cand)) continue;
                if (is_free(cand, lo, hi)) fresh = cand;
            }
            if (fresh < 0) continue;
            tk.insert(fresh);
            plans.push_back({bs, lo, hi, r, fresh, w.second, copy});
        }
    }
    if (plans.empty()) return;

    {
        std::vector<Plan> cp, loc;
        for (const Plan &pl : plans) (pl.copy ? cp : loc).push_back(pl);
        std::sort(cp.begin(), cp.end(),
                  [](const Plan &a, const Plan &b) { return a.cnt > b.cnt; });
        int cur_pad = (I::kPad - nreal % I::kPad) % I::kPad;
        size_t keep = cp.size();
        for (size_t kk = cp.size(); kk + 3 > cp.size() && kk > 0; kk--) {
            int pad = (I::kPad - (int)((nreal + (int)kk) % I::kPad)) % I::kPad;
            if (pad <= cur_pad) { keep = kk; break; }
        }
        if (cp.size() && keep == cp.size()) {
            int pad = (I::kPad - (int)((nreal + (int)keep) % I::kPad)) % I::kPad;
            if (pad > cur_pad && cp.size() <= 2) keep = 0;
        }
        cp.resize(keep);
        plans = loc;
        plans.insert(plans.end(), cp.begin(), cp.end());
    }
    if (plans.empty()) return;
    if (g_ac_budget >= 0) {

        std::stable_sort(plans.begin(), plans.end(),
                         [](const Plan &a, const Plan &b) {
                             if (a.copy != b.copy) return !a.copy;
                             return a.cnt > b.cnt;
                         });
        if ((long long)plans.size() > g_ac_budget) plans.resize((size_t)g_ac_budget);
        g_ac_budget -= (long long)plans.size();
    }
    if (plans.empty()) return;

    std::vector<Word> words((size_t)nreal);
    for (int kk = 0; kk < nreal; kk++) words[(size_t)kk] = I::read_word(bc, kk);
    for (const Plan &pl : plans) {
        for (int i = pl.lo; i <= pl.hi; i++) {
            if (I::empty(p.q[i])) continue;
            Word q = words[(size_t)i];
            for (const Field &f : fms[(size_t)i]) {
                if (f.base != pl.reg || f.w != 1) continue;
                if (i == pl.hi && f.kind == 'd') continue;
                if (i == pl.lo && !pl.copy && f.kind == 'u') continue;
                I::set_field(q, f.off, pl.fresh);
            }
            words[(size_t)i] = q;
        }
    }

    std::multimap<int, Word> ins;
    for (const Plan &pl : plans)
        if (pl.copy)
            ins.emplace(pl.bs, I::make_mov(pl.fresh, pl.reg));
    std::vector<Word> out;
    std::vector<int> oldof, leadpos((size_t)nreal + 1, -1);
    for (int kk = 0; kk < nreal; kk++) {
        auto range = ins.equal_range(kk);
        for (auto it = range.first; it != range.second; ++it) {
            if (leadpos[(size_t)kk] < 0) leadpos[(size_t)kk] = (int)out.size();
            out.push_back(it->second);
            oldof.push_back(-1);
        }
        if (leadpos[(size_t)kk] < 0) leadpos[(size_t)kk] = (int)out.size();
        out.push_back(words[(size_t)kk]);
        oldof.push_back(kk);
    }
    leadpos[(size_t)nreal] = (int)out.size();
    std::vector<u8> obc;
    stream_rebuild(p, bc, co, out, oldof, leadpos, nreal, "anticopy", true, obc, ct);
    bc.swap(obc);
    st.applied = (int)plans.size();
}
template void anticopy<Sm50>(std::vector<u8> &, std::vector<u8> &, bool, AnticopyStats &);
template void anticopy<Sm86>(std::vector<u8> &, std::vector<u8> &, bool, AnticopyStats &);

int g_sink_back = 2;
int g_sink_rounds = 32;
int g_sink_ext = 1;

bool Sm50::sink_op(u64 q, int nm) {
    const OpSets &T = S();
    static OpSet allow;
    static bool init = false;
    if (!init) {
        init = true;
        allow = make_opset({
            "Mov", "Mov32i", "Ldc", "Sel", "Rro", "Mufu", "Ipa",
            "Fadd", "Fadd32i", "Ffma", "Fmul", "Fmul32i", "Fmnmx",
            "Iadd", "Iadd3", "Iadd32i", "Imnmx", "Iscadd",
            "Lop", "Lop3", "Lop32i", "Shl", "Shr", "Shf", "Bfe", "Bfi",
            "Xmad", "Imad", "Prmt", "F2f", "F2i", "I2f", "I2i"});
    }
    if (nm < 0 || !allow[(size_t)nm]) return false;
    if (nm == T.O_Ldc) { if (((q >> 8) & 0xFF) != RZ) return false; }
    else if (T.load_or_store[(size_t)nm]) return false;
    if (nm == T.O_Mov && ((q >> 39) & 0xF) != 0xF) return false;
    return true;
}

template <class I>
static bool sink_movable(const ProgramT<I> &p, int i) {
    const OpSets &T = I::sets();
    int nm = p.op[i];
    if (nm < 0 || !I::sink_op(p.q[i], nm)) return false;
    if (T.side_effect[(size_t)nm] || T.branchy[(size_t)nm] ||
        T.pushy[(size_t)nm] || T.tex_bases[(size_t)nm]) return false;
    if (!I::guard_is_pt(p.q[i])) return false;
    return true;
}

template <class I>
static bool sink_round_i(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
                       SinkStats &st);
template <class I>
static bool sink_round(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
                       SinkStats &st) {
    bool r_ = sink_round_i<I>(bc, ct, fragment, st);
    return r_;
}
template <class I>
static bool sink_round_i(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
                       SinkStats &st) {
    typedef typename I::Word Word;
    const OpSets &T = I::sets();
    u32 co = I::const_off(ct);
    if (co > bc.size()) fail("sink: ConstBufOffset past the file");
    int n = I::nslots(co);
    if (n <= 0) return false;
    ProgramT<I> p;
    p.load_bytes(bc, ct);
    if (dce2_reads_cc(p)) return false;
    int nreal = 0;
    for (int k = 0; k < n && k < p.n; k++) if (!I::empty(p.q[k])) nreal = k + 1;
    if (nreal <= 0) return false;
    CFGraph c;
    std::vector<char> reach;
    std::vector<int> exit_live;
    std::vector<char> is_exit((size_t)RZ, 0);
    Live L;
    c.build(p, false);
    reach = c.reachable_from_entry();
    if (fragment) I::exit_live_regs(bc, exit_live);
    for (int r : exit_live) if (r >= 0 && r < RZ) is_exit[(size_t)r] = 1;
    liveness(p, c, reach, exit_live, L);

    std::vector<char> leader((size_t)nreal + 1, 0);
    leader[0] = 1;
    for (int i = 0; i < nreal; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        bool falls = false;
        for (int t : c.succ[(size_t)i]) {
            if (t == i + 1) falls = true;
            else if (t >= 0 && t < nreal) leader[(size_t)t] = 1;
        }
        if ((!falls || c.succ[(size_t)i].size() > 1) && i + 1 < nreal)
            leader[(size_t)i + 1] = 1;
    }

    int W = 0;
    std::vector<u64> dom;
    if (!dominators(c, reach, nreal, W, dom))
        fail("sink: the dominator fixpoint did not converge");
    auto has = [&](const std::vector<u64> &v, int row, int b) {
        return (v[(size_t)row * W + (b >> 6)] >> (b & 63)) & 1;
    };

    std::vector<char> in_cycle;
    cycle_nodes(c, reach, nreal, in_cycle);

    int maxlive = 0;
    std::vector<int> lpc((size_t)nreal, -1);
    for (int i = 0; i < nreal; i++)
        if (!I::empty(p.q[i]) && reach[(size_t)i]) {
            lpc[(size_t)i] = L.live[(size_t)i].popcount();
            maxlive = std::max(maxlive, lpc[(size_t)i]);
        }
    if (st.maxlive0 < 0) st.maxlive0 = maxlive;
    std::vector<char> peak((size_t)nreal, 0);
    for (int i = 0; i < nreal; i++)
        if (lpc[(size_t)i] >= maxlive - 1 && lpc[(size_t)i] >= 0)
            peak[(size_t)i] = 1;

    std::vector<int> blk((size_t)nreal, -1), bstart, bend;
    for (int i = 0; i < nreal; i++) {
        if (leader[(size_t)i] || bstart.empty()) { bstart.push_back(i); bend.push_back(i); }
        blk[(size_t)i] = (int)bstart.size() - 1;
        bend.back() = i;
    }
    const int NB = (int)bstart.size();
    const int BW = (NB + 63) / 64;
    std::vector<std::vector<int>> bsucc((size_t)NB);
    for (int b = 0; b < NB; b++) {
        if (!reach[(size_t)bstart[(size_t)b]]) continue;
        for (int t : c.succ[(size_t)bend[(size_t)b]])
            if (t >= 0 && t < nreal && reach[(size_t)t]) bsucc[(size_t)b].push_back(blk[(size_t)t]);
    }

    std::vector<u64> fwd((size_t)NB * BW, 0), bwd((size_t)NB * BW, 0);
    auto rowhas = [&](const std::vector<u64> &v, int b, int x) {
        return (v[(size_t)b * BW + (x >> 6)] >> (x & 63)) & 1;
    };
    for (int b = 0; b < NB; b++)
        for (int s : bsucc[(size_t)b]) fwd[(size_t)b * BW + (s >> 6)] |= (u64)1 << (s & 63);
    for (bool ch = true; ch;) {
        ch = false;
        for (int b = NB - 1; b >= 0; b--)
            for (int s : bsucc[(size_t)b])
                for (int w = 0; w < BW; w++) {
                    u64 nv = fwd[(size_t)b * BW + w] | fwd[(size_t)s * BW + w];
                    if (nv != fwd[(size_t)b * BW + w]) { fwd[(size_t)b * BW + w] = nv; ch = true; }
                }
    }
    for (int a = 0; a < NB; a++)
        for (int b = 0; b < NB; b++)
            if (rowhas(fwd, a, b)) bwd[(size_t)b * BW + (a >> 6)] |= (u64)1 << (a & 63);

    auto fwd_in = [&](int i, int j) {
        int bi = blk[(size_t)i], bj = blk[(size_t)j];
        return bi == bj ? j > i : (bool)rowhas(fwd, bi, bj);
    };
    auto bwd_in = [&](int t, int j) {
        int bt = blk[(size_t)t], bj = blk[(size_t)j];
        return bt == bj ? j < t : (bool)rowhas(bwd, bt, bj);
    };

    std::vector<std::vector<int>> touch((size_t)I::key_limit()),
        wtouch((size_t)I::key_limit());
    {
        std::vector<int> tl;
        for (int j = 0; j < nreal; j++) {
            if (!reach[(size_t)j]) continue;
            p.uses[j].list(tl);
            for (int r : tl) touch[(size_t)r].push_back(j);
            p.defs[j].list(tl);
            for (int r : tl) {
                wtouch[(size_t)r].push_back(j);
                if (!p.uses[j].has(r)) touch[(size_t)r].push_back(j);
            }
            p.maydefs[j].list(tl);
            for (int r : tl) {
                if (!p.defs[j].has(r)) wtouch[(size_t)r].push_back(j);
                if (!p.uses[j].has(r) && !p.defs[j].has(r)) touch[(size_t)r].push_back(j);
            }
        }
    }

    std::vector<int> target((size_t)nreal, -1);
    std::vector<std::vector<int>> mrefs((size_t)nreal);
    std::vector<int> dl, ml, ul, refs;
    std::vector<u64> common((size_t)W);
    int moved = 0;
    std::vector<int> peakpts;
    for (int i = 0; i < nreal; i++) if (peak[(size_t)i]) peakpts.push_back(i);
    int d = -1, lo = -1, best = -1, t2 = -1;

    for (int i = 0; i < nreal; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i] || !sink_movable(p, i)) continue;
        p.defs[i].list(dl);
        p.maydefs[i].list(ml);
        p.uses[i].list(ul);
        d = -1; lo = -1; best = -1; t2 = -1;
        if (dl.size() != 1 || !ml.empty()) continue;
        d = dl[0];
        if (d < 0 || d >= RZ || is_exit[(size_t)d]) continue;
        bool selfsrc = false;
        for (int s : ul) if (s == d) selfsrc = true;
        if (selfsrc) continue;

        const int bi = blk[(size_t)i];
        if (rowhas(fwd, bi, bi)) continue;
        refs.clear();
        for (int j : touch[(size_t)d]) if (fwd_in(i, j)) refs.push_back(j);
        if (refs.empty()) continue;

        best = -1;
        lo = refs[0];
        for (int r : refs) if (r < lo) lo = r;

        if (lo <= i) continue;
        const int w0 = i >> 6, w1 = lo >> 6;
        for (int w = w0; w <= w1; w++) common[(size_t)w] = ~(u64)0;
        for (int r : refs) {
            const u64 *drow = &dom[(size_t)r * W];
            for (int w = w0; w <= w1; w++) common[(size_t)w] &= drow[w];
        }
        for (int t = lo; t > i; t--) {
            u64 word = common[(size_t)(t >> 6)] & (((u64)2 << (t & 63)) - 1);
            if (!word) { t = (t & ~63); continue; }
            t = (t & ~63) + 63 - __builtin_clzll(word);
            if (t <= i) break;
            if (!reach[(size_t)t] || in_cycle[(size_t)t]) continue;
            if (!has(dom, t, i)) continue;
            best = t;
            break;
        }
        if (best < 0) continue;

        t2 = best;
        for (int k = 0; k < g_sink_back && t2 > i + 1 && !leader[(size_t)t2]; k++) t2--;
        if (t2 <= i + 1) continue;
        {

            auto between = [&](int j) { return fwd_in(i, j) && bwd_in(t2, j); };
            bool clob = false;
            for (int j : touch[(size_t)d]) if (between(j)) { clob = true; break; }
            for (size_t k = 0; k < ul.size() && !clob; k++)
                for (int j : wtouch[(size_t)ul[k]]) if (between(j)) { clob = true; break; }
            if (clob) continue;
            bool crosses = false;
            for (int x : peakpts) if (between(x)) { crosses = true; break; }
            if (!crosses) continue;

            int ext = 0;
            for (int s : ul)
                if (s >= 0 && s < RZ && !L.live[(size_t)t2].test(s)) ext++;
            if (ext > g_sink_ext) continue;
        }
        target[(size_t)i] = t2;
        mrefs[(size_t)i] = refs;
        moved++;
        st.moved++;
    }

    for (bool again = true; again;) {
        again = false;
        for (int i = 0; i < nreal; i++) {
            if (target[(size_t)i] < 0) continue;
            for (int r : mrefs[(size_t)i]) {
                if (target[(size_t)r] < 0) continue;
                if (target[(size_t)r] < target[(size_t)i] ||
                    (target[(size_t)r] == target[(size_t)i] && r < i)) {
                    target[(size_t)i] = -1;
                    moved--;
                    st.moved--;
                    again = true;
                    break;
                }
            }
        }
    }
    if (!moved) return false;

    std::vector<Word> words((size_t)nreal);
    for (int k = 0; k < nreal; k++) words[(size_t)k] = I::read_word(bc, k);
    std::vector<std::vector<int>> before((size_t)nreal + 1);
    for (int i = 0; i < nreal; i++)
        if (target[(size_t)i] >= 0) before[(size_t)target[(size_t)i]].push_back(i);
    std::vector<Word> out;
    std::vector<int> oldof, leadpos((size_t)nreal + 1, -1);
    for (int k = 0; k < nreal; k++) {
        for (int i : before[(size_t)k]) {
            if (leadpos[(size_t)k] < 0) leadpos[(size_t)k] = (int)out.size();
            out.push_back(words[(size_t)i]);
            oldof.push_back(i);
        }
        if (leadpos[(size_t)k] < 0) leadpos[(size_t)k] = (int)out.size();
        if (target[(size_t)k] >= 0) continue;
        out.push_back(words[(size_t)k]);
        oldof.push_back(k);
    }
    leadpos[(size_t)nreal] = (int)out.size();
    if ((int)out.size() != nreal) fail("sink: permutation changed the length");
    for (int kk = 0; kk < nreal; kk++) {
        int i2 = oldof[(size_t)kk];
        if (i2 < 0 || i2 >= p.n || I::empty(p.q[i2])) continue;
        if (!T.branchy_imm[(size_t)p.op[i2]]) continue;
        int t = p.target(i2);
        if (t < 0 || t > nreal) fail("sink: unresolved branch at slot %d", i2);
        int nt = leadpos[(size_t)t];
        if (!I::set_branch(out[(size_t)kk], kk, nt))
            fail("sink: branch displacement out of range");
    }
    for (int kk = 0; kk < nreal; kk++) I::write_word(bc, kk, out[(size_t)kk]);
    return true;
}

int g_remat_max = 8;

template <class I>
static bool remat_round(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
                        SinkStats &st) {
    typedef typename I::Word Word;
    u32 co = I::const_off(ct);
    if (co > bc.size()) fail("remat: ConstBufOffset past the file");
    int n = I::nslots(co);
    if (n <= 0) return false;
    ProgramT<I> p;
    p.load_bytes(bc, ct);
    if (dce2_reads_cc(p)) return false;
    int nreal = 0;
    for (int k = 0; k < n && k < p.n; k++) if (!I::empty(p.q[k])) nreal = k + 1;
    if (nreal <= 0) return false;
    CFGraph c;
    c.build(p, false);
    std::vector<char> reach = c.reachable_from_entry();
    std::vector<int> exit_live;
    if (fragment) I::exit_live_regs(bc, exit_live);
    std::vector<char> is_exit((size_t)RZ, 0);
    for (int r : exit_live) if (r >= 0 && r < RZ) is_exit[(size_t)r] = 1;
    Live L;
    liveness(p, c, reach, exit_live, L);

    SplitMapT<I> SM;
    Adj unused_adj;

    static std::vector<std::vector<int>> innode;
    if (!build_split(p, c, reach, L, exit_live, SM, unused_adj, false, &innode, true))
        return false;

    std::vector<char> grouped((size_t)RZ, 0);
    auto node_in = [&](int r, int i) -> int {
        if (r < 0 || r >= RZ) return -1;
        if (innode[(size_t)r].empty()) return L.live[(size_t)i].test(r) ? r : -1;
        return innode[(size_t)r][(size_t)i];
    };

    std::vector<char> leader((size_t)nreal + 1, 0);
    leader[0] = 1;
    for (int i = 0; i < nreal; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        bool falls = false;
        for (int t : c.succ[(size_t)i]) {
            if (t == i + 1) falls = true;
            else if (t >= 0 && t < nreal) leader[(size_t)t] = 1;
        }
        if ((!falls || c.succ[(size_t)i].size() > 1) && i + 1 < nreal)
            leader[(size_t)i + 1] = 1;
    }
    std::vector<int> block((size_t)nreal, 0);
    for (int i = 0, b = 0; i < nreal; i++) { if (leader[(size_t)i]) b = i; block[(size_t)i] = b; }

    int maxlive = 0;
    std::vector<int> lpc((size_t)nreal, -1);
    for (int i = 0; i < nreal; i++)
        if (!I::empty(p.q[i]) && reach[(size_t)i]) {
            lpc[(size_t)i] = L.live[(size_t)i].popcount();
            maxlive = std::max(maxlive, lpc[(size_t)i]);
        }
    std::vector<int> peakpts;
    for (int i = 0; i < nreal; i++)
        if (lpc[(size_t)i] >= maxlive - 1 && lpc[(size_t)i] >= 0)
            peakpts.push_back(i);

    std::vector<std::vector<Field>> fms((size_t)nreal);
    std::vector<char> used((size_t)RZ, 0);
    std::unordered_map<int, std::vector<int>> ndefs, nuses;
    for (int i = 0; i < nreal; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fms[(size_t)i]);
        for (const Field &f : fms[(size_t)i]) {
            for (int k = 0; k < f.w; k++)
                if (f.base + k >= 0 && f.base + k < RZ) {
                    used[(size_t)(f.base + k)] = 1;
                    if (f.w > 1) grouped[(size_t)(f.base + k)] = 1;
                }
            int nd = SM.at(i, f.off);
            if (nd < 0) continue;
            if (f.kind == 'd') ndefs[nd].push_back(i); else nuses[nd].push_back(i);
        }
    }
    int fresh_next = 0;
    auto fresh = [&]() {
        while (fresh_next < RZ && (used[(size_t)fresh_next] || is_exit[(size_t)fresh_next]))
            fresh_next++;
        if (fresh_next >= RZ) return -1;
        return fresh_next++;
    };

    struct Src { int off, name, node; };
    auto shape = [&](int i, int &d, int &doff, std::vector<Src> &srcs) {
        if (I::empty(p.q[i]) || !reach[(size_t)i] || !sink_movable(p, i)) return false;
        std::vector<int> dl, ml;
        p.defs[i].list(dl);
        p.maydefs[i].list(ml);
        if (dl.size() != 1 || !ml.empty()) return false;
        d = dl[0];
        if (d < 0 || d >= RZ || is_exit[(size_t)d] || grouped[(size_t)d]) return false;
        doff = -1;
        srcs.clear();
        for (const Field &f : fms[(size_t)i]) {
            if (f.w != 1) return false;
            if (f.kind == 'd') { if (f.base != d) return false; doff = f.off; }
            else {
                int nd = SM.at(i, f.off);
                if (nd < 0) return false;
                srcs.push_back({f.off, f.base, nd});
            }
        }
        if (doff < 0) return false;
        for (const Src &s : srcs) if (s.name == d) return false;
        return true;
    };

    std::vector<Word> words((size_t)nreal);
    for (int k = 0; k < nreal; k++) words[(size_t)k] = I::read_word(bc, k);
    std::multimap<int, Word> ins;
    std::vector<char> gone((size_t)nreal, 0);
    std::unordered_map<int, int> chain_name;
    std::set<int> gone_nodes;

    std::set<int> copy_reads;
    int made = 0;
    for (int i = 0; i < nreal; i++) {
        int d, doff;
        std::vector<Src> srcs;
        if (gone[(size_t)i] || !shape(i, d, doff, srcs)) continue;
        int dn = SM.at(i, doff);
        if (dn < 0) continue;
        auto dit = ndefs.find(dn);

        if (dit == ndefs.end()) continue;
        if (copy_reads.count(dn)) continue;

        {
            bool same = true;
            for (int k : dit->second) {
                if (k == i) continue;
                int dk, doffk;
                std::vector<Src> srcsk;
                if (gone[(size_t)k] || !shape(k, dk, doffk, srcsk) || dk != d ||
                    doffk != doff || !I::eq_but_field(p.q[k], p.q[i], doffk) ||
                    srcsk.size() != srcs.size()) { same = false; break; }
                for (size_t z = 0; z < srcs.size(); z++)
                    if (srcsk[z].off != srcs[z].off || srcsk[z].node != srcs[z].node) same = false;
                if (!same) break;
            }
            if (!same) continue;
        }
        auto uit = nuses.find(dn);
        if (uit == nuses.end() || uit->second.empty()) continue;
        const std::vector<int> &refs = uit->second;
        bool self = false;
        for (int r : refs) if (r == i) self = true;
        if (self) continue;
        std::map<int, int> firstref;
        for (int r : refs) {
            auto it = firstref.find(block[(size_t)r]);
            if (it == firstref.end() || r < it->second) firstref[block[(size_t)r]] = r;
        }
        if ((int)firstref.size() > g_remat_max) continue;

        bool gain = false;
        for (int x : peakpts) {
            if (x <= i || node_in(d, x) != dn) continue;
            auto fit = firstref.find(block[(size_t)x]);
            if (fit == firstref.end()) { gain = true; break; }
            int at = fit->second;
            for (int k = 0; k < g_sink_back && at > fit->first; k++) at--;
            if (at > x) { gain = true; break; }
        }
        if (!gain) continue;

        struct Plan { int at; std::vector<std::pair<int, Word>> pre; Word word; };
        std::vector<Plan> plans;
        bool ok = true;
        int F = -1;
        std::vector<std::pair<int, int>> chain_alloc;
        std::vector<int> named;
        auto chain_reg = [&](int nd) {
            auto it = chain_name.find(nd);
            if (it != chain_name.end()) return it->second;
            for (auto &pr : chain_alloc) if (pr.first == nd) return pr.second;
            int f = fresh();
            if (f >= 0) chain_alloc.push_back({nd, f});
            return f;
        };
        for (auto &pr : firstref) {
            int at = pr.second;
            for (int k = 0; k < g_sink_back && at > pr.first; k++) at--;
            Plan pl;
            pl.at = at;
            Word w = p.q[i];
            for (const Src &s : srcs) {
                if (gone_nodes.count(s.node)) {
                    ok = false; break;
                }
                if (node_in(s.name, at) == s.node) {
                    named.push_back(s.node);
                    continue;
                }

                auto sd = ndefs.find(s.node);
                if (sd == ndefs.end() || sd->second.size() != 1) {
                    ok = false; break;
                }
                int k = sd->second[0];
                int d2, doff2;
                std::vector<Src> srcs2;
                if (k == i || gone[(size_t)k] || !shape(k, d2, doff2, srcs2)) {
                    ok = false; break;
                }
                Word w2 = p.q[k];
                for (const Src &s2 : srcs2) {
                    if (gone_nodes.count(s2.node) || node_in(s2.name, at) != s2.node) {
                        ok = false; break;
                    }
                    named.push_back(s2.node);
                }
                if (!ok) break;
                int f2 = chain_reg(s.node);
                if (f2 < 0) { ok = false; break; }
                I::set_field(w2, doff2, f2);
                pl.pre.push_back({k, w2});
                I::set_field(w, s.off, f2);
            }
            if (!ok) break;
            pl.word = w;
            plans.push_back(pl);
        }
        if (!ok) continue;
        F = fresh();
        if (F < 0) break;
        for (auto &pr : chain_alloc) chain_name[pr.first] = pr.second;
        copy_reads.insert(named.begin(), named.end());
        for (Plan &pl : plans) {
            for (auto &pw : pl.pre) ins.emplace(pl.at, pw.second);
            Word wf = pl.word;
            I::set_field(wf, doff, F);
            ins.emplace(pl.at, wf);
            made += 1 + (int)pl.pre.size();
        }
        for (int r : refs) {
            Word q = words[(size_t)r];
            for (const Field &f : fms[(size_t)r])
                if (f.kind == 'u' && f.base == d && f.w == 1 && SM.at(r, f.off) == dn)
                    I::set_field(q, f.off, F);
            words[(size_t)r] = q;
        }
        for (int k : dit->second) gone[(size_t)k] = 1;
        gone_nodes.insert(dn);
        st.moved++;
    }
    if (!made) return false;

    std::vector<Word> out;
    std::vector<int> oldof, leadpos((size_t)nreal + 1, -1);
    for (int kk = 0; kk < nreal; kk++) {
        auto range = ins.equal_range(kk);
        for (auto it = range.first; it != range.second; ++it) {
            if (leadpos[(size_t)kk] < 0) leadpos[(size_t)kk] = (int)out.size();
            out.push_back(it->second);
            oldof.push_back(-1);
        }
        if (leadpos[(size_t)kk] < 0) leadpos[(size_t)kk] = (int)out.size();
        if (gone[(size_t)kk]) continue;
        out.push_back(words[(size_t)kk]);
        oldof.push_back(kk);
    }
    leadpos[(size_t)nreal] = (int)out.size();
    std::vector<u8> obc;
    stream_rebuild(p, bc, co, out, oldof, leadpos, nreal, "remat", false, obc, ct);
    bc.swap(obc);
    return true;
}

int g_spill_max = 4;

int g_spill_warps = 20;

template <class I>
static bool spill_round(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
                        SinkStats &st) {
    typedef typename I::Word Word;
    const OpSets &T = I::sets();
    if (g_spill_max <= 0) return false;
    u32 co = I::const_off(ct);
    if (co > bc.size()) fail("spill: ConstBufOffset past the file");
    int n = I::nslots(co);
    if (n <= 0) return false;
    ProgramT<I> p;
    p.load_bytes(bc, ct);
    if (dce2_reads_cc(p)) return false;
    int nreal = 0;
    for (int k = 0; k < n && k < p.n; k++) if (!I::empty(p.q[k])) nreal = k + 1;
    if (nreal <= 0) return false;
    CFGraph c;
    c.build(p, false);
    std::vector<char> reach = c.reachable_from_entry();
    std::vector<int> exit_live;
    if (fragment) I::exit_live_regs(bc, exit_live);
    std::vector<char> is_exit((size_t)RZ, 0);
    for (int r : exit_live) if (r >= 0 && r < RZ) is_exit[(size_t)r] = 1;
    Live L;
    liveness(p, c, reach, exit_live, L);

    int next_off = 0;
    for (int i = 0; i < nreal; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i] || !T.local_ops[(size_t)p.op[i]]) continue;
        int areg, w;
        int32_t off;
        I::lmem_access(p.q[i], p.op[i], &areg, &off, &w);
        if (areg != RZ) return false;
        if (off < 0) return false;
        if (off + 4 * w > next_off) next_off = off + 4 * w;
    }
    int nslots = g_spill_max - next_off / 4;
    if (nslots <= 0) return false;

    SplitMapT<I> SM;
    Adj unused_adj;

    static std::vector<std::vector<int>> innode;
    if (!build_split(p, c, reach, L, exit_live, SM, unused_adj, false, &innode, true))
        return false;
    auto node_in = [&](int r, int i) -> int {
        if (r < 0 || r >= RZ) return -1;
        if (innode[(size_t)r].empty()) return L.live[(size_t)i].test(r) ? r : -1;
        return innode[(size_t)r][(size_t)i];
    };

    std::vector<char> leader((size_t)nreal + 1, 0);
    leader[0] = 1;
    for (int i = 0; i < nreal; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        bool falls = false;
        for (int t : c.succ[(size_t)i]) {
            if (t == i + 1) falls = true;
            else if (t >= 0 && t < nreal) leader[(size_t)t] = 1;
        }
        if ((!falls || c.succ[(size_t)i].size() > 1) && i + 1 < nreal)
            leader[(size_t)i + 1] = 1;
    }
    std::vector<int> block((size_t)nreal, 0);
    for (int i = 0, b = 0; i < nreal; i++) { if (leader[(size_t)i]) b = i; block[(size_t)i] = b; }

    int maxlive = 0;
    for (int i = 0; i < nreal; i++)
        if (!I::empty(p.q[i]) && reach[(size_t)i])
            maxlive = std::max(maxlive, L.live[(size_t)i].popcount());
    if (I::occupancy_of(maxlive) > g_spill_warps) return false;
    std::vector<int> peakpts;
    for (int i = 0; i < nreal; i++)
        if (!I::empty(p.q[i]) && reach[(size_t)i] && L.live[(size_t)i].popcount() >= maxlive - 1)
            peakpts.push_back(i);
    if (peakpts.empty()) return false;

    std::vector<std::vector<Field>> fms((size_t)nreal);
    std::vector<char> used((size_t)RZ, 0), grouped((size_t)RZ, 0);
    std::unordered_map<int, std::vector<int>> ndefs, nuses;
    std::unordered_map<int, int> nname;
    for (int i = 0; i < nreal; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        I::fieldmap(p.q[i], p.op[i], p.props[i], fms[(size_t)i]);
        for (const Field &f : fms[(size_t)i]) {
            for (int k = 0; k < f.w; k++)
                if (f.base + k >= 0 && f.base + k < RZ) {
                    used[(size_t)(f.base + k)] = 1;
                    if (f.w > 1) grouped[(size_t)(f.base + k)] = 1;
                }
            int nd = SM.at(i, f.off);
            if (nd < 0) continue;
            nname[nd] = f.base;
            if (f.kind == 'd') ndefs[nd].push_back(i); else nuses[nd].push_back(i);
        }
    }
    int fresh_next = 0;
    auto fresh = [&]() {
        while (fresh_next < RZ && (used[(size_t)fresh_next] || is_exit[(size_t)fresh_next]))
            fresh_next++;
        if (fresh_next >= RZ) return -1;
        return fresh_next++;
    };

    struct Cand { int node, name, score, nblocks; };
    std::vector<Cand> cands;
    std::set<int> seen_nodes;
    for (int x : peakpts) {
        std::vector<int> regs;
        L.live[(size_t)x].bits(regs);
        for (int r : regs) {
            if (r >= RZ || is_exit[(size_t)r] || grouped[(size_t)r]) continue;
            int dn = node_in(r, x);
            if (dn < 0 || seen_nodes.count(dn)) continue;
            seen_nodes.insert(dn);
            auto dit = ndefs.find(dn);
            auto uit = nuses.find(dn);
            if (dit == ndefs.end() || uit == nuses.end() || uit->second.empty()) continue;
            bool ok = true;
            for (int k : dit->second) {
                if (!I::guard_is_pt(p.q[k]) || T.branchy[(size_t)p.op[k]] ||
                    T.pushy[(size_t)p.op[k]] || T.local_ops[(size_t)p.op[k]]) { ok = false; break; }
                std::vector<int> ml;
                p.maydefs[k].list(ml);
                if (!ml.empty()) { ok = false; break; }
                bool plain = false;
                for (const Field &f : fms[(size_t)k])
                    if (f.kind == 'd' && f.base == r && f.w == 1 && SM.at(k, f.off) == dn) plain = true;
                if (!plain) { ok = false; break; }
            }
            if (!ok) continue;
            std::map<int, int> firstref;
            for (int u : uit->second) {
                bool plain = false;
                for (const Field &f : fms[(size_t)u])
                    if (f.kind == 'u' && f.base == r && f.w == 1 && SM.at(u, f.off) == dn) plain = true;
                if (!plain) { ok = false; break; }
                auto it = firstref.find(block[(size_t)u]);
                if (it == firstref.end() || u < it->second) firstref[block[(size_t)u]] = u;
            }
            if (!ok) continue;

            for (int k : dit->second) if (p.uses[k].has(r) && node_in(r, k) == dn) ok = false;
            if (!ok) continue;
            int score = 0;
            for (int y : peakpts) {
                if (node_in(r, y) != dn) continue;
                auto fit = firstref.find(block[(size_t)y]);
                if (fit == firstref.end()) { score++; continue; }
                int at = fit->second;
                for (int k = 0; k < g_sink_back && at > fit->first; k++) at--;
                if (at > y) score++;
            }
            if (score && (int)firstref.size() <= g_remat_max)
                cands.push_back({dn, r, score, (int)firstref.size()});
        }
    }
    if (cands.empty()) return false;

    std::stable_sort(cands.begin(), cands.end(), [](const Cand &a, const Cand &b) {
        if (a.score != b.score) return a.score > b.score;
        return a.nblocks < b.nblocks;
    });

    std::vector<Word> words((size_t)nreal);
    for (int k = 0; k < nreal; k++) words[(size_t)k] = I::read_word(bc, k);
    std::multimap<int, Word> ins;
    int made = 0, taken = 0;
    for (const Cand &cd : cands) {
        if (taken >= nslots) break;
        int F = fresh();
        if (F < 0) break;
        int off = next_off + 4 * taken;
        const std::vector<int> &defs = ndefs[cd.node];
        const std::vector<int> &uses = nuses[cd.node];
        for (int k : defs) {
            ins.emplace(k + 1, I::make_stl(off, cd.name));
            made++;
        }
        std::map<int, int> firstref;
        for (int u : uses) {
            auto it = firstref.find(block[(size_t)u]);
            if (it == firstref.end() || u < it->second) firstref[block[(size_t)u]] = u;
        }
        for (auto &pr : firstref) {
            int at = pr.second;
            for (int k = 0; k < g_sink_back && at > pr.first; k++) at--;
            ins.emplace(at, I::make_ldl(F, off));
            made++;
        }
        for (int u : uses) {
            Word q = words[(size_t)u];
            for (const Field &f : fms[(size_t)u])
                if (f.kind == 'u' && f.base == cd.name && f.w == 1 && SM.at(u, f.off) == cd.node)
                    I::set_field(q, f.off, F);
            words[(size_t)u] = q;
        }
        taken++;
        st.moved++;
    }
    if (!made) return false;

    std::vector<Word> out;
    std::vector<int> oldof, leadpos((size_t)nreal + 1, -1);
    for (int kk = 0; kk <= nreal; kk++) {
        auto range = ins.equal_range(kk);
        for (auto it = range.first; it != range.second; ++it) {
            if (leadpos[(size_t)kk] < 0) leadpos[(size_t)kk] = (int)out.size();
            out.push_back(it->second);
            oldof.push_back(-1);
        }
        if (leadpos[(size_t)kk] < 0) leadpos[(size_t)kk] = (int)out.size();
        if (kk == nreal) break;
        out.push_back(words[(size_t)kk]);
        oldof.push_back(kk);
    }
    std::vector<u8> obc;
    stream_rebuild(p, bc, co, out, oldof, leadpos, nreal, "spill", false, obc, ct);
    bc.swap(obc);
    return true;
}

template <class I>
static bool entry_live_grew(const std::vector<u8> &bc, const std::vector<u8> &ct,
                           const std::vector<int> &before) {
    std::vector<int> now;
    entry_live<I>(bc, ct, now);
    for (int r : now)
        if (std::find(before.begin(), before.end(), r) == before.end())
            return true;
    return false;
}

template <class I>
void sink_cheap(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
                SinkStats &st) {
    bool changed = false;
    std::vector<int> ent0;
    entry_live<I>(bc, ct, ent0);
    std::vector<u8> kb, kc;
    for (int r = 0; r < g_sink_rounds; r++) {
        if (!sink_round<I>(bc, ct, fragment, st)) break;
        changed = true;
    }
    for (int r = 0; r < g_sink_rounds; r++) {
        bool rr_;
        kb = bc; kc = ct;
        rr_ = remat_round<I>(bc, ct, fragment, st);
        if (rr_ && entry_live_grew<I>(bc, ct, ent0)) {
            bc.swap(kb); ct.swap(kc); rr_ = false;
        }
        if (!rr_) break;
        changed = true;
        for (int r2 = 0; r2 < g_sink_rounds; r2++)
            if (!sink_round<I>(bc, ct, fragment, st)) break;
    }
    bool sp_;
    kb = bc; kc = ct;
    sp_ = spill_round<I>(bc, ct, fragment, st);
    if (sp_ && entry_live_grew<I>(bc, ct, ent0)) {
        bc.swap(kb); ct.swap(kc); sp_ = false;
    }
    if (sp_) {
        changed = true;
        for (int r2 = 0; r2 < g_sink_rounds; r2++)
            if (!sink_round<I>(bc, ct, fragment, st)) break;
    }

    if (changed) {
        I::phase_b(bc, I::const_off(ct));
    }
}
template void sink_cheap<Sm50>(std::vector<u8> &, std::vector<u8> &, bool, SinkStats &);
template void sink_cheap<Sm86>(std::vector<u8> &, std::vector<u8> &, bool, SinkStats &);

template <class I>
void entry_live(const std::vector<u8> &bc, const std::vector<u8> &ct,
                std::vector<int> &out) {
    ProgramT<I> p;
    p.load_bytes(bc, ct);
    CFGraph c;
    c.build(p, false);
    std::vector<char> reach = c.reachable_from_entry();
    Mask ent;
    live_entry(p, c, reach, ent);
    ent.bits(out);
}
template void entry_live<Sm50>(const std::vector<u8> &, const std::vector<u8> &,
                               std::vector<int> &);
template void entry_live<Sm86>(const std::vector<u8> &, const std::vector<u8> &,
                               std::vector<int> &);

bool g_vn = false;

template <class I>
static bool vn_cse_op(const ProgramT<I> &p, int i) {
    const OpSets &T = I::sets();
    int nm = p.op[i];
    if (nm < 0) return false;
    if (T.side_effect[(size_t)nm] || T.branchy[(size_t)nm] ||
        T.pushy[(size_t)nm] || T.freebie[(size_t)nm]) return false;
    if (T.tex_bases[(size_t)nm]) {
        return false;
    } else {
        if (!T.pure_cse[(size_t)nm] && nm != T.O_Mov && nm != T.O_Mov32i)
            return false;
        if (T.load_or_store[(size_t)nm] && nm != T.O_Ldc) return false;
    }
    if (!I::guard_is_pt(p.q[i])) return false;
    if (p.maydefs[i].any()) return false;
    std::vector<int> v;
    p.defs[i].list(v);
    if (v.empty()) return false;
    for (int r : v) if (!is_gpr_key(r)) return false;
    int spur = I::spurious_pred(nm, p.q[i]);
    p.uses[i].list(v);
    for (int r : v) if (!is_gpr_key(r) && r != spur) return false;
    return true;
}

template <class I>
static int vn_dead_sweep(const ProgramT<I> &p, const CFGraph &c,
                         const std::vector<char> &reach,
                         const std::vector<int> &exit_live,
                         std::vector<char> &killed) {
    std::vector<Mask> lout;
    std::vector<int> v;
    int dead = 0;
    for (int r = 0; r < 16; r++) {
        dce2_liveout(p, c, reach, killed, exit_live, lout);
        bool ch = false;
        for (int i = 0; i < p.n; i++) {
            if (!reach[(size_t)i] || killed[(size_t)i] || I::empty(p.q[i])) continue;
            if (!vn_cse_op(p, i)) continue;
            p.defs[i].list(v);
            bool live = false;
            for (int rg : v) if (is_gpr_key(rg) && lout[(size_t)i].test(rg)) live = true;
            if (live) continue;
            killed[(size_t)i] = 1; dead++; ch = true;
        }
        if (!ch) break;
    }
    return dead;
}

template <class I>
static bool vn_copy(const ProgramT<I> &p, int i) {
    int d, s;
    if (!I::reg_move(p.q[i], p.op[i], &d, &s)) return false;
    if (!I::guard_is_pt(p.q[i])) return false;
    return is_gpr_key(s) && is_gpr_key(d);
}

struct VnGroup {
    int w = 0, fresh = -1;
    bool ok = true;
    int name[8] = {0};
    int node[8] = {0};
};

static int vn_live_gprs(const Mask &m) {
    int c = 0;
    for (int w = 0; w < (RZ + 63) / 64; w++) {
        u64 x = m.w[w];
        if (w == (RZ >> 6)) x &= ((u64)1 << (RZ & 63)) - 1;
        while (x) { x &= x - 1; c++; }
    }
    return c;
}

template <class I>
static bool vn_round(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
                     int span, bool &rejected) {
    typedef typename I::Word Word;
    u32 co = I::const_off(ct);
    if (co > bc.size()) fail("vn: ConstBufOffset past the file");
    int n = I::nslots(co);
    if (n <= 0) return false;
    ProgramT<I> p;
    p.load_bytes(bc, ct);
    if (dce2_reads_cc(p)) return false;
    int nreal = 0;
    for (int k = 0; k < n && k < p.n; k++) if (!I::empty(p.q[k])) nreal = k + 1;
    if (nreal <= 0) return false;
    CFGraph c;
    c.build(p, false);
    std::vector<char> reach = c.reachable_from_entry();

    if (c.overflow) return false;
    for (int i = 0; i < nreal; i++)
        if (reach[(size_t)i] && c.unknown[(size_t)i]) return false;
    std::vector<char> in_cycle;
    cycle_nodes(c, reach, nreal, in_cycle);
    std::vector<int> exit_live;
    if (fragment) I::exit_live_regs(bc, exit_live);
    std::vector<char> is_exit((size_t)RZ, 0);
    for (int r : exit_live) if (r >= 0 && r < RZ) is_exit[(size_t)r] = 1;
    Live L;
    liveness(p, c, reach, exit_live, L);

    SplitMapT<I> SM;
    Adj unused_adj;
    static std::vector<std::vector<int>> innode, outnode;
    if (!build_split(p, c, reach, L, exit_live, SM, unused_adj, false,
                     &innode, true, &outnode))
        return false;
    auto nin = [&](int r, int i) -> int {
        if (r < 0 || r >= RZ) return -1;
        const std::vector<int> &v = innode[(size_t)r];
        return v.empty() ? -1 : v[(size_t)i];
    };
    auto nout = [&](int r, int i) -> int {
        if (r < 0 || r >= RZ) return -1;
        const std::vector<int> &v = outnode[(size_t)r];
        return v.empty() ? -1 : v[(size_t)i];
    };

    std::vector<std::vector<Field>> fms((size_t)nreal);
    for (int i = 0; i < nreal; i++)
        if (!I::empty(p.q[i]) && reach[(size_t)i])
            I::fieldmap(p.q[i], p.op[i], p.props[i], fms[(size_t)i]);

    std::vector<char> used((size_t)RZ, 0);
    {
        std::vector<int> v;
        for (int i = 0; i < p.n; i++) {
            if (I::empty(p.q[i])) continue;
            typename I::RSet all = p.defs[i];
            all.unite(p.maydefs[i]);
            all.unite(p.uses[i]);
            all.list(v);
            for (int r : v) if (r >= 0 && r < RZ) used[(size_t)r] = 1;
            if (i >= nreal || !reach[(size_t)i]) continue;
            for (const Field &f : fms[(size_t)i])
                for (int k = 0; k < f.w; k++)
                    if (f.base + k >= 0 && f.base + k < RZ)
                        used[(size_t)(f.base + k)] = 1;
        }
    }

    std::unordered_map<int, int> ndef;
    for (int i = 0; i < nreal; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        for (const Field &f : fms[(size_t)i]) {
            if (f.kind != 'd') continue;
            for (int k = 0; k < f.w; k++) {
                int nd = nout(f.base + k, i);
                if (nd >= 0) ndef[nd]++;
            }
        }
    }

    std::unordered_map<int, int> vnum;
    int nextvn = 1;
    for (const auto &e : ndef) if (e.second != 1) vnum[e.first] = nextvn++;
    auto vnof = [&](int node) -> int {
        if (node < 0) return nextvn++;
        auto it = vnum.find(node);
        if (it != vnum.end()) return it->second;
        int v = nextvn++;
        vnum[node] = v;
        return v;
    };

    std::string key;
    auto build_key = [&](int i) {
        key.clear();
        long long x;
        auto push = [&](long long y) { x = y; key.append((const char *)&x, sizeof x); };
        push(p.op[i]);
        I::field_free_key(key, p.q[i], fms[(size_t)i]);
        for (const Field &f : fms[(size_t)i]) {
            push(((long long)f.off << 16) | ((long long)f.w << 8) | (long long)f.kind);
            if (f.kind == 'd') continue;
            for (int k = 0; k < f.w; k++) push(vnof(nin(f.base + k, i)));
        }
    };

    int W = 0;
    std::vector<u64> dom;
    if (!dominators(c, reach, nreal, W, dom)) return false;
    auto dominates = [&](int a, int b) {
        return (dom[(size_t)b * W + (a >> 6)] >> (a & 63)) & 1;
    };

    std::vector<VnGroup> gr;
    std::unordered_map<long long, int> gidof;
    std::unordered_map<int, long long> gpos;
    std::unordered_map<std::string, std::vector<int>> table;
    for (int i = 0; i < nreal; i++) {
        if (I::empty(p.q[i]) || !reach[(size_t)i]) continue;
        bool ok = !in_cycle[(size_t)i] && vn_cse_op(p, i);
        if (ok)
            for (const Field &f : fms[(size_t)i]) {
                if (f.kind != 'd') continue;
                for (int k = 0; k < f.w && ok; k++) {
                    int nd = nout(f.base + k, i);
                    if (nd >= 0 && ndef[nd] != 1) ok = false;
                }
                if (!ok) break;
            }
        int m = -1, seen = -1;
        const bool iscopy = !I::empty(p.q[i]) && reach[(size_t)i] && vn_copy(p, i);
        if (ok) {
            build_key(i);
            std::vector<int> &cand = table[key];

            for (size_t z = cand.size(); z-- > 0;) {
                if (seen < 0) seen = cand[z];
                if (i - cand[z] > span) continue;
                if (dominates(cand[z], i)) { m = cand[z]; break; }
            }
            if (m < 0) cand.push_back(i);
        }

        for (size_t z = 0; z < fms[(size_t)i].size(); z++) {
            const Field &f = fms[(size_t)i][z];
            if (f.kind != 'd') continue;
            if (iscopy) {
                int nd = nout(f.base, i);
                int cd = 0, cs = 0;
                I::reg_move(p.q[i], p.op[i], &cd, &cs);
                if (nd >= 0 && ndef[nd] == 1)
                    vnum[nd] = vnof(nin(cs, i));
            } else if (m < 0) {
                for (int k = 0; k < f.w; k++) {
                    int nd = nout(f.base + k, i);
                    if (nd >= 0 && ndef[nd] == 1) vnum[nd] = nextvn++;
                }
            }
            if (m < 0) continue;
            const Field &g = fms[(size_t)m][z];
            if (!iscopy)
                for (int k = 0; k < f.w; k++) {
                    int nd = nout(f.base + k, i);
                    if (nd >= 0 && ndef[nd] == 1)
                        vnum[nd] = vnof(nout(g.base + k, m));
                }
            if (f.w > 8) continue;
            long long gk = (long long)m * 64 + (long long)z;
            auto git = gidof.find(gk);
            int gid;
            if (git == gidof.end()) {
                VnGroup G;
                G.w = g.w;
                for (int k = 0; k < g.w; k++) {
                    G.name[k] = g.base + k;
                    G.node[k] = nout(g.base + k, m);
                    if (G.node[k] < 0 || is_exit[(size_t)(g.base + k)]) G.ok = false;
                }
                gid = (int)gr.size();
                gr.push_back(G);
                gidof.emplace(gk, gid);
                if (G.ok)
                    for (int k = 0; k < g.w; k++) gpos[G.node[k]] = (long long)gid * 8 + k;
            } else {
                gid = git->second;
            }
            if (!gr[(size_t)gid].ok) continue;
            for (int k = 0; k < f.w; k++) {
                int nd = nout(f.base + k, i);
                if (nd < 0) { gr[(size_t)gid].ok = false; break; }
                gpos[nd] = (long long)gid * 8 + k;
            }
        }
    }
    if (gpos.empty()) return false;

    std::vector<char> gfail((size_t)gr.size(), 0);
    for (size_t pass = 0; pass <= gr.size() + 1; pass++) {
        bool ch = false;
        for (int u = 0; u < nreal; u++) {
            if (I::empty(p.q[u]) || !reach[(size_t)u]) continue;
            for (const Field &f : fms[(size_t)u]) {
                if (f.kind == 'd') continue;
                int g0 = -1, k0 = -1, nfound = 0;
                bool okf = true;
                for (int j = 0; j < f.w; j++) {
                    auto it = gpos.find(nin(f.base + j, u));
                    if (it == gpos.end()) { okf = false; continue; }
                    nfound++;
                    int gid = (int)(it->second / 8), kk = (int)(it->second % 8);
                    if (j == 0) { g0 = gid; k0 = kk; }
                    else if (gid != g0 || kk != k0 + j) okf = false;
                }
                if (!nfound) continue;
                if (g0 < 0 || k0 < 0 || k0 + f.w > gr[(size_t)g0].w ||
                    gfail[(size_t)g0]) okf = false;
                if (okf) continue;
                for (int j = 0; j < f.w; j++) {
                    auto it = gpos.find(nin(f.base + j, u));
                    if (it == gpos.end()) continue;
                    int gid = (int)(it->second / 8);
                    if (!gfail[(size_t)gid]) { gfail[(size_t)gid] = 1; ch = true; }
                }
            }
        }
        if (!ch) break;
        if (pass == gr.size() + 1) return false;
    }

    int ngroup = 0;
    {
        int next_free = 0;
        for (size_t g = 0; g < gr.size(); g++) {
            if (!gr[g].ok || gfail[g]) continue;
            int w = gr[g].w, base = -1;
            for (int r = next_free; r + w <= RZ; r++) {
                bool free_run = true;
                for (int k = 0; k < w; k++)
                    if (used[(size_t)(r + k)] || is_exit[(size_t)(r + k)]) free_run = false;
                if (free_run) { base = r; break; }
            }
            if (base < 0) { gfail[g] = 1; continue; }
            gr[g].fresh = base;
            for (int k = 0; k < w; k++) used[(size_t)(base + k)] = 1;
            next_free = base + w;
            ngroup++;
        }
    }
    if (!ngroup) return false;

    std::vector<Word> words((size_t)nreal);
    for (int k = 0; k < nreal; k++) words[(size_t)k] = I::read_word(bc, k);
    int moved = 0;
    for (int u = 0; u < nreal; u++) {
        if (I::empty(p.q[u]) || !reach[(size_t)u]) continue;
        for (const Field &f : fms[(size_t)u]) {
            int g0 = -1, k0 = -1;
            if (f.kind == 'd') {
                auto it = gpos.find(nout(f.base, u));
                if (it == gpos.end()) continue;
                g0 = (int)(it->second / 8); k0 = (int)(it->second % 8);
                if (gfail[(size_t)g0] || gr[(size_t)g0].fresh < 0) continue;

                if (gr[(size_t)g0].node[k0] != nout(f.base, u)) continue;
                if (k0 != 0 || f.w != gr[(size_t)g0].w) continue;
            } else {
                for (int j = 0; j < f.w; j++) {
                    auto it = gpos.find(nin(f.base + j, u));
                    if (it == gpos.end()) { g0 = -1; break; }
                    int gid = (int)(it->second / 8), kk = (int)(it->second % 8);
                    if (gfail[(size_t)gid] || gr[(size_t)gid].fresh < 0) { g0 = -1; break; }
                    if (j == 0) { g0 = gid; k0 = kk; }
                    else if (gid != g0 || kk != k0 + j) { g0 = -1; break; }
                }
                if (g0 < 0 || k0 < 0 || k0 + f.w > gr[(size_t)g0].w) continue;
            }
            I::set_field(words[(size_t)u], f.off, gr[(size_t)g0].fresh + k0);
            moved++;
        }
    }
    if (!moved) return false;

    std::vector<u8> nbc = bc;
    for (int k = 0; k < nreal; k++) I::write_word(nbc, k, words[(size_t)k]);
    ProgramT<I> p2;
    p2.load_bytes(nbc, ct);
    CFGraph c2;
    c2.build(p2, false);
    std::vector<char> reach2 = c2.reachable_from_entry();
    std::vector<char> killed((size_t)p2.n, 0);
    int dead = vn_dead_sweep(p2, c2, reach2, exit_live, killed);
    if (!dead) return false;

    std::vector<int> newidx((size_t)nreal + 1, -1), nextkept((size_t)nreal + 1, -1);
    std::vector<Word> out;
    std::vector<int> oldof;
    for (int k = 0; k < nreal; k++) {
        if (k < p2.n && killed[(size_t)k]) continue;
        newidx[(size_t)k] = (int)out.size();
        out.push_back(words[(size_t)k]);
        oldof.push_back(k);
    }
    if (out.empty()) fail("vn: nothing left");
    { int nk = (int)out.size();
      for (int k = nreal; k >= 0; k--) {
          if (k < nreal && newidx[(size_t)k] >= 0) nk = newidx[(size_t)k];
          nextkept[(size_t)k] = nk;
      } }
    std::vector<u8> obc, oct = ct;
    u32 co2 = stream_rebuild(p2, bc, co, out, oldof, nextkept, nreal, "vn", true, obc, oct);

    int cyc0 = I::issue_cycles(bc, co), cyc1 = I::issue_cycles(obc, co2);
    int ml0 = 0, ml1 = 0;
    for (int i = 0; i < nreal; i++)
        if (!I::empty(p.q[i]) && reach[(size_t)i])
            ml0 = std::max(ml0, vn_live_gprs(L.live[(size_t)i]));
    {
        ProgramT<I> p3;
        p3.load_bytes(obc, oct);
        CFGraph c3;
        c3.build(p3, false);
        std::vector<char> r3 = c3.reachable_from_entry();
        Live L3;
        liveness(p3, c3, r3, exit_live, L3);
        for (int i = 0; i < p3.n; i++)
            if (!I::empty(p3.q[i]) && r3[(size_t)i])
                ml1 = std::max(ml1, vn_live_gprs(L3.live[(size_t)i]));
    }

    {
        ProgramT<I> p4;
        p4.load_bytes(obc, oct);
        CFGraph c4;
        c4.build(p4, false);
        std::vector<char> r4 = c4.reachable_from_entry();
        Mask ent;
        live_entry(p4, c4, r4, ent);
        if (ent.any()) {
            rejected = true; return false;
        }
    }
    bool keep = cyc1 <= cyc0;
    if (!keep) {
        rejected = true; return false;
    }

    bc.swap(obc);
    ct.swap(oct);
    return true;
}

template <class I>
void vn_cse(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
            VnStats &st, int reach) {
    if (!g_vn) return;
    for (int r = 0; r < 8; r++) {
        bool rejected = false;
        if (!vn_round<I>(bc, ct, fragment, reach, rejected)) break;
        st.rounds++;
    }
}
template void vn_cse<Sm50>(std::vector<u8> &, std::vector<u8> &, bool, VnStats &, int);
template void vn_cse<Sm86>(std::vector<u8> &, std::vector<u8> &, bool, VnStats &, int);

}
