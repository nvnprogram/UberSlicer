
#include <chrono>
#include "emit.h"
#include "nv_sched_ctl.h"

extern "C" {
int uber_validate(unsigned char *bc, unsigned int constOff);
int ub_vote_latency(unsigned long long q);
extern int uber_vote_floor_fail;
}

namespace ub {

struct Field { int off, base, w; char kind; };

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

void words_used_regs(const std::vector<u64> &words, std::set<int> &out) {
    std::vector<Field> fm;
    for (u64 q : words) {
        if (!q) continue;
        fieldmap(q, decode_op(q), decode_props(q), fm);
        fm_regs(fm, out);
    }
}

static void check_fieldmap(const Program &p) {
    std::vector<Field> fm;
    for (int i = 0; i < p.n; i++) {
        if (!p.q[i]) continue;
        fieldmap(p.q[i], p.op[i], p.props[i], fm);
        std::set<int> got;
        fm_regs(fm, got);
        RSet u = p.defs[i];
        u.unite(p.maydefs[i]);
        u.unite(p.uses[i]);
        std::vector<int> lst; u.list(lst);
        std::set<int> want;
        for (int r : lst) if (r < RZ) want.insert(r);
        if (got != want)
            fail("field map disagrees with _du at instruction %d (%s)", i,
                 op_name(p.op[i]));
    }
}

struct Live {
    std::vector<Mask> live, dmask, umask;
};

static void liveness(const Program &p, const CFGraph &c,
                     const std::vector<char> &reach,
                     const std::vector<int> &exit_live, Live &L) {
    const OpSets &Te = S();
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
        for (int r : v) if (r < RZ) L.dmask[(size_t)i].set(r);
        int spur = spurious_pred(p.op[i], p.q[i]);
        p.uses[i].list(v);
        for (int r : v) if (r < RZ && r != spur) L.umask[(size_t)i].set(r);
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
            if (p.op[i] == Te.O_Exit || p.op[i] == Te.O_Ret) lo |= seed;
            li = lo;
            li.andnot_or(L.dmask[(size_t)i], L.umask[(size_t)i]);
            if (li != L.live[(size_t)i]) { L.live[(size_t)i] = li; ch = true; }
        }
        if (!ch) { conv = true; break; }
    }
    if (!conv) fail("liveness did not converge");
}

static void live_entry(const Program &p, const CFGraph &c,
                       const std::vector<char> &reach, Mask &ent) {
    int n = p.n;
    std::vector<Mask> live((size_t)n), dm((size_t)n), um((size_t)n);
    std::vector<int> order;
    for (int i = 0; i < n; i++) if (reach[(size_t)i]) order.push_back(i);
    std::vector<int> v;
    for (int i : order) {
        p.defs[i].list(v);
        for (int r : v) dm[(size_t)i].set(r);
        int spur = spurious_pred(p.op[i], p.q[i]);
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

static void interference(const Program &p, const std::vector<char> &reach,
                         Live &L, Adj &adj) {
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
                if (pass && d >= RZ) continue;
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

static void runs_of(const Program &p, const std::set<int> &used,
                    std::vector<std::vector<int>> &runs) {
    std::set<int> follows;
    std::vector<Field> fm;
    for (int i = 0; i < p.n; i++) {
        if (!p.q[i]) continue;
        fieldmap(p.q[i], p.op[i], p.props[i], fm);
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

struct SplitMap;
static void bank_conflicts_nodes(const Program &p, const std::vector<char> &reach,
                                 const SplitMap &S, BConf &bc);

static void bank_conflicts(const Program &p, BConf &bc) {
    std::vector<Field> fm;
    for (int i = 0; i < p.n; i++) {
        if (!p.q[i]) continue;
        fieldmap(p.q[i], p.op[i], p.props[i], fm);
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

bool g_rp_colour = false;

bool g_rp_align = false;

enum ColourOrder { ORD_DEG = 0, ORD_SMALLEST_LAST, ORD_DEG_ASC, ORD_NAME,
                   ORD_NAME_DESC, ORD_N };

static void colour(const std::vector<std::vector<int>> &runs, Adj &adj,
                   const std::set<int> &pinned, const BConf *bconf, int limit,
                   std::unordered_map<int, int> &cmap, int corder = ORD_DEG);

static void colour(const std::vector<std::vector<int>> &runs, Adj &adj,
                   const std::set<int> &pinned, const BConf *bconf, int limit,
                   std::unordered_map<int, int> &cmap, int corder) {
    const int align_mod = 4;
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
            int r = run[k], bank = (base + (int)k) & 3;
            auto it = bcadj.find(r);
            if (it == bcadj.end()) continue;
            for (const auto &pc : it->second) {
                auto ct = cmap.find(pc.first);
                if (ct != cmap.end() && (ct->second & 3) == bank) n += pc.second;
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

    for (size_t idx : order) {
        const std::vector<int> &run = runs[idx];
        if (pin[idx]) {
            for (int r : run)
                if (!pinned.count(r)) fail("run is only partly pinned");
            if (!fits(run, run[0])) fail("pinned run does not fit at its own base");
            place(run, run[0]);
            continue;
        }
        int step = constrained[idx] ? align_mod : 1;
        int start = constrained[idx] ? (run[0] % align_mod) : 0;
        if (g_rp_align && constrained[idx]) {

            int a = (run[0] % 4 == 0) ? 4 : ((run[0] % 2 == 0) ? 2 : 1);
            step = a; start = 0;
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

bool g_rp_split = false;
bool g_rp_force = false;

int g_rp_offered_n = 0, g_rp_kept_n = 0, g_rp_occ_n = 0;

int occupancy_of(int regs) {
    if (regs <= 0) return 64;
    int per = ((regs * 32 + 255) / 256) * 256;
    int w = (65536 / per) / 4 * 4;
    return w > 64 ? 64 : w;
}

extern bool g_grow;
extern int  g_grow_k;
int grow_limit(int lim) {
    if (!g_grow || lim <= 0) return lim;
    int w = occupancy_of(lim), hi = lim;
    while (hi < 255 && occupancy_of(hi + 1) == w) hi++;
    if (g_grow_k > 0 && hi > lim + g_grow_k) hi = lim + g_grow_k;
    return hi;
}

static const int SPLIT_NODE0 = 4096;

struct SplitMap {

    std::unordered_map<long long, int> fnode;
    std::set<int> nodes;
    int nsplit = 0, nnodes = 0;
    static long long key(int i, int off) { return (long long)i * 64 + off; }
    int at(int i, int off) const {
        auto it = fnode.find(key(i, off));
        return it == fnode.end() ? -1 : it->second;
    }
};

bool g_rp_defrelax = false;

static bool build_split(const Program &p, const CFGraph &c,
                        const std::vector<char> &reach, const Live &L,
                        const std::vector<int> &exit_live, SplitMap &S,
                        Adj &nadj) {
    const OpSets &T = ub::S();
    int n = p.n;
    std::vector<Field> fm;

    std::set<int> wide, used;
    for (int i = 0; i < n; i++) {
        if (!p.q[i] || !reach[(size_t)i]) continue;
        fieldmap(p.q[i], p.op[i], p.props[i], fm);
        fm_regs(fm, used);
        for (const Field &f : fm)
            if (f.w > 1)
                for (int k = 0; k < f.w; k++) wide.insert(f.base + k);
    }
    std::set<int> pinset(exit_live.begin(), exit_live.end());
    auto splittable = [&](int r) {
        return r < RZ && !wide.count(r) && !pinset.count(r) && used.count(r);
    };

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

    std::unordered_map<int, std::vector<int>> innode, outnode;
    std::vector<int> uf(2 * (size_t)n);
    std::function<int(int)> find = [&](int x) {
        while (uf[(size_t)x] != x) {
            uf[(size_t)x] = uf[(size_t)uf[(size_t)x]];
            x = uf[(size_t)x];
        }
        return x;
    };
    int next = SPLIT_NODE0;
    int nsplit = 0;
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
        if (rep2node.size() > 1) nsplit++;
    }
    S.nsplit = nsplit;
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
        deadnode[k] = id;
        return id;
    };
    auto usenode = [&](int i, int r) {
        if (!splittable(r)) return r;
        int v = innode[r][(size_t)i];
        if (v < 0) fail("split: use of R%d at %d is not live-in", r, i);
        return v;
    };

    for (int i = 0; i < n; i++) {
        if (!p.q[i] || !reach[(size_t)i]) continue;
        fieldmap(p.q[i], p.op[i], p.props[i], fm);
        for (const Field &f : fm) {
            int nd = (f.kind == 'd') ? defnode(i, f.base) : usenode(i, f.base);
            S.fnode[SplitMap::key(i, f.off)] = nd;

            for (int k = 0; k < f.w; k++) S.nodes.insert(nd + k);
        }
    }
    S.nnodes = (int)S.nodes.size();

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

        bool wideop = T.tex_bases[(size_t)p.op[i]] || p.op[i] == T.O_Shfl ||
                      mem_data_regs(p.q[i], p.op[i]) > 1;
        std::vector<int> dns;
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
                if (wideop || may || !g_rp_defrelax) {
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
    return true;
}

static void apply_split(const Program &p, const std::vector<char> &reach,
                        const SplitMap &S,
                        const std::unordered_map<int, int> &cmap,
                        std::vector<u64> &words) {
    words.assign((size_t)p.n, 0);
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
        u64 q = p.q[i];
        words[(size_t)i] = q;
        if (!q || !reach[(size_t)i]) continue;
        fieldmap(q, p.op[i], p.props[i], fm);
        u64 nq = q;
        defcol.clear();
        usecol.clear();
        for (const Field &f : fm) {
            int nd = S.at(i, f.off);
            if (nd < 0) fail("split: no node for field %d at %d", f.off, i);
            int nb = C(nd);
            if (nb < 0 || nb >= RZ) fail("split: colour %d out of range at %d", nb, i);
            if (f.w > 1) {

                for (int k = 1; k < f.w; k++) {
                    auto it = cmap.find(f.base + k);
                    int ck = (it == cmap.end()) ? f.base + k : it->second;
                    if (ck != nb + k) fail("split: group at %d broken", i);
                }
            }
            for (int k = 0; k < f.w; k++)
                (f.kind == 'd' ? defcol : usecol)
                    .push_back(std::make_pair(f.base + k, nb + k));
            nq = (nq & ~((u64)0xFF << f.off)) | ((u64)nb << f.off);
        }
        words[(size_t)i] = nq;

        RSet d, md, u;
        Program::du_word(nq, p.op[i], p.props[i], d, md, u);
        int spur_g = spurious_pred(p.op[i], nq);
        int spur_w = spurious_pred(p.op[i], q);
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
                         k == 2 ? "use" : "def", r, i, op_name(p.op[i]));
                mapped.add(col);
            }
            if (!(*gots[k] == mapped))
                fail("split: operand mismatch after renumbering at %d (%s)", i,
                     op_name(p.op[i]));
        }
    }
}

static void bank_conflicts_nodes(const Program &p, const std::vector<char> &reach,
                                 const SplitMap &S, BConf &bc) {
    std::vector<Field> fm;
    for (int i = 0; i < p.n; i++) {
        if (!p.q[i] || !reach[(size_t)i]) continue;
        fieldmap(p.q[i], p.op[i], p.props[i], fm);
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

static void apply_map(const Program &p, const std::unordered_map<int, int> &cmap,
                      std::vector<u64> &words) {
    words.assign((size_t)p.n, 0);
    std::vector<Field> fm;
    auto M = [&](int r) {
        auto it = cmap.find(r);
        return it == cmap.end() ? r : it->second;
    };
    for (int i = 0; i < p.n; i++) {
        u64 q = p.q[i];
        if (!q) { words[(size_t)i] = q; continue; }
        fieldmap(q, p.op[i], p.props[i], fm);
        u64 nq = q;
        for (const Field &f : fm) {
            int nb = M(f.base);
            for (int k = 0; k < f.w; k++)
                if (M(f.base + k) != nb + k)
                    fail("group at %d (%s) broken", i, op_name(p.op[i]));
            nq = (nq & ~((u64)0xFF << f.off)) | ((u64)nb << f.off);
        }
        words[(size_t)i] = nq;
    }
}

static void gate_operands(const Program &p, const std::vector<u64> &words,
                          const std::unordered_map<int, int> &cmap) {
    auto M = [&](int r) {
        if (r >= RZ) return r;
        auto it = cmap.find(r);
        return it == cmap.end() ? r : it->second;
    };
    for (int i = 0; i < p.n; i++) {
        if (!p.q[i]) continue;
        RSet d, md, u;
        Program::du_word(words[(size_t)i], p.op[i], p.props[i], d, md, u);

        int spur_g = spurious_pred(p.op[i], words[(size_t)i]);
        int spur_w = spurious_pred(p.op[i], p.q[i]);
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
                     op_name(p.op[i]));
        }
    }
}

static int maxgpr(const Program &p) {
    int mx = -1;
    for (int i = 0; i < p.n; i++) {
        if (!p.q[i]) continue;
        const RSet *s[3] = {&p.defs[i], &p.maydefs[i], &p.uses[i]};
        for (int k = 0; k < 3; k++) {
            std::vector<int> v; s[k]->list(v);
            for (int r : v) if (r < RZ && r > mx) mx = r;
        }
    }
    return mx;
}

bool g_bank = false;
bool g_bank_force = false;

bool g_anti = false;
bool g_anti_force = false;

bool g_grow = false;
bool g_grow_bank = false;

int  g_grow_k = 0;
long long g_grow_room = 0, g_grow_calls = 0;
long long g_anti_rows = 0, g_anti_kept = 0, g_anti_before = 0, g_anti_after = 0;
long long g_anti_cyc_saved = 0, g_anti_calls = 0;
long long g_bank_rows = 0, g_bank_kept = 0, g_bank_before = 0, g_bank_after = 0;
long long g_bank_us = 0, g_bank_emit_us = 0, g_bank_calls = 0;

static long long bank_cost_of(const BConf &bconf,
                              const std::unordered_map<int, int> &cmap) {
    long long n = 0;
    for (const auto &pr : bconf) {
        auto a = cmap.find(pr.first.first);
        auto b = cmap.find(pr.first.second);
        if (a == cmap.end() || b == cmap.end()) continue;

        if (a->second == b->second) continue;
        if ((a->second & 3) == (b->second & 3)) n += pr.second;
    }
    return n;
}

static long long bank_repair(const std::vector<std::vector<int>> &runs,
                             const Adj &adj, const std::set<int> &pinned,
                             const BConf &bconf, int limit,
                             std::unordered_map<int, int> &cmap) {
    if (bconf.empty() || cmap.empty()) return 0;
    long long before = bank_cost_of(bconf, cmap);
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
                if ((cp & 3) == (c & 3)) n += pw.second;
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
                    if ((cp & 3) != (cu & 3)) continue;
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
                if ((cp & 3) == (cu & 3)) n += pw.second;
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
                    if (((c1 ^ c2) & 3) == 0) continue;
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

                int step = run.size() > 1 ? 4 : 1;
                int start = run.size() > 1 ? (run[0] % 4) : 0;
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
    long long after = bank_cost_of(bconf, cmap);
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

static void build_anti(const Program &p, const std::vector<char> &reach,
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
        if (!p.q[i] || !reach[(size_t)i]) continue;
        fieldmap(p.q[i], p.op[i], p.props[i], fm);
        for (const Field &f : fm) {
            if (f.base >= RZ) continue;
            int nd = nodeof(i, f.off);
            if (nd < 0) continue;
            if (f.kind == 'd') wr[(size_t)i].push_back(nd);
            else { rd[(size_t)i].push_back(nd); nsrc[(size_t)i] += f.w; }
        }
    }
    for (int i = 0; i < n; i++) {
        if (!p.q[i] || !reach[(size_t)i]) continue;

        if (!(cls[(size_t)i] & 1)) continue;
        if (!(cls[(size_t)i] & 6)) continue;
        if (rd[(size_t)i].empty() && wr[(size_t)i].empty()) continue;
        int w = 5 + (nsrc[(size_t)i] >> 1);
        for (int j = i + 1; j < n && j - i <= WINDOW; j++) {
            if (leader[(size_t)j]) break;
            if (!p.q[j] || !reach[(size_t)j]) continue;
            for (int v : wr[(size_t)j]) {
                for (int u : rd[(size_t)i]) A.add(u, v, w);
                for (int u : wr[(size_t)i]) A.add(u, v, 5);
            }
        }
    }
}

static long long anti_repair(const std::vector<std::vector<int>> &runs,
                             const Adj &adj, const std::set<int> &pinned,
                             const AntiModel &A, int limit,
                             std::unordered_map<int, int> &cmap) {
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
            int step = run.size() > 1 ? 4 : 1;
            int start = run.size() > 1 ? (run[0] % 4) : 0;
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

bool web_map(const std::vector<u8> &bc_in, const std::vector<u8> &ct_in,
             bool fragment, std::vector<int> &wuse, std::vector<int> &wdef,
             int &nslots) {
    const OpSets &T = ub::S();
    Program p;
    p.load_bytes(bc_in, ct_in);
    CFGraph c;
    std::vector<char> reach;
    { PerfScope ps_(&g_perf.x[1]);
      c.build(p, false);
      reach = c.reachable_from_entry(); }
    std::vector<int> exit_live;
    if (fragment) exit_live_regs(bc_in, exit_live);
    Live L;
    liveness(p, c, reach, exit_live, L);

    int n = p.n;
    nslots = n;
    wuse.assign((size_t)n * WEB_STRIDE, -1);
    wdef.assign((size_t)n * WEB_STRIDE, -1);

    std::vector<Field> fm;
    std::set<int> wide, used;
    for (int i = 0; i < n; i++) {
        if (!p.q[i] || !reach[(size_t)i]) continue;
        fieldmap(p.q[i], p.op[i], p.props[i], fm);
        fm_regs(fm, used);
        for (const Field &f : fm)
            if (f.w > 1)
                for (int k = 0; k < f.w; k++) wide.insert(f.base + k);
    }
    std::set<int> pinset(exit_live.begin(), exit_live.end());
    auto splittable = [&](int r) {
        return r < RZ && !wide.count(r) && !pinset.count(r) && used.count(r);
    };

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

    std::unordered_map<int, std::vector<int>> innode, outnode;
    std::vector<int> uf(2 * (size_t)n);
    std::function<int(int)> find = [&](int x) {
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
        if (!p.q[i] || !reach[(size_t)i]) continue;
        fieldmap(p.q[i], p.op[i], p.props[i], fm);
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

static const int RN_NCTR = 18;
static void rn_counters(long long *v) {
    long long src[RN_NCTR] = {
        g_rp_offered_n, g_rp_kept_n, g_rp_occ_n,
        g_bank_rows, g_bank_kept, g_bank_before, g_bank_after,
        g_bank_us, g_bank_emit_us, g_bank_calls,
        g_anti_rows, g_anti_kept, g_anti_before, g_anti_after,
        g_anti_cyc_saved, g_anti_calls, g_grow_room, g_grow_calls};
    for (int i = 0; i < RN_NCTR; i++) v[i] = src[i];
}
static void rn_counters_add(const long long *d) {
    long long *dst[RN_NCTR] = {
        nullptr, nullptr, nullptr,
        &g_bank_rows, &g_bank_kept, &g_bank_before, &g_bank_after,
        &g_bank_us, &g_bank_emit_us, &g_bank_calls,
        &g_anti_rows, &g_anti_kept, &g_anti_before, &g_anti_after,
        &g_anti_cyc_saved, &g_anti_calls, &g_grow_room, &g_grow_calls};
    g_rp_offered_n += (int)d[0];
    g_rp_kept_n    += (int)d[1];
    g_rp_occ_n     += (int)d[2];
    for (int i = 3; i < RN_NCTR; i++) *dst[i] += d[i];
}

struct RnEntry {
    std::vector<u8> bc, ct;
    RegStats st;
    long long d[RN_NCTR];
};
static std::map<std::string, RnEntry> g_rn_cache;
void renumber_cache_clear() { g_rn_cache.clear(); }

static void renumber_uncached(std::vector<u8> &bc, std::vector<u8> &ct,
                              bool fragment, bool bank_aware, RegStats &st);

void renumber(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
              bool bank_aware, RegStats &st) {
    std::string key;
    key.reserve(bc.size() + ct.size() + 2);
    key.push_back(fragment ? 'F' : 'V');
    key.push_back(bank_aware ? 'B' : 'b');
    key.append((const char *)bc.data(), bc.size());
    key.append((const char *)ct.data(), ct.size());
    auto it = g_rn_cache.find(key);
    if (it != g_rn_cache.end()) {
        bc = it->second.bc;
        ct = it->second.ct;
        st = it->second.st;
        rn_counters_add(it->second.d);
        g_perf.n_rn_hit++;
        return;
    }
    long long c0[RN_NCTR];
    rn_counters(c0);
    renumber_uncached(bc, ct, fragment, bank_aware, st);
    RnEntry e;
    e.bc = bc;
    e.ct = ct;
    e.st = st;
    long long c1[RN_NCTR];
    rn_counters(c1);
    for (int i = 0; i < RN_NCTR; i++) e.d[i] = c1[i] - c0[i];
    g_rn_cache.emplace(std::move(key), std::move(e));
}

static void renumber_uncached(std::vector<u8> &bc, std::vector<u8> &ct,
                              bool fragment, bool bank_aware, RegStats &st) {
    Program p;
    { PerfScope ps_(&g_perf.x[0]); p.load_bytes(bc, ct); }
    u32 co = p.co;

    std::vector<u8> g_icls;
    std::vector<char> g_bbleader;
    if (g_anti) {
        int nsl = 3 * ((int)co - INSTR_START) / 32;
        if (nsl < 0) nsl = 0;
        g_icls.assign((size_t)nsl + 8, 0);
        std::vector<uint16_t> rsb((size_t)nsl + 8, 0), wsb((size_t)nsl + 8, 0);
        int got = 0;
        if (ub_inst_class(bc.data(), co, nsl, g_icls.data(), rsb.data(),
                          wsb.data(), &got) < 0 || got != nsl)
            fail("renumber: ub_inst_class returned %d for %d slots", got, nsl);
    }

    check_fieldmap(p);

    CFGraph c;
    c.build(p, false);
    std::vector<char> reach = c.reachable_from_entry();

    std::vector<int> exit_live;
    if (fragment) exit_live_regs(bc, exit_live);

    Live L;
    { PerfScope ps_(&g_perf.x[2]); liveness(p, c, reach, exit_live, L); }
    Adj adj;
    { PerfScope ps_(&g_perf.x[3]); interference(p, reach, L, adj); }

    if (g_anti) {
        g_bbleader.assign((size_t)p.n + 8, 0);
        if (p.n) g_bbleader[0] = 1;
        for (int i = 0; i < p.n; i++) {
            if (!p.q[i]) continue;
            bool falls = false;
            for (int t : c.succ[(size_t)i]) {
                if (t == i + 1) falls = true;
                else if (t >= 0 && t < p.n) g_bbleader[(size_t)t] = 1;
            }
            if ((!falls || c.succ[(size_t)i].size() > 1) && i + 1 < p.n)
                g_bbleader[(size_t)i + 1] = 1;
        }
    }

    std::set<int> used;
    std::vector<Field> fm;
    for (int i = 0; i < p.n; i++) {
        if (!p.q[i]) continue;
        fieldmap(p.q[i], p.op[i], p.props[i], fm);
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
        std::vector<u64> words;
        u32 decl = 0;
        int nruns = 0, nconstrained = 0, bank = 0, maxcol = -1;
        std::vector<u8> bc, ct;
        int cycles = 0, warps = 0;
        long long bankcost = 0;
        long long anticost = 0;
        std::unordered_map<int, int> cmap;
        bool have = false;
    };
    auto build = [&](bool usesplit, const SplitMap &S, std::set<int> &nodes,
                     Adj &cadj, Cand &out) {
        std::set<int> pin2;
        for (int r : exit_live) if (nodes.count(r)) pin2.insert(r);
        std::vector<std::vector<int>> runs;
        runs_of(p, nodes, runs);
        std::unordered_map<int, int> cmap;
        { PerfScope ps_(&g_perf.x[4]); g_perf.xn[4]++;
          colour(runs, cadj, pin2, nullptr, -1, cmap, ORD_DEG); }
        int corder = ORD_DEG;
        if (g_rp_colour) {

            for (int o = ORD_DEG + 1; o < ORD_N; o++) {
                std::unordered_map<int, int> alt;
                try {
                    colour(runs, cadj, pin2, nullptr, -1, alt, o);
                } catch (NoFit &) { continue; }
                if (maxc(alt) < maxc(cmap)) { cmap.swap(alt); corder = o; }
            }
        }
        int nbank = 0;
        BConf bconf;
        if (bank_aware || g_bank) {
            PerfScope ps_(&g_perf.x[5]);
            if (usesplit) bank_conflicts_nodes(p, reach, S, bconf);
            else bank_conflicts(p, bconf);
        }

        AntiModel amod;
        if (g_anti) {
            std::function<int(int, int)> nodeof;
            if (usesplit) nodeof = [&S](int i, int off) { return S.at(i, off); };
            else nodeof = [&p](int i, int off) {
                return (int)((p.q[(size_t)i] >> off) & 0xFF);
            };
            { PerfScope ps_(&g_perf.x[6]);
              build_anti(p, reach, g_icls, g_bbleader, nodeof, amod); }
        }
        if (bank_aware) {
            int lim = cmap.empty() ? 1 : maxc(cmap) + 1;
            std::unordered_map<int, int> cmap2;
            bool ok = true;
            try {
                PerfScope ps_(&g_perf.x[7]); g_perf.xn[7]++;
                colour(runs, cadj, pin2, &bconf, lim, cmap2, corder);
            } catch (NoFit &) { ok = false; }
            if (ok && (cmap2.empty() || maxc(cmap2) < lim)) {
                cmap.swap(cmap2);
                nbank = 1;
            }
        }

        std::unordered_map<int, int> cmap_rep;
        long long removed = 0;
        if (g_bank && !cmap.empty()) {
            auto t0 = std::chrono::steady_clock::now();
            cmap_rep = cmap;

            int blim = g_grow_bank ? grow_limit(maxc(cmap) + 1) : maxc(cmap) + 1;
            { PerfScope ps_(&g_perf.x[8]);
              removed = bank_repair(runs, cadj, pin2, bconf, blim, cmap_rep); }
            g_bank_us += std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now() - t0).count();
            g_bank_calls++;
        }
        auto emit_from = [&](std::unordered_map<int, int> &cm, Cand &o) {
            PerfScope ps_(&g_perf.x[10]); g_perf.xn[10]++;
            for (auto &pr : cadj)
                for (int b : pr.second)
                    if (cm.at(pr.first) == cm.at(b))
                        fail("invalid colouring: interfering pair shares a register");
            if (usesplit) apply_split(p, reach, S, cm, o.words);
            else {
                apply_map(p, cm, o.words);
                gate_operands(p, o.words, cm);
            }
            o.maxcol = maxc(cm);
            o.decl = (u32)std::max(o.maxcol + 1, 4);
            o.nruns = (int)runs.size();
            o.nconstrained = 0;
            for (auto &r : runs) if (r.size() > 1) o.nconstrained++;
            o.bank = nbank;
            { PerfScope ps_(&g_perf.x[13]);
              o.bankcost = bconf.empty() ? 0 : bank_cost_of(bconf, cm);
              o.anticost = amod.w.empty() ? 0 : anti_cost_of(amod, cm); }
            o.cmap = cm;
            o.bc = bc;
            o.ct = ct;
            for (int i = 0; i < p.n; i++)
                std::memcpy(o.bc.data() + INSTR_START + p.rel[(size_t)i],
                            &o.words[(size_t)i], 8);
            ctl(o.ct)->mProgramRegNum = o.decl;
            { PerfScope ps_(&g_perf.x[11]); g_perf.xn[11]++; phase_b(o.bc, co); }
            o.cycles = issue_cycles(o.bc, co);
            o.warps = occupancy_of((int)o.decl);
            o.have = true;
        };
        emit_from(cmap, out);
        if (removed > 0) {

            g_bank_rows++;
            Cand R;
            auto t1 = std::chrono::steady_clock::now();
            emit_from(cmap_rep, R);
            g_bank_emit_us += std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now() - t1).count();
            bool ok = R.warps >= out.warps && R.cycles <= out.cycles &&
                      R.bankcost < out.bankcost;
            if (g_bank_force || ok) {
                g_bank_kept++;
                g_bank_before += out.bankcost;
                g_bank_after += R.bankcost;
                out = std::move(R);
            }
        }

        if (g_anti && !amod.w.empty() && !out.cmap.empty()) {
            g_anti_calls++;
            std::unordered_map<int, int> cm2 = out.cmap;
            int alim = grow_limit(maxc(out.cmap) + 1);
            if (g_grow) { g_grow_calls++; g_grow_room += alim - (maxc(out.cmap) + 1); }
            long long got;
                { PerfScope ps_(&g_perf.x[9]);
                  got = anti_repair(runs, cadj, pin2, amod, alim, cm2); }
            if (got > 0) {
                g_anti_rows++;
                Cand R2;
                emit_from(cm2, R2);

                for (int i2 = 0; i2 < p.n; i2++) {
                    u64 m = renumber_mask(p.q[(size_t)i2]);
                    if ((R2.words[(size_t)i2] & ~m) != (out.words[(size_t)i2] & ~m))
                        fail("anti: instruction %d changed outside its register "
                             "fields (%016llx -> %016llx, mask %016llx)", i2,
                             (unsigned long long)out.words[(size_t)i2],
                             (unsigned long long)R2.words[(size_t)i2],
                             (unsigned long long)m);
                }
                bool ok2 = R2.warps >= out.warps && R2.cycles < out.cycles;
                if (g_anti_force || ok2) {
                    g_anti_kept++;
                    g_anti_before += out.anticost;
                    g_anti_after += R2.anticost;
                    g_anti_cyc_saved += out.cycles - R2.cycles;
                    out = std::move(R2);
                }
            }
        }
    };

    std::set<int> namenodes = used;
    SplitMap none;
    Cand A;
    build(false, none, namenodes, adj, A);

    Cand B;
    SplitMap S;
    Adj nadj;
    if (g_rp_split) {
        bool bs_;
        { PerfScope ps_(&g_perf.x[12]);
          bs_ = build_split(p, c, reach, L, exit_live, S, nadj); }
        if (bs_) {
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
        }
    }

    Cand *pick = &A;
    if (B.have) {
        bool better = B.warps > A.warps ||
                      (B.warps == A.warps && B.cycles <= A.cycles);
        if (g_rp_force || better) pick = &B;
        st.rp_offered = 1;
    }
    st.rp_used = (pick == &B) ? 1 : 0;
    if (B.have) {
        g_rp_offered_n++;
        if (pick == &B) g_rp_kept_n++;
        if (pick == &B && B.warps > A.warps) g_rp_occ_n++;
    }
    st.rp_webs = B.have ? (int)S.nodes.size() : 0;

    int old_maxlive = 0;
    for (int i = 0; i < p.n; i++)
        if (reach[(size_t)i])
            old_maxlive = std::max(old_maxlive, L.live[(size_t)i].popcount());
    int old_max = maxgpr(p);
    u32 old_decl = ctl(p.ct)->mProgramRegNum;

    bc.swap(pick->bc);
    ct.swap(pick->ct);

    st.old_max = old_max;
    st.new_max = pick->maxcol;
    st.old_decl = (int)old_decl;
    st.new_decl = (int)pick->decl;
    st.maxlive = old_maxlive;
    st.nregs = (int)used.size();
    st.nruns = pick->nruns;
    st.bank_pass = pick->bank;
    st.nconstrained = pick->nconstrained;
}

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

bool g_dce2 = false;
bool g_dce2_force = false;
bool g_dce2_early = false;
long long g_dce2_dead = 0, g_dce2_self = 0, g_dce2_calls = 0, g_dce2_rev = 0;

long long g_dce2_notrunc = 0, g_dce2_badtrunc = 0;

static const u64 DCE2_W_NOP = 0x50b0000000070f00ull;

static bool dce2_deletable_op(const Program &p, int i) {
    const OpSets &T = S();
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
    int nm = p.op[i];
    if (nm < 0 || !allow[(size_t)nm]) return false;
    if (T.side_effect[(size_t)nm] || T.branchy[(size_t)nm] ||
        T.pushy[(size_t)nm] || T.tex_bases[(size_t)nm] ||
        T.load_or_store[(size_t)nm]) return false;

    std::vector<int> v;
    RSet all = p.defs[i];
    all.unite(p.maydefs[i]);
    all.list(v);
    bool any = false;
    for (int r : v) {
        if (r >= PREG) return false;
        if (r < RZ) any = true;
    }
    return any;
}

static bool dce2_self_copy(const Program &p, int i) {
    if (p.op[i] != S().O_Mov) return false;
    u64 q = p.q[i];
    if (srcb_form(q) != FORM_REG) return false;
    if (((q >> 39) & 0xF) != 0xF) return false;
    if (p.guarded(i)) return false;
    int rd = (int)(q & 0xFF);
    return rd != RZ && rd == (int)((q >> 20) & 0xFF);
}

static bool dce2_reads_cc(const Program &p) {
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

static void dce2_liveout(const Program &p, const CFGraph &c,
                         const std::vector<char> &reach,
                         const std::vector<char> &killed,
                         const std::vector<int> &exit_live,
                         std::vector<Mask> &lout) {
    const OpSets &Te = S();
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
        for (int r : v) if (r < RZ) dm[(size_t)i].set(r);
        int spur = spurious_pred(p.op[i], p.q[i]);
        p.uses[i].list(v);
        for (int r : v) if (r < RZ && r != spur) um[(size_t)i].set(r);
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
            if (p.op[i] == Te.O_Exit || p.op[i] == Te.O_Ret) lo |= seed;
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
        if (p.op[i] == Te.O_Exit || p.op[i] == Te.O_Ret) lo2 |= seed;
        lout[(size_t)i] = lo2;
    }
}

static bool dce2_kill_valid(const Program &p, const CFGraph &c,
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
        RSet all = p.defs[i];
        all.unite(p.maydefs[i]);
        all.list(v);
        for (int r : v)
            if (r < RZ && lout[(size_t)i].test(r)) return false;
    }
    return true;
}

void dce2(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
          Dce2Stats &st, bool guard) {
    const OpSets &T = S();
    u32 co = const_off(ct);
    if (co > bc.size()) fail("dce2: ConstBufOffset past the file");
    int n = 3 * ((int)co - INSTR_START) / 32;
    if (n <= 0) return;
    g_dce2_calls++;

    Program p;
    p.load_bytes(bc, ct);
    if (dce2_reads_cc(p)) { st.cc_declined = 1; return; }
    CFGraph c;
    c.build(p, false);
    std::vector<char> reach = c.reachable_from_entry();
    std::vector<int> exit_live;
    if (fragment) exit_live_regs(bc, exit_live);

    std::vector<char> killed((size_t)p.n, 0);
    std::vector<Mask> lout;
    int rounds = 0, dead = 0, self = 0;
    for (int r = 0; r < 16; r++) {
        rounds++;
        dce2_liveout(p, c, reach, killed, exit_live, lout);
        bool ch = false;
        for (int i = 0; i < p.n; i++) {
            if (!reach[(size_t)i] || killed[(size_t)i] || !p.q[i]) continue;
            if (dce2_self_copy(p, i)) {
                killed[(size_t)i] = 1; self++; ch = true; continue;
            }
            if (!dce2_deletable_op(p, i)) continue;
            RSet all = p.defs[i];
            all.unite(p.maydefs[i]);
            std::vector<int> v;
            all.list(v);
            bool live = false;
            for (int rg : v)
                if (rg < RZ && lout[(size_t)i].test(rg)) { live = true; break; }
            if (live) continue;
            killed[(size_t)i] = 1; dead++; ch = true;
        }
        if (!ch) break;
    }
    st.rounds = rounds;
    if (!dead && !self) return;

    int nreal = 0;
    std::vector<u64> words((size_t)n);
    for (int k = 0; k < n; k++) {
        std::memcpy(&words[(size_t)k], bc.data() + slot_off(k), 8);
        if (words[(size_t)k]) nreal = k + 1;
    }
    size_t blobsz = bc.size() - (size_t)co;

    auto build = [&](const std::vector<char> &kill, std::vector<u8> &obc,
                     std::vector<u8> &oct, u32 *oco) -> bool {
        std::vector<int> newidx((size_t)nreal + 1, -1),
                         nextkept((size_t)nreal + 1, -1);
        std::vector<u64> out;
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
        while (out.size() % 3) { out.push_back(DCE2_W_NOP); oldof.push_back(-1); }
        for (size_t k = 0; k < oldof.size(); k++) {
            int i2 = oldof[k];
            if (i2 < 0 || i2 >= p.n || !p.q[i2]) continue;
            if (!T.branchy_imm[(size_t)p.op[i2]]) continue;
            int t = p.target(i2);
            if (t < 0 || t > nreal) fail("dce2: unresolved branch at slot %d", i2);
            int nt = nextkept[(size_t)t];
            int disp = slot_rel(nt) - (slot_rel((int)k) + 8);
            if (!branch_disp_ok(disp))
                fail("dce2: branch displacement out of range");
            out[k] = setbits(out[k], 20, 24, (u64)(u32)disp & 0xFFFFFF);
        }
        size_t nb = out.size() / 3;
        u32 co2 = (u32)(INSTR_START + nb * 32);
        co2 = (co2 + CBUF_ALIGN - 1) / CBUF_ALIGN * CBUF_ALIGN;
        obc.assign((size_t)co2 + blobsz, 0);
        std::memcpy(obc.data(), bc.data(), INSTR_START);
        for (size_t k = 0; k < out.size(); k++)
            std::memcpy(obc.data() + slot_off(k), &out[k], 8);
        if (blobsz) std::memcpy(obc.data() + co2, bc.data() + co, blobsz);
        oct = ct;
        NVNshaderControl *oc = ctl(oct);
        oc->mProgramSize = (u32)(SPH_SIZE + nb * 32);
        oc->mConstBufOffset = co2;
        oc->mShaderSize = (u32)obc.size();
        phase_b(obc, co2);
        int ns = 3 * ((int)co2 - INSTR_START) / 32;
        if (!slots_ok(ns))
            fail("dce2: padded instruction count %d is not 12 mod 24", ns);
        *oco = co2;
        return true;
    };

    std::vector<char> kill_trunc = killed;
    std::vector<char> ghost = killed;
    int extra = (dead + self) % 3, trimmed = 0;
    if (extra) {
        std::vector<int> kills;
        for (int i = 0; i < p.n; i++) if (killed[(size_t)i]) kills.push_back(i);
        std::vector<RSet> kdef((size_t)kills.size());
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
            kill_trunc = killed; ghost = killed; trimmed = 0; g_dce2_notrunc++;
        }
    }

    int before = issue_cycles(bc, co);
    std::vector<u8> bcA, ctA, bcB, ctB;
    u32 coA = 0, coB = 0;
    build(killed, bcA, ctA, &coA);
    int cycA = issue_cycles(bcA, coA);
    int cycB = cycA;
    bool useB = false;
    if (trimmed &&
        !dce2_kill_valid(p, c, reach, kill_trunc, ghost, exit_live)) {

        trimmed = 0; g_dce2_badtrunc++;
    }
    if (trimmed) {
        build(kill_trunc, bcB, ctB, &coB);
        cycB = issue_cycles(bcB, coB);
        if (cycB < cycA) useB = true;
    }
    int after = useB ? cycB : cycA;
    int ndel = (dead + self) - (useB ? trimmed : 0);

    if (guard && !g_dce2_force && after > before) {
        st.reverted = 1; g_dce2_rev++; return;
    }

    st.dead = dead;
    st.self = self;
    st.trimmed = useB ? trimmed : 0;
    st.deleted = ndel;
    st.cycles_saved = before - after;
    g_dce2_dead += dead;
    g_dce2_self += self;
    if (useB) { bc.swap(bcB); ct.swap(ctB); }
    else { bc.swap(bcA); ct.swap(ctA); }
}

bool g_texnarrow = false;
long long g_texnarrow_sites = 0, g_texnarrow_progs = 0, g_texnarrow_calls = 0;

static const int TN_LUT[2][8] = {
    {0x1, 0x2, 0x4, 0x8, 0x3, 0x9, 0xA, 0xC},
    {0x7, 0xB, 0xD, 0xE, 0xF, 0x0, 0x0, 0x0}};

static int tn_pc(int m) { int c = 0; while (m) { c += m & 1; m >>= 1; } return c; }

static int tn_prefix(int m, int n) {
    int r = 0;
    for (int b = 0; b < 4 && n; b++) if (m & (1 << b)) { r |= 1 << b; n--; }
    return r;
}

struct TnShape {
    bool texs = false;
    int ch = 0;
    int n = 0;
    int reg[4] = {RZ, RZ, RZ, RZ};
};

static bool tn_shape(const Program &p, int i, TnShape &s) {
    const OpSets &T = S();
    int nm = p.op[i];
    if (nm < 0) return false;
    const char *nv = op_name(nm);
    u64 q = p.q[i];
    if (T.texs_fam[(size_t)nm]) {
        if (std::strcmp(nv, "Texs") && std::strcmp(nv, "Tlds")) return false;
        int dest = (int)(q & 0xFF), dest2 = (int)((q >> 28) & 0xFF);
        int ch = TN_LUT[dest2 == RZ ? 0 : 1][(q >> 50) & 7];
        if (!ch || dest == RZ) return false;
        s.texs = true; s.ch = ch; s.n = tn_pc(ch);
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
        s.texs = false; s.ch = ch; s.n = tn_pc(ch);
        for (int k = 0; k < s.n; k++)
            s.reg[k] = (dest + k < RZ) ? dest + k : RZ;
        return true;
    }
    return false;
}

static bool tn_encode(const TnShape &s, int keep, u64 &q) {
    int nch = tn_prefix(s.ch, keep);
    if (!nch) return false;
    if (!s.texs) {
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

void texnarrow(std::vector<u8> &bc, const std::vector<u8> &ct, bool fragment,
               TexNarrowStats &st) {
    u32 co = const_off(ct);
    if (co > bc.size()) fail("texnarrow: ConstBufOffset past the file");
    if (3 * ((int)co - INSTR_START) / 32 <= 0) return;
    g_texnarrow_calls++;

    Program p;
    p.load_bytes(bc, ct);
    CFGraph c;
    c.build(p, false);
    std::vector<char> reach = c.reachable_from_entry();
    std::vector<int> exit_live;
    if (fragment) exit_live_regs(bc, exit_live);

    std::vector<char> ghost((size_t)p.n, 0);
    if (!dce2_reads_cc(p)) {
        std::vector<Mask> gl;
        for (int rnd = 0; rnd < 16; rnd++) {
            dce2_liveout(p, c, reach, ghost, exit_live, gl);
            bool ch = false;
            for (int i = 0; i < p.n; i++) {
                if (!reach[(size_t)i] || ghost[(size_t)i] || !p.q[i]) continue;
                if (dce2_self_copy(p, i)) {
                    ghost[(size_t)i] = 1; st.selfcopies++; ch = true; continue;
                }
                if (!dce2_deletable_op(p, i)) continue;
                RSet all = p.defs[i]; all.unite(p.maydefs[i]);
                std::vector<int> v; all.list(v);
                bool live = false;
                for (int rg : v)
                    if (rg < RZ && gl[(size_t)i].test(rg)) { live = true; break; }
                if (live) continue;
                ghost[(size_t)i] = 1; st.deadops++; ch = true;
            }
            if (!ch) break;
        }
        if (!dce2_kill_valid(p, c, reach, ghost, ghost, exit_live)) {

            st.ghostRejected = 1;
            st.selfcopies = st.deadops = 0;
            std::fill(ghost.begin(), ghost.end(), (char)0);
            for (int i = 0; i < p.n; i++)
                if (reach[(size_t)i] && p.q[i] && dce2_self_copy(p, i)) {
                    ghost[(size_t)i] = 1; st.selfcopies++;
                }
        }
    }
    std::vector<Mask> lout;
    dce2_liveout(p, c, reach, ghost, exit_live, lout);

    for (int i = 0; i < p.n; i++) {
        if (!reach[(size_t)i] || !p.q[i]) continue;
        TnShape s;
        if (!tn_shape(p, i, s)) {

            const OpSets &T = S();
            if (T.tex_bases[(size_t)p.op[i]]) {
                RSet all = p.defs[i]; all.unite(p.maydefs[i]);
                std::vector<int> v; all.list(v);
                for (int r : v)
                    if (r < RZ && !lout[(size_t)i].test(r)) { st.unmodelled++; break; }
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
        st.sites++;
        if (keep == 0) { st.allDead++; continue; }
        u64 q = p.q[i];
        if (!tn_encode(s, keep, q)) { st.declined++; continue; }
        std::memcpy(bc.data() + INSTR_START + p.rel[i], &q, 8);
        st.narrowed++;
        st.comps += s.n - keep;
    }
    if (!st.narrowed) return;

    for (int i = 0; i < p.n; i++) {
        if (!ghost[(size_t)i]) continue;
        std::memcpy(bc.data() + INSTR_START + p.rel[i], &DCE2_W_NOP, 8);
        st.nopped++;
    }
    g_texnarrow_sites += st.narrowed;
    g_texnarrow_progs++;
}

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

    int max_gpr = -1, n_real = 0;
    bool kills = false, dls = false, dgs = false, fp64 = false;
    int local_max_byte = 0, local_count = 0;
    bool local_indexed = false;
    std::vector<int> tex_order;
    int bindless = 0, back_edges = 0;
    std::vector<int> regs;

    for (int i = 0; i < p.n; i++) {
        int nm = p.op[i];
        if (nm == T.O_Invalid) continue;
        n_real++;
        real_gprs(p, i, regs);
        for (int r : regs) if (r < 255 && r > max_gpr) max_gpr = r;
        if (nm == T.O_Kil) kills = true;
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
    f.max_gpr = max_gpr;
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
    f.back_edges = back_edges;
    f.max_stack_depth = depth;
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

void pressure_facts(const std::vector<u8> &bc, const std::vector<u8> &ct,
                    PressFacts &f) {
    Program p;
    p.load_bytes(bc, ct);
    CFGraph c;
    c.build(p, false);
    std::vector<char> reach = c.reachable_from_entry();
    std::vector<int> exit_live;
    exit_live_regs(bc, exit_live);
    Live L;
    liveness(p, c, reach, exit_live, L);
    f = PressFacts();
    for (int i = 0; i < p.n; i++) {
        if (!reach[(size_t)i]) continue;
        f.npts++;
        int pc = L.live[(size_t)i].popcount();
        if (pc > f.maxlive) f.maxlive = pc;
        if (pc > 48) f.over48++;
        if (pc > 56) f.over56++;
    }

    std::set<int> used;
    std::vector<int> ureg;
    for (int i = 0; i < p.n; i++) {
        if (!p.q[i] || !reach[(size_t)i]) continue;
        RSet u = p.defs[i];
        u.unite(p.maydefs[i]);
        u.unite(p.uses[i]);
        u.list(ureg);
        for (int r : ureg) if (r < RZ) used.insert(r);
    }
    f.nnames = (int)used.size();
    int n = p.n;

    Mask pseed;
    for (int r : exit_live) pseed.set(r);
    std::vector<Mask> lout((size_t)n);
    for (int i = 0; i < n; i++) {
        if (!reach[(size_t)i]) continue;
        if (c.succ[(size_t)i].empty()) lout[(size_t)i] = pseed;
        else
            for (int t : c.succ[(size_t)i])
                if (reach[(size_t)t]) lout[(size_t)i] |= L.live[(size_t)t];
        if (p.op[i] == S().O_Exit || p.op[i] == S().O_Ret)
            lout[(size_t)i] |= pseed;
    }
    std::vector<int> uf(2 * (size_t)n);
    std::function<int(int)> find = [&](int x) {
        while (uf[(size_t)x] != x) { uf[(size_t)x] = uf[(size_t)uf[(size_t)x]];
                                     x = uf[(size_t)x]; }
        return x;
    };
    for (int r : used) {
        if (r >= RZ) continue;
        for (int i = 0; i < 2 * n; i++) uf[(size_t)i] = i;
        std::vector<char> has(2 * (size_t)n, 0);
        for (int i = 0; i < n; i++) {
            if (!reach[(size_t)i]) continue;
            bool lo = lout[(size_t)i].test(r);
            bool ln = L.live[(size_t)i].test(r);
            has[(size_t)(2 * i)] = ln;
            has[(size_t)(2 * i + 1)] = lo;
            bool killed = L.dmask[(size_t)i].test(r) && !p.maydefs[i].has(r);
            if (ln && lo && !killed) {
                int a = find(2 * i), b = find(2 * i + 1);
                if (a != b) uf[(size_t)b] = a;
            }
        }
        for (int i = 0; i < n; i++) {
            if (!reach[(size_t)i] || !has[(size_t)(2 * i + 1)]) continue;
            for (int t : c.succ[(size_t)i]) {
                if (!reach[(size_t)t] || !has[(size_t)(2 * t)]) continue;
                int a = find(2 * i + 1), b = find(2 * t);
                if (a != b) uf[(size_t)b] = a;
            }
        }
        std::set<int> comps;
        for (int i = 0; i < 2 * n; i++) if (has[(size_t)i]) comps.insert(find(i));
        f.nwebs += comps.empty() ? 1 : (int)comps.size();
    }
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
}

}
