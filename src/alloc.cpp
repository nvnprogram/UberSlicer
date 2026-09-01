
#include "alloc.h"

namespace ub {

typedef std::vector<u64> BV;

static inline void bv_set(BV &b, size_t nw, int k) {
    if (b.size() < nw) b.resize(nw, 0);
    b[(size_t)(k >> 6)] |= (u64)1 << (k & 63);
}
static inline bool bv_inter(const BV &a, const BV &b) {
    size_t n = std::min(a.size(), b.size());
    for (size_t i = 0; i < n; i++) if (a[i] & b[i]) return true;
    return false;
}
static inline void bv_or(BV &a, const BV &b) {
    if (a.size() < b.size()) a.resize(b.size(), 0);
    for (size_t i = 0; i < b.size(); i++) a[i] |= b[i];
}
static inline BV bv_and(const BV &a, const BV &b) {
    BV r(std::min(a.size(), b.size()));
    for (size_t i = 0; i < r.size(); i++) r[i] = a[i] & b[i];
    return r;
}
static inline bool bv_any(const BV &a) {
    for (u64 x : a) if (x) return true;
    return false;
}

bool g_idfold = false;

int idfold_src(const Spec &sp, const RunRes &R, int i) {
    const Program &p = *sp.p;
    u64 q = p.q[i];
    if (sp.norw[(size_t)i]) return -1;

    if (!R.fmac.empty() && R.fmac[(size_t)i] >= 0) return -1;
    if (srcb_form(q) != FORM_REG) return -1;
    int d = (int)(q & 0xFF), ra = (int)((q >> 8) & 0xFF), rb = (int)((q >> 20) & 0xFF);
    if (d == RZ) return -1;

    u32 hi = (u32)(q >> 32);
    if (hi == 0x5C581000u) {
        if (ra == RZ && rb != RZ && rb != d) return rb;
        if (rb == RZ && ra != RZ && ra != d) return ra;
        return -1;
    }

    if (hi == 0x5C681000u) {
        if (ra == RZ || rb == RZ) return -1;
        const u32 *v;
        if (rb != d && (v = vmap_get(R.vals[(size_t)i], rb)) && *v == 0x3F800000u)
            return ra;
        if (ra != d && (v = vmap_get(R.vals[(size_t)i], ra)) && *v == 0x3F800000u)
            return rb;
        return -1;
    }
    return -1;
}

void allocate(Spec &sp, const RunRes &R, Alloc &al) {
    const Program &p = *sp.p;
    int n = p.n;
    al.kept = R.kept;
    al.K = (int)al.kept.size();
    if (al.K == 0) fail("nothing kept");
    for (int k = 0; k < al.K; k++) al.ordn[al.kept[(size_t)k]] = k;
    std::vector<char> keptset((size_t)n, 0);
    for (int i : al.kept) keptset[(size_t)i] = 1;
    size_t nw = al.words();

    al.lout.assign((size_t)al.K, Mask());
    for (int k = 0; k < al.K; k++) {
        int i = al.kept[(size_t)k];
        Mask m;
        for (int t : R.succ[(size_t)i]) m |= R.live_in[(size_t)t];
        if (sp.cat[(size_t)i] == C_EXIT) m |= sp.exit_mask;
        al.lout[(size_t)k] = m;
    }

    std::vector<std::set<int>> nk((size_t)n);
    std::vector<char> nk_has((size_t)n, 0);
    std::vector<int> order(R.reach.rbegin(), R.reach.rend());
    for (int round = 0; round < 64; round++) {
        bool ch = false;
        for (int i : order) {
            if (keptset[(size_t)i]) continue;
            std::set<int> m;
            for (int t : R.succ[(size_t)i]) {
                if (keptset[(size_t)t]) m.insert(t);
                else if (nk_has[(size_t)t])
                    m.insert(nk[(size_t)t].begin(), nk[(size_t)t].end());
            }
            if (!nk_has[(size_t)i] || m != nk[(size_t)i]) {
                nk[(size_t)i] = m;
                nk_has[(size_t)i] = 1;
                ch = true;
            }
        }
        if (!ch) break;
    }
    al.succ_k.assign((size_t)al.K, {});
    for (int k = 0; k < al.K; k++) {
        int i = al.kept[(size_t)k];
        std::set<int> m;
        for (int t : R.succ[(size_t)i]) {
            if (keptset[(size_t)t]) m.insert(t);
            else if (nk_has[(size_t)t])
                m.insert(nk[(size_t)t].begin(), nk[(size_t)t].end());
        }
        al.succ_k[(size_t)k].assign(m.begin(), m.end());
    }

    al.uses.assign((size_t)al.K, {});
    al.hard.assign((size_t)al.K, {});
    al.soft.assign((size_t)al.K, {});
    for (int k = 0; k < al.K; k++) {
        int i = al.kept[(size_t)k];
        R.gen[(size_t)i].bits(al.uses[(size_t)k]);
        R.kill[(size_t)i].bits(al.hard[(size_t)k]);
        Mask s = sp.dall_mask[(size_t)i];
        s.andnot(R.kill[(size_t)i]);
        s.bits(al.soft[(size_t)k]);
    }

    std::unordered_map<long long, int> did;
    al.did_key.clear();
    auto D = [&](int i, int r) {
        long long key = ((long long)(i + 1) << 11) + r;
        auto it = did.find(key);
        if (it != did.end()) return it->second;
        int d = (int)did.size() + 1;
        did.emplace(key, d);
        al.did_key.push_back(std::make_pair(i, r));
        return d;
    };
    auto E = [&](int r) { return D(-1, r); };

    std::set<int> entry;
    if (keptset[0]) entry.insert(0);
    else if (nk_has[0]) entry.insert(nk[0].begin(), nk[0].end());
    if (entry.empty()) entry.insert(al.kept[0]);

    al.st_in.assign((size_t)al.K, DefMap());
    al.st_out.assign((size_t)al.K, DefMap());
    std::vector<int> tmp;
    for (int e : entry) {
        int ke = al.ordn.at(e);
        R.live_in[(size_t)e].bits(tmp);
        for (int r : tmp) al.st_in[(size_t)ke][r] = E(r);
    }

    UF &uf = al.uf;
    auto transfer = [&](int k, const DefMap &s, DefMap &o) {
        o = s;
        for (int r : al.uses[(size_t)k]) if (!o.count(r)) o[r] = E(r);
        int i = al.kept[(size_t)k];
        for (int r : al.soft[(size_t)k]) {
            auto it = o.find(r);
            int nd = D(i, r);
            if (it != o.end()) o[r] = uf.unite(it->second, nd);
            else o[r] = nd;
        }
        for (int r : al.hard[(size_t)k]) o[r] = D(i, r);
    };

    {

        std::vector<int> kidx((size_t)n, -1);
        for (int k = 0; k < al.K; k++) kidx[(size_t)al.kept[(size_t)k]] = k;
        std::vector<int> dq(entry.begin(), entry.end());
        size_t head = 0;
        std::vector<char> inq((size_t)n, 0);
        for (int e : entry) inq[(size_t)e] = 1;
        DefMap o;
        while (head < dq.size()) {
            int i = dq[head++];
            inq[(size_t)i] = 0;
            int k = kidx[(size_t)i];
            DefMap &s = al.st_in[(size_t)k];
            for (int r : al.uses[(size_t)k]) if (!s.count(r)) s[r] = E(r);
            transfer(k, s, o);
            for (int t : al.succ_k[(size_t)k]) {
                int kt = kidx[(size_t)t];
                DefMap &tg = al.st_in[(size_t)kt];
                bool ch = false;
                for (auto &pr : o) {
                    auto it = tg.find(pr.first);
                    if (it == tg.end()) { tg[pr.first] = pr.second; ch = true; }
                    else if (uf.find(it->second) != uf.find(pr.second)) {
                        uf.unite(it->second, pr.second);
                        ch = true;
                    }
                }
                if (ch && !inq[(size_t)t]) { dq.push_back(t); inq[(size_t)t] = 1; }
            }
            if (head > 4096 && head * 2 > dq.size()) {
                dq.erase(dq.begin(), dq.begin() + (long)head);
                head = 0;
            }
        }
    }

    for (int k = 0; k < al.K; k++)
        transfer(k, al.st_in[(size_t)k], al.st_out[(size_t)k]);

    al.undefined_uses = 0;
    al.max_live = 0;
    for (int k = 0; k < al.K; k++) {
        DefMap &s = al.st_out[(size_t)k];
        al.lout[(size_t)k].bits(tmp);
        int cnt = 0;
        for (int r : tmp) {
            auto it = s.find(r);
            int d;
            if (it == s.end()) { d = E(r); s[r] = d; al.undefined_uses++; }
            else d = it->second;
            int w = uf.find(d);
            bv_set(al.livepts[w], nw, k);
            if (!(r >= PREG && r < LMBIT)) cnt++;
        }
        if (cnt > al.max_live) al.max_live = cnt;
    }

    for (int k = 0; k < al.K; k++) {
        int i = al.kept[(size_t)k];
        if (!sp.norw[(size_t)i]) continue;
        for (int r : al.uses[(size_t)k]) {
            auto it = al.st_in[(size_t)k].find(r);
            if (it != al.st_in[(size_t)k].end())
                al.constrained.insert(uf.find(it->second));
        }
        for (int pass = 0; pass < 2; pass++) {
            const std::vector<int> &L = pass ? al.soft[(size_t)k] : al.hard[(size_t)k];
            for (int r : L) {
                auto it = al.st_out[(size_t)k].find(r);
                if (it != al.st_out[(size_t)k].end())
                    al.constrained.insert(uf.find(it->second));
            }
        }
    }

    const OpSets &T = S();
    for (int k = 0; k < al.K; k++) {
        int i = al.kept[(size_t)k];
        if (R.guard[(size_t)i] != TRI_T) continue;
        int nm = p.op[i];
        u64 q = p.q[i];
        if (nm == T.O_Mov && srcb_form(q) == FORM_REG) {
            int d = (int)(q & 0xFF), s = (int)((q >> 20) & 0xFF);
            if (d == RZ || s == RZ || d == s) continue;
            auto eit = R.env[(size_t)i].find(s);
            int32_t a = (eit != R.env[(size_t)i].end()) ? eit->second : s;
            if (a < 0 || a == RZ) continue;
            auto sit = al.st_in[(size_t)k].find(a);
            auto dit = al.st_out[(size_t)k].find(d);
            if (sit == al.st_in[(size_t)k].end() || dit == al.st_out[(size_t)k].end())
                continue;
            al.copies.push_back({i, uf.find(dit->second), uf.find(sit->second), 0});
        } else if (g_idfold && idfold_src(sp, R, i) >= 0) {

            int s = idfold_src(sp, R, i);
            int d = (int)(q & 0xFF);
            auto eit = R.env[(size_t)i].find(s);
            int32_t a = (eit != R.env[(size_t)i].end()) ? eit->second : s;
            if (a < 0 || a == RZ) continue;
            auto sit = al.st_in[(size_t)k].find(a);
            auto dit = al.st_out[(size_t)k].find(d);
            if (sit == al.st_in[(size_t)k].end() || dit == al.st_out[(size_t)k].end())
                continue;
            al.copies.push_back({i, uf.find(dit->second), uf.find(sit->second), 2});
        } else if (sp.lm[(size_t)i].valid && sp.lm_live) {
            int off = sp.lm[(size_t)i].off, w = sp.lm[(size_t)i].w;
            bool is_store = sp.lm[(size_t)i].store;
            if (w != 1) continue;
            const int *sd = nullptr, *dd_ = nullptr;
            int sdv = 0, ddv = 0;
            bool have_s = false, have_d = false;
            if (is_store) {
                int s = (int)(q & 0xFF);
                if (s == RZ) continue;
                auto eit = R.env[(size_t)i].find(s);
                int32_t a = (eit != R.env[(size_t)i].end()) ? eit->second : s;
                if (a < 0 || a == RZ) continue;
                auto sit = al.st_in[(size_t)k].find(a);
                auto dit = al.st_out[(size_t)k].find(LMBIT + off);
                if (sit != al.st_in[(size_t)k].end()) { sdv = sit->second; have_s = true; }
                if (dit != al.st_out[(size_t)k].end()) { ddv = dit->second; have_d = true; }
            } else {
                int d = (int)(q & 0xFF);
                if (d == RZ) continue;
                auto sit = al.st_in[(size_t)k].find(LMBIT + off);
                auto dit = al.st_out[(size_t)k].find(d);
                if (sit != al.st_in[(size_t)k].end()) { sdv = sit->second; have_s = true; }
                if (dit != al.st_out[(size_t)k].end()) { ddv = dit->second; have_d = true; }
            }
            (void)sd; (void)dd_;
            if (!have_s || !have_d) continue;
            al.copies.push_back({i, uf.find(ddv), uf.find(sdv), 1});
        }
    }

    al.ndid = (int)did.size();
    for (int d = 1; d <= al.ndid; d++) al.base_root[d] = uf.find(d);

    int n_spill_left = 0, wide_extra = 0;
    for (int i : al.kept) {
        if (p.op[i] != T.O_Stl && p.op[i] != T.O_Ldl) continue;
        n_spill_left++;
        if (sp.lm[(size_t)i].valid) wide_extra += sp.lm[(size_t)i].w - 1;
    }
    al.n_after = al.K + wide_extra;
}

void webreg(Spec &sp, Alloc &al, std::unordered_map<int, int> &wr) {
    (void)sp;
    wr.clear();
    for (int k = 0; k < al.K; k++) {
        for (int pass = 0; pass < 2; pass++) {
            const DefMap &tbl = pass ? al.st_out[(size_t)k] : al.st_in[(size_t)k];
            for (auto &pr : tbl) {
                int w = al.uf.find(pr.second);
                auto it = wr.find(w);
                if (it == wr.end()) wr[w] = pr.first;
                else if (it->second != pr.first)
                    fail("web %d names both %d and %d", w, it->second, pr.first);
            }
        }
    }
}

static void lm_blocked(Spec &sp, Alloc &al, std::set<int> &blocked) {
    std::set<int> copy_at;
    for (const Copy &c : al.copies) if (c.kind == 1) copy_at.insert(c.i);
    for (int k = 0; k < al.K; k++) {
        int i = al.kept[(size_t)k];
        if (!sp.lm[(size_t)i].valid) continue;
        int off = sp.lm[(size_t)i].off, w = sp.lm[(size_t)i].w;
        std::set<int> webs;
        for (int j = 0; j < w; j++) {
            for (int pass = 0; pass < 2; pass++) {
                const DefMap &tbl = pass ? al.st_out[(size_t)k] : al.st_in[(size_t)k];
                auto it = tbl.find(LMBIT + off + j);
                if (it != tbl.end()) webs.insert(al.uf.find(it->second));
            }
        }
        if (!copy_at.count(i)) blocked.insert(webs.begin(), webs.end());
    }
}

static void web_values(Spec &sp, Alloc &al,
                       std::unordered_map<int, int> &nval,
                       std::unordered_map<int, BV> &defpts) {
    size_t nw = al.words();
    for (int d = 1; d <= al.ndid; d++) nval[al.uf.find(d)]++;
    std::vector<int> tmp;
    for (int k = 0; k < al.K; k++) {
        int i = al.kept[(size_t)k];
        sp.dall_mask[(size_t)i].bits(tmp);
        for (int r : tmp) {
            auto it = al.st_out[(size_t)k].find(r);
            if (it != al.st_out[(size_t)k].end())
                bv_set(defpts[al.uf.find(it->second)], nw, k);
        }
    }
}

void post_coalesce(Spec &sp, const RunRes &R, Alloc &al,
                   std::unordered_map<int, int> &wr,
                   std::set<int> &removed,
                   std::unordered_map<int, int> &lmparent) {
    (void)R;
    lmparent.clear();

    std::set<int> extra;
    std::vector<int> tmp;
    for (int k = 0; k < al.K; k++) {
        int i = al.kept[(size_t)k];
        if (!sp.tex_rw[(size_t)i]) continue;
        sp.dall_mask[(size_t)i].bits(tmp);
        for (int r : tmp) {
            auto it = al.st_out[(size_t)k].find(r);
            if (it != al.st_out[(size_t)k].end())
                extra.insert(al.uf.find(it->second));
        }
    }
    bool has_lm = false;
    for (const Copy &c : al.copies) if (c.kind == 1) { has_lm = true; break; }
    if (!has_lm) {
        for (int w : extra) al.constrained.insert(w);
        return;
    }

    std::set<int> constrained = extra;
    for (int w : al.constrained) constrained.insert(w);

    std::set<int> blocked;
    lm_blocked(sp, al, blocked);
    std::unordered_map<int, int> nval;
    std::unordered_map<int, BV> defpts;
    web_values(sp, al, nval, defpts);

    std::unordered_map<int, BV> livepts = al.livepts;
    std::unordered_map<int, int> parent;
    std::unordered_map<int, int> reg = wr;
    std::unordered_map<int, std::set<int>> byreg;
    for (auto &pr : reg) if (pr.second < PREG) byreg[pr.second].insert(pr.first);

    std::function<int(int)> find = [&](int w) {
        for (;;) {
            auto it = parent.find(w);
            if (it == parent.end() || it->second == w) return w;
            w = it->second;
        }
    };
    auto gpr = [&](int w) -> int {
        auto it = reg.find(w);
        if (it != reg.end() && it->second < PREG) return it->second;
        return -1;
    };

    std::vector<char> pinned_name(PREG, 0);
    BV exitpts;
    {
        std::vector<int> em;
        sp.exit_mask.bits(em);
        for (int r : em) if (r >= 0 && r < PREG) pinned_name[(size_t)r] = 1;
        size_t nw = al.words();
        for (int k = 0; k < al.K; k++)
            if (sp.cat[(size_t)al.kept[(size_t)k]] == C_EXIT)
                bv_set(exitpts, nw, k);
    }

    std::vector<int> group_order;
    std::unordered_map<int, std::vector<Copy>> groups;
    for (const Copy &c : al.copies) {
        if (c.kind != 1) continue;
        int a = c.dw, b = c.sw;
        int lmw = (gpr(a) < 0) ? a : b;
        if (!groups.count(lmw)) group_order.push_back(lmw);
        groups[lmw].push_back(c);
    }

    for (int lmw : group_order) {
        const std::vector<Copy> &members = groups[lmw];
        if (blocked.count(lmw) || constrained.count(lmw)) continue;
        auto s_parent = parent;
        auto s_livepts = livepts;
        auto s_reg = reg;
        auto s_byreg = byreg;
        auto s_removed = removed;
        bool ok = true;
        for (const Copy &c : members) {
            int a = find(c.dw), b = find(c.sw);
            if (a == b) { removed.insert(c.i); continue; }
            int ra = gpr(a), rb = gpr(b);
            if (ra < 0 && rb < 0) { ok = false; break; }
            int keep = (rb >= 0) ? b : a;
            int drop = (rb >= 0) ? a : b;
            if (constrained.count(drop)) { ok = false; break; }
            int rk = reg.at(keep);

            int rdrop = (rb >= 0) ? ra : rb;
            if (rdrop >= 0 && rdrop != rk && pinned_name[(size_t)rdrop]) {
                auto lit = livepts.find(drop);
                if (lit != livepts.end() && bv_inter(lit->second, exitpts)) {
                    ok = false; break;
                }
            }
            BV lk = livepts.count(keep) ? livepts[keep] : BV();
            BV ld = livepts.count(drop) ? livepts[drop] : BV();
            if (bv_inter(lk, ld)) {
                BV ovl = bv_and(lk, ld);
                int oi = al.ordn.at(c.i);
                if ((size_t)(oi >> 6) < ovl.size())
                    ovl[(size_t)(oi >> 6)] &= ~((u64)1 << (oi & 63));
                BV dp;
                if (defpts.count(keep)) bv_or(dp, defpts[keep]);
                if (defpts.count(drop)) bv_or(dp, defpts[drop]);
                int nk_ = nval.count(keep) ? nval[keep] : 9;
                int nd_ = nval.count(drop) ? nval[drop] : 9;
                if (!(nk_ == 1 && nd_ == 1 && !bv_inter(ovl, dp))) { ok = false; break; }
            }
            bool clash = false;
            auto bit = byreg.find(rk);
            if (bit != byreg.end()) {
                for (int cw : bit->second) {
                    int cf = find(cw);
                    if (cf == keep || cf == drop) continue;
                    if (livepts.count(cf) && bv_inter(livepts[cf], ld)) { clash = true; break; }
                }
            }
            if (clash) { ok = false; break; }
            parent[drop] = keep;
            bv_or(lk, ld);
            livepts[keep] = lk;
            livepts.erase(drop);
            byreg[rk].insert(keep);
            removed.insert(c.i);
        }
        if (!ok) {
            parent.swap(s_parent);
            livepts.swap(s_livepts);
            reg.swap(s_reg);
            byreg.swap(s_byreg);
            removed.swap(s_removed);
        }
    }

    std::unordered_map<int, std::set<int>> perreg;
    for (auto &pr : reg) {
        int f = find(pr.first);
        auto it = reg.find(f);
        int r = (it != reg.end()) ? it->second : pr.second;
        if (r < PREG) perreg[r].insert(f);
    }
    int viol = 0;
    for (auto &pr : perreg) {
        std::vector<int> ws(pr.second.begin(), pr.second.end());
        for (size_t x = 0; x < ws.size(); x++)
            for (size_t y = x + 1; y < ws.size(); y++) {
                const BV *A = livepts.count(ws[x]) ? &livepts[ws[x]] : nullptr;
                const BV *B = livepts.count(ws[y]) ? &livepts[ws[y]] : nullptr;
                if (A && B && bv_inter(*A, *B)) viol++;
            }
    }
    if (viol)
        fail("lm coalescing produced %d overlapping same-register web pairs", viol);

    for (auto &pr : parent) lmparent[pr.first] = find(pr.first);
    (void)bv_any;
}

bool g_copyprop_nopin = false;

int copy_coalesce(Spec &sp, Alloc &al, std::unordered_map<int, int> &wr,
                  std::set<int> &removed,
                  std::unordered_map<int, int> &lmparent, CopyStats &cs,
                  int kinds) {
    const OpSets &T = S();
    const Program &p = *sp.p;
    int n_merged_here = 0;

    std::set<int> constrained = al.constrained;
    {
        std::vector<int> tmp;
        for (int k = 0; k < al.K; k++) {
            int i = al.kept[(size_t)k];
            if (!sp.tex_dstgroup[(size_t)i]) continue;
            sp.dall_mask[(size_t)i].bits(tmp);
            for (int r : tmp) {
                auto it = al.st_out[(size_t)k].find(r);
                if (it != al.st_out[(size_t)k].end())
                    constrained.insert(al.uf.find(it->second));
            }
        }
    }

    std::unordered_map<int, int> parent = lmparent;
    std::function<int(int)> find = [&](int w) {
        for (;;) {
            auto it = parent.find(w);
            if (it == parent.end() || it->second == w) return w;
            w = it->second;
        }
    };

    std::unordered_map<int, BV> livepts;
    for (auto &pr : al.livepts) {
        int r = find(pr.first);
        BV &dst = livepts[r];
        bv_or(dst, pr.second);
    }

    auto gpr = [&](int w) -> int {
        auto it = wr.find(w);
        if (it != wr.end() && it->second < PREG) return it->second;
        return -1;
    };
    std::unordered_map<int, std::set<int>> byreg;
    for (auto &pr : wr) {
        int r = find(pr.first);
        int g = gpr(r);
        if (g >= 0) byreg[g].insert(r);
    }

    {
        std::set<int> c2;
        for (int w : constrained) c2.insert(find(w));
        constrained.swap(c2);
    }

    std::vector<char> pinned_name(PREG, 0);
    if (!g_copyprop_nopin) {
        std::vector<int> em;
        sp.exit_mask.bits(em);
        for (int r : em) if (r >= 0 && r < PREG) pinned_name[(size_t)r] = 1;
    }

    std::vector<int> names;
    for (auto &pr : byreg) names.push_back(pr.first);
    std::sort(names.begin(), names.end());

    for (const Copy &c : al.copies) {
        bool is_lm = (c.kind == 1);
        bool is_id = (c.kind == 2);
        if (c.kind != 0 && !is_lm && !is_id) continue;
        if (c.kind == 0 && !(kinds & 1)) continue;
        if (is_lm && !(kinds & 2)) continue;
        if (is_id && !(kinds & 4)) continue;
        int i = c.i;

        if (removed.count(i)) continue;
        if (is_id) {

            if (sp.norw[(size_t)i]) continue;
            if (!sp.nopred[(size_t)i] && sp.pnum[(size_t)i] != PT) { cs.rej_pred++; continue; }
            cs.id_cands++;
        } else if (!is_lm) {

            if (p.op[i] != T.O_Mov) continue;
            if (sp.norw[(size_t)i]) continue;
            if (!sp.nopred[(size_t)i] && sp.pnum[(size_t)i] != PT) { cs.rej_pred++; continue; }
            if (((p.q[i] >> 39) & 0xF) != 0xF) continue;
            cs.cands++;
        } else {

            if (!sp.lm[(size_t)i].valid || sp.lm[(size_t)i].w != 1) continue;
            cs.lm_cands++;
        }

        int a = find(c.dw), b = find(c.sw);
        if (a == b) {

            if (!is_lm) {
                if (is_id) cs.id_merged++; else cs.already++;
                removed.insert(i);
            }
            continue;
        }
        if (constrained.count(a) || constrained.count(b)) { cs.rej_constrained++; continue; }
        int ra = gpr(a), rb = gpr(b);

        if (ra < 0 && rb < 0) { cs.rej_nogpr++; continue; }
        if (!is_lm && (ra < 0 || rb < 0)) { cs.rej_nogpr++; continue; }

        int keep = b, drop = a;
        const BV *lkp = livepts.count(keep) ? &livepts[keep] : nullptr;
        const BV *ldp = livepts.count(drop) ? &livepts[drop] : nullptr;
        BV lk = lkp ? *lkp : BV(), ld = ldp ? *ldp : BV();

        if (bv_inter(lk, ld)) { cs.rej_interfere++; continue; }

        BV merged = lk;
        bv_or(merged, ld);

        bool pa = (ra >= 0) && pinned_name[(size_t)ra];
        bool pb = (rb >= 0) && pinned_name[(size_t)rb];
        std::vector<int> want;
        if (ra < 0 || rb < 0) {
            int g = (ra >= 0) ? ra : rb;
            want.push_back(g);
            if (!pinned_name[(size_t)g])
                for (int r : names)
                    if (r != g && !pinned_name[(size_t)r]) want.push_back(r);
        } else if (pa && pb) {
            if (ra != rb) { cs.rej_clash++; continue; }
            want.push_back(ra);
        } else if (pa) { want.push_back(ra); cs.pin_kept++; }
        else if (pb) want.push_back(rb);
        else {
            want.push_back(rb);
            if (ra != rb) want.push_back(ra);
            for (int r : names)
                if (r != ra && r != rb && !pinned_name[(size_t)r])
                    want.push_back(r);
        }

        auto legal = [&](int r) {
            auto bit = byreg.find(r);
            if (bit == byreg.end()) return true;
            for (int cw : bit->second) {
                int cf = find(cw);
                if (cf == keep || cf == drop) continue;
                if (livepts.count(cf) && bv_inter(livepts[cf], merged))
                    return false;
            }
            return true;
        };
        int rk = -1;
        for (int r : want) if (legal(r)) { rk = r; break; }
        if (rk < 0) { cs.rej_clash++; continue; }

        parent[drop] = keep;
        livepts[keep] = merged;
        livepts.erase(drop);
        if (ra >= 0) byreg[ra].erase(drop);
        if (rb >= 0) byreg[rb].erase(keep);
        byreg[rk].insert(keep);
        wr[keep] = rk;
        n_merged_here++;
        if (is_lm) {

            cs.lm_merged++;
        } else {
            removed.insert(i);
            if (is_id) cs.id_merged++;
            else cs.merged++;
        }
    }

    {
        std::unordered_map<int, BV> lp;
        for (auto &pr : al.livepts) bv_or(lp[find(pr.first)], pr.second);
        std::unordered_map<int, std::set<int>> perreg;
        for (auto &pr : wr) {
            int f = find(pr.first);
            int r = gpr(f);
            if (r >= 0) perreg[r].insert(f);
        }
        int viol = 0;
        for (auto &pr : perreg) {
            std::vector<int> ws(pr.second.begin(), pr.second.end());
            for (size_t x = 0; x < ws.size(); x++)
                for (size_t y = x + 1; y < ws.size(); y++)
                    if (lp.count(ws[x]) && lp.count(ws[y]) &&
                        bv_inter(lp[ws[x]], lp[ws[y]])) viol++;
        }
        if (viol)
            fail("copy coalescing produced %d overlapping same-register web "
                 "pairs", viol);
    }

    lmparent.clear();
    for (auto &pr : parent) lmparent[pr.first] = find(pr.first);
    return n_merged_here;
}

}
