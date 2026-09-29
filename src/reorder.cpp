
#include "emit.h"
#include "nv_sched_ctl.h"

extern "C" {
int uber_phase_a(const unsigned char *bc, unsigned int constOff, int nreal,
                 int *perm, unsigned char *leader, int *nslots, int memdeps,
                 const unsigned char *pdefs, const unsigned char *puses);
int uber_fill_bubbles(const unsigned char *bc, unsigned int constOff, int nreal,
                      int *perm, unsigned char *leader, int *nslots, int memdeps,
                      const unsigned char *pdefs, const unsigned char *puses);
int uber_hoist_ll(const unsigned char *bc, unsigned int constOff, int nreal,
                  int *perm, unsigned char *leader, int *nslots, int memdeps,
                  const unsigned char *pdefs, const unsigned char *puses);

void ub_set_webs(const int *wuse, const int *wdef, int stride);
void ub_fe_reset(void);
void ub_fe_get(long long *seen, long long *fals);
void ub_fe_cls_get(long long *cls);
void ub_fe_renames_get(long long *v);
void ub_fe_crossed_get(long long *defs, long long *edges);
void ub_cp_reset(void);
void ub_cp_get(long long *all, long long *nofalse);
extern int _ub_nofalse;
extern int _ub_docp;
}

namespace ub {

enum { MC_NONE = 0, MC_LOCAL, MC_ATTR, MC_SHARED, MC_GLOBAL, MC_ALL = 9 };

struct MemRef {
    int cls = MC_NONE;
    bool wr = false;
    int ra = -1;
    long off = 0;
    int size = 0;
    bool exact = false;
};

static int ldst_bytes(int t) {
    switch (t) {
    case 0: case 1: return 1;
    case 2: case 3: return 2;
    case 4: return 4;
    case 5: return 8;
    case 6: return 16;
    default: return -1;
    }
}

static MemRef memref_of(u64 q, int nm) {
    const OpSets &T = S();
    MemRef m;
    const char *n = op_name(nm);
    if (nm == T.O_Ldl || nm == T.O_Stl) {
        long off = lmem_off(q);
        int sz = ldst_bytes((int)((q >> 48) & 7));
        m.cls = MC_LOCAL;
        m.wr = (nm == T.O_Stl);
        m.ra = (int)((q >> 8) & 0xFF);
        m.off = off;
        m.size = sz;
        m.exact = (sz > 0 && off >= 0);
        return m;
    }
    if (nm == T.O_Ald || nm == T.O_Ast) {
        m.cls = MC_ATTR;
        m.wr = (nm == T.O_Ast);
        m.ra = (int)((q >> 8) & 0xFF);
        m.off = (long)((q >> 20) & 0x7FF);
        m.size = 4 * ((int)((q >> 47) & 3) + 1);
        m.exact = ((int)((q >> 39) & 0xFF) == 0xFF);
        return m;
    }
    if (!strcmp(n, "Lds") || !strcmp(n, "Sts")) {
        m.cls = MC_SHARED; m.wr = (n[0] == 'S'); return m;
    }
    if (!strcmp(n, "Ld") || !strcmp(n, "Ldg")) { m.cls = MC_GLOBAL; return m; }
    if (!strcmp(n, "St") || !strcmp(n, "Stg")) {
        m.cls = MC_GLOBAL; m.wr = true; return m;
    }
    static const char *conservative[] = {
        "Atom", "Atoms", "AtomCas", "AtomsCas", "Red", "Membar", "Bar",
        "Depbar", "Cctl", "Cctll", "Cctlt", "Suld", "SuldB", "SuldD",
        "SuldDB", "Sust", "SustB", "SustD", "SustDB", "Sured", "SuredB",
        "Suatom", "SuatomB", "SuatomB2", "SuatomCas", "SuatomCasB", "Out",
        "Isberd", "Al2p", "Pixld", nullptr};
    for (int i = 0; conservative[i]; i++)
        if (!strcmp(n, conservative[i])) { m.cls = MC_ALL; m.wr = true; return m; }
    return m;
}

static bool may_alias(const MemRef &a, const MemRef &b) {
    if (!a.cls || !b.cls) return false;
    if (!a.wr && !b.wr) return false;
    if (a.cls == MC_ALL || b.cls == MC_ALL) return true;
    if (a.cls != b.cls) return false;
    if (!a.exact || !b.exact) return true;
    if (a.ra != b.ra) return true;
    if (a.off + a.size <= b.off) return false;
    if (b.off + b.size <= a.off) return false;
    return true;
}

struct MemOp { u64 q; u64 key; MemRef r; };

static u64 memkey(u64 q) {
    u64 k = q & ~(u64)0xFF;

    k &= ~(renumber_mask(q) & ~(u64)0xFF);
    return k;
}

static void mem_sequence(const std::vector<u8> &bc, const std::vector<u8> &ct,
                         std::vector<MemOp> &out) {
    out.clear();
    u32 co = const_off(ct);
    if (co > bc.size()) co = (u32)bc.size();
    int n = 3 * ((int)co - INSTR_START) / 32;
    for (int k = 0; k < n; k++) {
        size_t off = slot_off(k);
        if (off + 8 > bc.size()) break;
        u64 q;
        std::memcpy(&q, bc.data() + off, 8);
        if (!q) continue;
        MemRef r = memref_of(q, decode_op(q));
        if (r.cls) out.push_back({q, memkey(q), r});
    }
}

bool gate_memorder(const std::vector<u8> &pre_bc, const std::vector<u8> &pre_ct,
                   const std::vector<u8> &post_bc, const std::vector<u8> &post_ct,
                   std::string &detail) {
    std::vector<MemOp> a, b;
    mem_sequence(pre_bc, pre_ct, a);
    mem_sequence(post_bc, post_ct, b);
    char buf[256];

    {
        std::set<long> pre_slots;
        for (const MemOp &m : a)
            if (m.r.cls == MC_LOCAL && m.r.exact) pre_slots.insert(m.r.off);
        std::vector<MemOp> kept;
        std::set<long> stored;
        int nfresh = 0;
        for (const MemOp &m : b) {
            if (m.r.cls == MC_LOCAL && m.r.exact && !pre_slots.count(m.r.off)) {
                nfresh++;
                if (m.r.wr) stored.insert(m.r.off);
                else if (!stored.count(m.r.off)) {
                    snprintf(buf, sizeof buf,
                             "load from fresh local slot %ld before any store", m.r.off);
                    detail = buf;
                    return false;
                }
                continue;
            }
            kept.push_back(m);
        }
        if (nfresh) b.swap(kept);
    }
    if (a.size() != b.size()) {
        snprintf(buf, sizeof buf, "memory-op count changed %zu -> %zu",
                 a.size(), b.size());
        detail = buf;
        return false;
    }

    std::map<u64, std::vector<int>> where;
    for (size_t i = 0; i < b.size(); i++) where[b[i].key].push_back((int)i);
    std::map<u64, size_t> seen;
    std::vector<int> to(a.size(), -1);
    for (size_t i = 0; i < a.size(); i++) {
        auto it = where.find(a[i].key);
        size_t k = seen[a[i].key]++;
        if (it == where.end() || k >= it->second.size()) {
            snprintf(buf, sizeof buf,
                     "memory-op multiset changed (word %016llx)",
                     (unsigned long long)a[i].q);
            detail = buf;
            return false;
        }
        to[i] = it->second[k];
    }
    int bad = 0;
    size_t fi = 0, fj = 0;
    for (size_t i = 0; i < a.size(); i++)
        for (size_t j = i + 1; j < a.size(); j++)
            if (may_alias(a[i].r, a[j].r) && to[i] > to[j]) {
                if (!bad) { fi = i; fj = j; }
                bad++;
            }
    if (bad) {
        snprintf(buf, sizeof buf,
                 "%d aliasing memory pair(s) reordered; first %016llx before "
                 "%016llx", bad, (unsigned long long)a[fj].q,
                 (unsigned long long)a[fi].q);
        detail = buf;
        return false;
    }
    snprintf(buf, sizeof buf, "%zu memory ops, order preserved", a.size());
    detail = buf;
    return true;
}

bool g_reorder_report_only = false;

void pred_masks(const Program &p, int n, std::vector<u8> &pdefs,
                std::vector<u8> &puses) {
    pdefs.assign((size_t)n, 0);
    puses.assign((size_t)n, 0);
    for (int k = 0; k < n && k < p.n; k++) {
        if (!p.q[k]) continue;
        RSet d = p.defs[k];
        d.unite(p.maydefs[k]);
        for (int b = 0; b < 7; b++) {
            if (d.has(PREG + b)) pdefs[(size_t)k] |= (u8)(1 << b);
            if (p.uses[k].has(PREG + b)) puses[(size_t)k] |= (u8)(1 << b);
        }
    }
}

static void apply_perm(std::vector<u8> &bc, const Program &p, u32 co, int n,
                       const std::vector<int> &perm, const std::vector<u8> &leader,
                       const char *who) {
    const OpSets &T = S();
    std::vector<u64> words((size_t)n), out((size_t)n);
    for (int k = 0; k < n; k++)
        std::memcpy(&words[(size_t)k], bc.data() + slot_off(k), 8);
    for (int k = 0; k < n; k++) out[(size_t)k] = words[(size_t)perm[(size_t)k]];
    for (int k = 0; k < n; k++) {
        int j = perm[(size_t)k];
        if (j >= p.n || !p.q[j]) continue;
        if (!T.branchy_imm[(size_t)p.op[j]]) continue;
        int t = p.target(j);
        if (t < 0 || t >= n) fail("%s: unresolved branch at slot %d", who, j);
        if (!leader[(size_t)t])
            fail("%s: branch target slot %d is not a basic-block leader", who, t);
        int disp = slot_rel(t) - (slot_rel(k) + 8);
        if (!branch_disp_ok(disp))
            fail("%s: branch displacement out of range", who);
        out[(size_t)k] = setbits(out[(size_t)k], 20, 24, (u64)(u32)disp & 0xFFFFFF);
    }
    for (int k = 0; k < n; k++)
        std::memcpy(bc.data() + slot_off(k), &out[(size_t)k], 8);
    phase_b(bc, co);
}

int issue_cycles(const std::vector<u8> &bc, u32 co) {
    int total = 0;
    for (u32 off = INSTR_START; off + 32 <= co; off += 32) {
        u64 w;
        std::memcpy(&w, bc.data() + off, 8);
        for (int s = 0; s < 3; s++) {
            u64 q;
            std::memcpy(&q, bc.data() + off + 8 + 8 * s, 8);
            if (q) total += SCHED_WAIT_DEC[sched_wait_code(w, s)];
        }
    }
    return total;
}

bool g_presched_probe = false;
int g_presched_drop = 0;
bool g_stage_fragment = true;
FEStats g_fe;

bool g_fe_locked = false;

void reorder(std::vector<u8> &bc, std::vector<u8> &ct, ReorderStats &st,
             bool memdeps) {
    u32 co = const_off(ct);
    if (co > bc.size()) fail("reorder: ConstBufOffset past the file");
    int n = 3 * ((int)co - INSTR_START) / 32;
    if (n <= 0) return;

    std::vector<u8> pre_bc = bc;
    int nreal = 0;
    for (int k = 0; k < n; k++) {
        u64 q;
        std::memcpy(&q, bc.data() + slot_off(k), 8);
        if (q) nreal = k + 1;
    }

    Program p;
    p.load_bytes(bc, ct);
    std::vector<u8> pdefs, puses;
    pred_masks(p, n, pdefs, puses);

    bool want_webs = g_presched_drop || (g_presched_probe && !g_fe_locked);
    std::vector<int> wuse, wdef;
    if (want_webs) {
        int wn = 0;
        web_map(pre_bc, ct, g_stage_fragment, wuse, wdef, wn);
        if (wn != n) fail("reorder: web map slot count %d != %d", wn, n);
        ub_fe_reset();
        ub_cp_reset();
        _ub_nofalse = g_presched_drop;
        _ub_docp = g_presched_drop ? 0 : 1;
        ub_set_webs(wuse.data(), wdef.data(), WEB_STRIDE);
    }

    std::vector<int> perm((size_t)n);
    std::vector<u8> leader((size_t)n);
    int nslots = 0;
    int moved = uber_phase_a(bc.data(), co, nreal, perm.data(), leader.data(),
                             &nslots, memdeps ? 1 : 0, pdefs.data(),
                             puses.data());
    if (want_webs) {
        long long seen[3], fals[3], cpa = 0, cpn = 0, cls[8], ren = 0;
        long long crd = 0, cre = 0;
        ub_fe_get(seen, fals);
        ub_fe_cls_get(cls);
        ub_fe_renames_get(&ren);
        ub_fe_crossed_get(&crd, &cre);
        ub_cp_get(&cpa, &cpn);
        if (!g_fe_locked) {
            for (int k = 0; k < 3; k++) { g_fe.seen[k] += seen[k]; g_fe.fals[k] += fals[k]; }
            for (int k = 0; k < 8; k++) g_fe.cls[k] += cls[k];
            g_fe.renames += ren;
            g_fe.crossed += crd;
            g_fe.crossed_edges += cre;
            g_fe.cp_all += cpa;
            g_fe.cp_nofalse += cpn;
            g_fe_locked = true;
        }
        ub_set_webs(nullptr, nullptr, 0);
        _ub_nofalse = 0;
    }
    if (moved < 0) fail("reorder: phase A failed");
    if (nslots != n) fail("reorder: phase A slot count %d != %d", nslots, n);

    apply_perm(bc, p, co, n, perm, leader, "reorder");

    std::string d;
    if (!gate_memorder(pre_bc, ct, bc, ct, d)) {
        if (!g_reorder_report_only)
            fail("reorder: V11 memory order violated -- %s", d.c_str());
        st.v11_violations = 1;
    }

    st.moved = moved;
    st.slots = n;
    st.memops = (int)([&] {
        std::vector<MemOp> v;
        mem_sequence(bc, ct, v);
        return v.size();
    }());
}


struct FillEntry {
    std::vector<u8> bc;
    int before = 0, after = 0, moved = 0, rounds = 0, v11 = 0;
};
static std::map<std::string, FillEntry> g_fill_cache;
void fill_cache_clear() { g_fill_cache.clear(); }

static void fill_bubbles_uncached(std::vector<u8> &bc, std::vector<u8> &ct,
                                  ReorderStats &st, bool memdeps, int rounds);

void fill_bubbles(std::vector<u8> &bc, std::vector<u8> &ct, ReorderStats &st,
                  bool memdeps, int rounds) {
    std::string key;
    key.reserve(bc.size() + ct.size() + 8);
    key.push_back(memdeps ? 'M' : 'm');
    key.push_back((char)(rounds & 0x7F));
    key.append((const char *)bc.data(), bc.size());
    key.append((const char *)ct.data(), ct.size());
    g_perf.n_fill++;
    auto it = g_fill_cache.find(key);
    if (it != g_fill_cache.end()) {
        g_perf.n_fill_hit++;
        bc = it->second.bc;
        st.fill_before = it->second.before;
        st.fill_after = it->second.after;
        st.fill_moved += it->second.moved;
        st.fill_rounds = it->second.rounds;
        st.v11_violations |= it->second.v11;
        return;
    }
    ReorderStats probe;
    probe.fill_moved = 0;
    fill_bubbles_uncached(bc, ct, probe, memdeps, rounds);
    FillEntry e;
    e.bc = bc;
    e.before = probe.fill_before;
    e.after = probe.fill_after;
    e.moved = probe.fill_moved;
    e.rounds = probe.fill_rounds;
    e.v11 = probe.v11_violations;
    g_fill_cache.emplace(std::move(key), std::move(e));
    st.fill_before = e.before;
    st.fill_after = e.after;
    st.fill_moved += e.moved;
    st.fill_rounds = e.rounds;
    st.v11_violations |= e.v11;
}

static void fill_bubbles_uncached(std::vector<u8> &bc, std::vector<u8> &ct,
                                  ReorderStats &st, bool memdeps, int rounds) {
    u32 co = const_off(ct);
    if (co > bc.size()) fail("fill: ConstBufOffset past the file");
    int n = 3 * ((int)co - INSTR_START) / 32;
    if (n <= 0) return;

    std::vector<u8> pre_bc = bc;
    int best = issue_cycles(bc, co);
    st.fill_before = best;

    for (int r = 0; r < rounds; r++) {
        std::vector<u8> trial = bc;
        int nreal = 0;
        for (int k = 0; k < n; k++) {
            u64 q;
            std::memcpy(&q, trial.data() + slot_off(k), 8);
            if (q) nreal = k + 1;
        }
        Program p;
        p.load_bytes(trial, ct);
        std::vector<u8> pdefs, puses;
        pred_masks(p, n, pdefs, puses);

        std::vector<int> perm((size_t)n);
        std::vector<u8> leader((size_t)n);
        int nslots = 0;
        int moved = uber_fill_bubbles(trial.data(), co, nreal, perm.data(),
                                      leader.data(), &nslots, memdeps ? 1 : 0,
                                      pdefs.data(), puses.data());
        if (moved < 0) fail("fill: pass failed");
        if (nslots != n) fail("fill: slot count %d != %d", nslots, n);
        if (moved == 0) break;

        apply_perm(trial, p, co, n, perm, leader, "fill");
        int now = issue_cycles(trial, co);
        if (now >= best) break;
        best = now;
        bc.swap(trial);
        st.fill_moved += moved;
        st.fill_rounds = r + 1;
    }
    st.fill_after = best;

    std::string d;
    if (!gate_memorder(pre_bc, ct, bc, ct, d)) {
        if (!g_reorder_report_only)
            fail("fill: V11 memory order violated -- %s", d.c_str());
        st.v11_violations = 1;
    }
}


}
