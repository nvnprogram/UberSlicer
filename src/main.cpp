
#include <exception>
#include <numeric>
#include "emit.h"
#include "nv_sched_ctl.h"

#include "json.hpp"
#include <cctype>
#include <cerrno>
#include <sys/stat.h>

#ifdef _WIN32
#include <direct.h>
#define MKDIR(p) _mkdir(p)
#else
#include <unistd.h>
#define MKDIR(p) mkdir(p, 0777)
#endif

namespace ub {

static std::string slurp_text(const std::string &p) {
    std::vector<u8> b = read_file(p);
    return std::string((const char *)b.data(), b.size());
}
static void spit(const std::string &p, const std::vector<u8> &b) {
    FILE *f = fopen(p.c_str(), "wb");
    if (!f) fail("cannot write %s", p.c_str());
    if (!b.empty() && fwrite(b.data(), 1, b.size(), f) != b.size()) {
        fclose(f); fail("short write %s", p.c_str());
    }
    fclose(f);
}
static void mkdirs(const std::string &p) {
    std::string cur;
    for (size_t i = 0; i < p.size(); i++) {
        cur += p[i];
        if (p[i] == '/' || p[i] == '\\') {
            if (cur.size() > 1) MKDIR(cur.c_str());
        }
    }
    MKDIR(p.c_str());
}
static bool exists(const std::string &p) {
    struct stat st;
    return stat(p.c_str(), &st) == 0;
}




struct OptionRec {
    std::string name;
    std::vector<std::string> choice_names;
    int default_choice_idx = 0;
};

struct DataSet {
    std::string root;
    std::string table_path;
    std::vector<OptionRec> options;
    std::map<std::string, size_t> by_name;
    std::vector<std::string> c6_order;

    std::map<std::string, int> c6_slot;
    std::vector<std::string> option_order;
    std::map<std::string, size_t> oidx;

    void load(const std::string &r, const std::string &tablePath) {
        root = r;
        table_path = tablePath;

        if (table_path.empty()) fail("--options-table is required");
        {
            nlohmann::json v = nlohmann::json::parse(slurp_text(table_path));
            std::vector<std::pair<long long, std::string>> c6;
            for (const nlohmann::json &o : v.at("options")) {
                OptionRec rec;
                rec.name = o.at("name").get<std::string>();
                for (const nlohmann::json &c : o.at("choice_names"))
                    rec.choice_names.push_back(c.get<std::string>());
                rec.default_choice_idx = o.at("default_choice_idx").get<int>();
                by_name[rec.name] = options.size();
                option_order.push_back(rec.name);

                auto ci = o.find("c6_option_index");
                if (ci != o.end() && ci->is_number())
                    c6.push_back({ci->get<long long>(), rec.name});
                options.push_back(rec);
            }
            std::sort(c6.begin(), c6.end());
            for (size_t i = 0; i < c6.size(); i++) {
                if (c6[i].first != (long long)i)
                    fail("%s: c6_option_index is not 0..n-1 (slot %lld at position %zu)",
                         table_path.c_str(), c6[i].first, i);
                c6_order.push_back(c6[i].second);
                c6_slot[c6[i].second] = (int)i;
            }
            for (size_t i = 0; i < option_order.size(); i++) oidx[option_order[i]] = i;
        }
    }

    std::vector<u32> build_c6(const std::map<std::string, std::string> &ov,
                              std::vector<std::string> *unrepresented) const {
        std::vector<u32> out;
        std::set<std::string> seen;
        for (const std::string &nm : c6_order) {
            const OptionRec &rec = options[by_name.at(nm)];
            size_t idx;
            auto it = ov.find(nm);
            if (it != ov.end()) {
                auto ci = std::find(rec.choice_names.begin(),
                                    rec.choice_names.end(), it->second);
                if (ci == rec.choice_names.end())
                    fail("option %s has no choice '%s'", nm.c_str(),
                         it->second.c_str());
                idx = (size_t)(ci - rec.choice_names.begin());
                seen.insert(nm);
            } else idx = (size_t)rec.default_choice_idx;
            out.push_back((u32)strtoul(rec.choice_names[idx].c_str(), nullptr, 10));
        }
        if (unrepresented)
            for (auto &pr : ov)
                if (!seen.count(pr.first)) unrepresented->push_back(pr.first);
        return out;
    }

};


struct UberCtx {
    Program prog;
    Spec sp;
};

static bool g_reorder = false;
static bool g_reorder2 = false;
static bool g_fill = false;
static int  g_fill_rounds = 8;
static bool g_pa_anti = false;
static bool g_reorder_nomem = false;
static bool g_cbfold = false;

extern "C" void uber_set_pa_anti(int v);
extern "C" int ubf_pick_last;
extern "C" int ubh_class;
extern "C" int ubh_thresh;
extern "C" int ubh_cap;
extern "C" int ubh_latency;

static std::map<std::string, UberCtx *> g_ctx;

struct UberInputs {
    std::map<std::string, std::string> bc, ct;

    int bank = -1;
};

static UberInputs g_uber[2];

static const char *stage_name(bool fragment) {
    return fragment ? "fragment" : "vertex";
}

static int uber_bank(bool fragment) {
    int b = g_uber[fragment].bank;
    if (b < 0)
        fail("--option-bank-%s is required: it is "
             "UniformBlockIndices[gsys_shader_option].%sLocation + 3 for the "
             "archive this ubershader came from, which only the caller can see",
             stage_name(fragment), fragment ? "Fragment" : "Vertex");
    return b;
}

static std::string control_sibling(const std::string &bc) {
    static const char *suf[2] = {"_bytecode.bin", "_control.bin"};
    size_t n = std::strlen(suf[0]);
    if (bc.size() > n && bc.compare(bc.size() - n, n, suf[0]) == 0)
        return bc.substr(0, bc.size() - n) + suf[1];
    fail("cannot derive a control path from '%s'; pass it explicitly", bc.c_str());
}

static std::string basename_of(const std::string &p) {
    size_t k = p.find_last_of("/\\");
    return (k == std::string::npos) ? p : p.substr(k + 1);
}

static void uber_paths(bool fragment, const std::string &key,
                       std::string &bc, std::string &ct) {
    const UberInputs &U = g_uber[fragment];
    auto it = U.bc.find(key);
    if (it == U.bc.end()) it = U.bc.find(std::string());
    if (it == U.bc.end()) {
        if (fragment)
            fail("no fragment ubershader: pass --uber <bytecode.bin>");
        fail("no vertex ubershader for gsys_weight=%s: pass "
             "--uber %s=<bytecode.bin>, or --uber <bytecode.bin> for every "
             "weight", key.empty() ? "(any)" : key.c_str(), key.c_str());
    }
    bc = it->second;
    auto ci = U.ct.find(it->first);
    ct = ci != U.ct.end() ? ci->second : control_sibling(bc);
}

static bool uber_stage_of(const std::string &bcp) {
    static std::map<std::string, bool> memo;
    auto it = memo.find(bcp);
    if (it != memo.end()) return it->second;
    bool f = bytecode_is_fragment(read_file(bcp), bcp.c_str());
    memo[bcp] = f;
    return f;
}

struct UberArg {
    std::string key, path;
    int stage;
    bool control;
};

static void uber_arg(std::vector<UberArg> &v, const std::string &spec,
                     int stage, bool control) {
    UberArg a;
    a.stage = stage;
    a.control = control;
    size_t q = spec.find('=');
    if (q != std::string::npos &&
        spec.find_first_of("/\\", 0) > q && q > 0) {
        a.key = spec.substr(0, q);
        a.path = spec.substr(q + 1);
    } else a.path = spec;
    v.push_back(a);
}


static void resolve_uber_args(const std::vector<UberArg> &v) {
    for (const UberArg &a : v) {
        if (a.control) continue;
        if (!exists(a.path)) fail("%s does not exist", a.path.c_str());
        bool f = uber_stage_of(a.path);
        if (a.stage >= 0 && (int)f != a.stage)
            fail("%s is a %s shader (sph_type says so), but it was passed as "
                 "the %s ubershader", a.path.c_str(), stage_name(f),
                 stage_name(a.stage != 0));
        std::string &slot = g_uber[f].bc[a.key];
        if (!slot.empty() && slot != a.path) {
            std::string which = a.key.empty() ? std::string()
                                             : " for gsys_weight=" + a.key;
            fail("two %s ubershaders%s: %s and %s", stage_name(f),
                 which.c_str(), slot.c_str(), a.path.c_str());
        }
        slot = a.path;
    }
    for (const UberArg &a : v) {
        if (!a.control) continue;
        int f = a.stage;
        if (f < 0) {
            bool hf = g_uber[1].bc.count(a.key) != 0;
            bool hv = g_uber[0].bc.count(a.key) != 0;
            if (hf == hv)
                fail("--uber-control %s: %s ubershader under that key, so the "
                     "stage is ambiguous - use --uber-fragment-control or "
                     "--uber-vertex-control", a.path.c_str(),
                     hf ? "both stages have an" : "no");
            f = hf ? 1 : 0;
        }
        g_uber[f].ct[a.key] = a.path;
    }
}

static bool stage_is_fragment(const std::string &s) {
    if (s == "fragment") return true;
    if (s == "vertex") return false;
    fail("stage '%s': expected fragment or vertex", s.c_str());
}

static bool check_stage(const std::string &s) {
    bool f = stage_is_fragment(s);
    if (g_uber[f].bc.empty())
        fail("no %s ubershader was passed, so nothing can answer for the %s "
             "stage: pass --uber <bytecode.bin>", stage_name(f), stage_name(f));
    return f;
}

static UberCtx *get_ctx(DataSet &D, bool fragment, const std::string &uber_key,
                        bool redundancy) {
    (void)D;
    std::string bcp, ctp;
    uber_paths(fragment, uber_key, bcp, ctp);

    std::string key = (fragment ? "F:" : "V:") + bcp + "|" + ctp +
                      (redundancy ? ":6" : ":5") + (g_cbfold ? ":cb" : "") +
                      (g_cse_mov32i ? ":cse" : "");
    auto it = g_ctx.find(key);
    if (it != g_ctx.end()) return it->second;
    UberCtx *c = new UberCtx();
    c->prog.load_paths(bcp, ctp);

    std::vector<int> exit_live;
    if (fragment) exit_live_regs(c->prog.bc, exit_live);

    int folds = redundancy ? FOLD_ALL : 0;
    c->sp.init(c->prog, uber_bank(fragment), exit_live,
                 true,   g_cbfold, folds,
                 redundancy);
    g_ctx[key] = c;
    return c;
}

static void option_slots_read(const Program &p, int bank, std::set<int> &out) {
    for (int i = 0; i < p.n; i++) {
        u64 q = p.q[i];
        if (!q) continue;
        int b, o;

        if (cbuf_read_of(q, p.op[i], &b, &o) && b == bank) out.insert(o >> 2);
    }
}

static std::map<std::string, std::set<int>> g_slots_read;
static const std::set<int> &uber_slots_read(bool fragment,
                                            const std::string &key) {
    std::string bcp, ctp;
    uber_paths(fragment, key, bcp, ctp);
    auto it = g_slots_read.find(bcp);
    if (it != g_slots_read.end()) return it->second;
    Program p;
    p.load_paths(bcp, ctp);
    std::set<int> s;
    option_slots_read(p, uber_bank(fragment), s);
    return g_slots_read.emplace(bcp, std::move(s)).first->second;
}

enum OptionReach { REACH_OK = 0, REACH_NO_SLOT, REACH_UNREAD };

static OptionReach option_reach(const DataSet &D, bool fragment,
                                const std::string &key, const std::string &nm) {
    auto sit = D.c6_slot.find(nm);
    if (sit == D.c6_slot.end()) return REACH_NO_SLOT;
    return uber_slots_read(fragment, key).count(sit->second) ? REACH_OK
                                                            : REACH_UNREAD;
}





static bool g_quick = false;

struct Composed {
    std::vector<u8> bc, ct;
    EmitStats st;
    RegStats rst;
    CtlFacts facts;
    ReorderStats ro;
    Dce2Stats dce;
    TexNarrowStats tn;
    std::vector<u8> pre_bc, pre_ct;
    bool has_pre = false;
};


static void compose_one(DataSet &D, bool fragment, const std::string &uber_key,
                        const std::vector<u32> &c6, const std::string &name,
                        Composed &out) {
    UberCtx *c = get_ctx(D, fragment, uber_key, true);
    g_perf.n_compose++;
    g_stage_fragment = fragment;
    emit(c->prog, c->sp, c6, name, out.st);
    out.bc = out.st.bc;
    out.ct = out.st.ct;


    if (g_dce2_early) {
        Dce2Stats e;
        dce2(out.bc, out.ct, fragment, e,   false);
        out.dce.dead += e.dead; out.dce.self += e.self;
    }
    if (g_reorder || g_reorder_nomem || g_fill) {
        out.pre_bc = out.bc;
        out.pre_ct = out.ct;
        out.has_pre = true;
        if (g_reorder || g_reorder_nomem) {
            PerfScope ps_(&g_perf.t_reorder);
            reorder(out.bc, out.ct, out.ro, !g_reorder_nomem);
        }

    }
    if (g_fill && !g_quick) {

        std::vector<u8> nf_bc = out.bc, nf_ct = out.ct;
        ReorderStats fs;
        { PerfScope ps_(&g_perf.t_fill);
          fill_bubbles(out.bc, out.ct, fs, !g_reorder_nomem, g_fill_rounds); }
        out.ro.fill_moved = fs.fill_moved;
        out.ro.fill_rounds = fs.fill_rounds;
        out.ro.fill_before = fs.fill_before;
        out.ro.fill_after = fs.fill_after;
        out.ro.v11_violations |= fs.v11_violations;

        std::vector<u8> a_bc = out.bc, a_ct = out.ct;
        RegStats ra;
        { PerfScope ps_(&g_perf.t_renumber); g_perf.n_renumber++;
          renumber(a_bc, a_ct, fragment,   true, ra); }
        RegStats rb;
        { PerfScope ps_(&g_perf.t_renumber); g_perf.n_renumber++;
          renumber(nf_bc, nf_ct, fragment,   true, rb); }

        u32 co_a, co_b;
        co_a = const_off(a_ct);
        co_b = const_off(nf_ct);
        bool keep = occupancy_of(ra.new_decl) >= occupancy_of(rb.new_decl) &&
                    issue_cycles(a_bc, co_a) <= issue_cycles(nf_bc, co_b);
        if (keep) {
            out.bc.swap(a_bc); out.ct.swap(a_ct); out.rst = ra;
        } else {
            out.bc.swap(nf_bc); out.ct.swap(nf_ct); out.rst = rb;
            out.ro.fill_reverted = 1;
        }
    } else {
        if (g_fill) { PerfScope ps_(&g_perf.t_fill);
            fill_bubbles(out.bc, out.ct, out.ro, !g_reorder_nomem,
                         g_fill_rounds); }
        {
            PerfScope ps_(&g_perf.t_renumber); g_perf.n_renumber++;
            renumber(out.bc, out.ct, fragment,   true, out.rst);
        }
    }

    if (g_reorder2) {
        ReorderStats r2;
        reorder(out.bc, out.ct, r2, !g_reorder_nomem);
        out.ro.moved += r2.moved;
        out.ro.v11_violations |= r2.v11_violations;
    }

    if (g_dce2) dce2(out.bc, out.ct, fragment, out.dce);
    {
        PerfScope ps_(&g_perf.t_control);
        control_rewrite(out.bc, out.ct, out.facts);
    }

    if (g_texnarrow)
        texnarrow(out.bc, out.ct, fragment, out.tn);
}

static void compose_cp(DataSet &D, bool fragment, const std::string &uber_key,
                       const std::vector<u32> &c6, const std::string &name,
                       Composed &out) {
    g_perf.n_compose_cp++;
    if (!g_copyprop) {
        compose_one(D, fragment, uber_key, c6, name, out);
        return;
    }
    Composed with, without;
    compose_one(D, fragment, uber_key, c6, name, with);
    g_copyprop = false;
    compose_one(D, fragment, uber_key, c6, name, without);
    g_copyprop = true;

    u32 ca, cb;
    ca = const_off(with.ct);
    cb = const_off(without.ct);
    bool keep = occupancy_of(with.rst.new_decl) >=
                    occupancy_of(without.rst.new_decl) &&
                issue_cycles(with.bc, ca) <= issue_cycles(without.bc, cb);
    CopyStats cp = with.st.cp;
    out = keep ? std::move(with) : std::move(without);
    if (!keep) { out.st.cp = cp; out.st.cp.reverted = 1; }
}

int g_lm_pick_promote = 0, g_lm_pick_compact = 0, g_lm_pick_off = 0;
int g_lm_pick_cp = 0;

static bool cheaper(const Composed &a, const Composed &b) {
    u32 ca = const_off(a.ct), cb = const_off(b.ct);
    int ya = issue_cycles(a.bc, ca), yb = issue_cycles(b.bc, cb);
    if (ya != yb) return ya < yb;
    int wa = occupancy_of(a.rst.new_decl), wb = occupancy_of(b.rst.new_decl);
    if (wa != wb) return wa > wb;
    return a.facts.n_real < b.facts.n_real;
}

static void compose_lm(DataSet &D, bool fragment, const std::string &uber_key,
                    const std::vector<u32> &c6, const std::string &name,
                    Composed &out) {
    g_perf.n_compose_lm++;
    struct Rung { bool promote, compact; int *pick; };
    static const Rung rungs[] = {
        { true,  false, &g_lm_pick_promote },
        { false, true,  &g_lm_pick_compact },
        { false, false, &g_lm_pick_off     },
    };
    bool want_cp = g_lmem_copyprop;
    for (const Rung &r : rungs) {
        g_lmem_promote = r.promote;
        g_lmem_compact = r.compact;

        Composed best;
        bool have = false, took_cp = false;
        std::exception_ptr err;
        for (int v = (r.promote && want_cp) ? 1 : 0; v >= 0; v--) {
            g_lmem_copyprop = (v != 0);
            Composed c;
            try {
                compose_cp(D, fragment, uber_key, c6, name, c);
            } catch (const std::exception &) {
                if (!err) err = std::current_exception();
                continue;
            }
            if (!have || cheaper(c, best)) {
                best = std::move(c); have = true; took_cp = (v != 0);
            }
        }
        g_lmem_copyprop = want_cp;
        if (!have) {

            if (r.pick != &g_lm_pick_off) continue;
            g_lmem_promote = g_lmem_compact = true;
            std::rethrow_exception(err);
        }
        (*r.pick)++;
        if (took_cp) g_lm_pick_cp++;
        g_lmem_promote = g_lmem_compact = true;
        out = std::move(best);
        return;
    }
}

static int cycles_of_c(const Composed &c) {
    u32 co = const_off(c.ct);
    return issue_cycles(c.bc, co);
}
static bool better_c(const Composed &a, const Composed &b) {
    int wa = occupancy_of(a.rst.new_decl), wb = occupancy_of(b.rst.new_decl);
    if (wa != wb) return wa > wb;
    int ya = cycles_of_c(a), yb = cycles_of_c(b);
    if (ya != yb) return ya < yb;
    return a.facts.n_real < b.facts.n_real;
}

bool g_cbfold_force = false;
bool g_cse_force    = false;
bool g_idfold_force = false;
bool g_fmac_force   = false;

int g_alg_cb_kept = 0, g_alg_cse_kept = 0, g_alg_id_kept = 0, g_alg_fm_kept = 0;
int g_alg_base = 0, g_alg_rows = 0;

struct AlgCounters { int lmp, lmc, lmo, lmcp, rpo, rpk, rpocc; };
static AlgCounters alg_snap() {
    return {g_lm_pick_promote, g_lm_pick_compact, g_lm_pick_off, g_lm_pick_cp,
            g_rp_offered_n, g_rp_kept_n, g_rp_occ_n};
}
static void alg_restore(const AlgCounters &c) {
    g_lm_pick_promote = c.lmp; g_lm_pick_compact = c.lmc;
    g_lm_pick_off = c.lmo;     g_lm_pick_cp = c.lmcp;
    g_rp_offered_n = c.rpo;    g_rp_kept_n = c.rpk;  g_rp_occ_n = c.rpocc;
}

static void compose(DataSet &D, bool fragment, const std::string &uber_key,
                    const std::vector<u32> &c6, const std::string &name,
                    Composed &out) {
    g_perf.n_compose_top++;

    renumber_cache_clear();
    fill_cache_clear();
    run3_cache_clear();

    if (g_quick) { compose_one(D, fragment, uber_key, c6, name, out); return; }
    bool want[3] = {g_cbfold, g_cse_mov32i, g_idfold};
    bool forced[3] = {g_cbfold_force, g_cse_force, g_idfold_force};
    bool g[3];
    int nguard = 0;
    for (int t = 0; t < 3; t++) { g[t] = want[t] && !forced[t]; nguard += g[t]; }

    bool fm_want = g_fmac, fm_guard = g_fmac && !g_fmac_force;
    if (!nguard && !fm_guard) {
        compose_lm(D, fragment, uber_key, c6, name, out);
        return;
    }
    if (fm_guard) g_fmac = false;
    auto setflags = [&](int m) {
        bool v[3];
        for (int t = 0; t < 3; t++) v[t] = g[t] ? ((m >> t) & 1) != 0 : want[t];
        g_cbfold = v[0]; g_cse_mov32i = v[1]; g_idfold = v[2];
    };

    AlgCounters c0 = alg_snap();
    setflags(0);
    Composed base;
    compose_lm(D, fragment, uber_key, c6, name, base);
    AlgCounters cbase = alg_snap();
    int base_cyc = cycles_of_c(base), base_warps = occupancy_of(base.rst.new_decl);

    Composed best; bool have = false; int bestm = 0;
    AlgCounters cbest = cbase;
    for (int m = 1; m < 8; m++) {
        bool skip = false;
        for (int t = 0; t < 3; t++) if (((m >> t) & 1) && !g[t]) skip = true;
        if (skip) continue;
        alg_restore(c0);
        setflags(m);
        Composed c;
        try {
            compose_lm(D, fragment, uber_key, c6, name, c);
        } catch (const std::exception &) { continue; }

        int w = occupancy_of(c.rst.new_decl), cy = cycles_of_c(c);
        if (w < base_warps || (w == base_warps && cy > base_cyc)) continue;
        if (!have || better_c(c, best)) {
            best = std::move(c); have = true; bestm = m; cbest = alg_snap();
        }
    }
    g_alg_rows++;
    Composed chosen;
    AlgCounters cchosen;
    int chosenm = 0;
    if (have) {
        if (bestm & 1) g_alg_cb_kept++;
        if (bestm & 2) g_alg_cse_kept++;
        if (bestm & 4) g_alg_id_kept++;
        chosen = std::move(best); cchosen = cbest; chosenm = bestm;
    } else {
        g_alg_base++;
        chosen = std::move(base); cchosen = cbase; chosenm = 0;
    }

    if (fm_guard) {
        int cw = occupancy_of(chosen.rst.new_decl), cy0 = cycles_of_c(chosen);
        alg_restore(c0);
        setflags(chosenm);
        g_fmac = true;
        Composed c;
        bool okc = true;
        try {
            compose_lm(D, fragment, uber_key, c6, name, c);
        } catch (const std::exception &) { okc = false; }
        g_fmac = false;
        if (okc) {
            int w = occupancy_of(c.rst.new_decl), cy = cycles_of_c(c);
            if (!(w < cw || (w == cw && cy > cy0)) && better_c(c, chosen)) {
                chosen = std::move(c); cchosen = alg_snap(); g_alg_fm_kept++;
            }
        }
    }

    g_cbfold = want[0]; g_cse_mov32i = want[1]; g_idfold = want[2];
    g_fmac = fm_want;
    alg_restore(cchosen);
    out = std::move(chosen);
}

static void write_pair(const std::string &dir, const std::string &name,
                       const Composed &c) {
    mkdirs(dir);
    spit(dir + "/" + name + "_bytecode.bin", c.bc);
    spit(dir + "/" + name + "_control.bin", c.ct);
}

static std::string content_name(const std::vector<u8> &bc) {
    if (bc.size() <= (size_t)SPH_OFF)
        fail("the emitted bytecode is %zu bytes, which is not a program to "
             "name", bc.size());
    char h[17];
    snprintf(h, sizeof h, "%016llx",
             (unsigned long long)xxh3_64(bc.data() + SPH_OFF,
                                         bc.size() - (size_t)SPH_OFF));
    return std::string(h);
}





struct ProfRec {
    int cycles = 0, instrs = 0, temp = 0, warps = 0;
    u32 lmem = 0;
    size_t bytes = 0;

    int maxlive = 0, over48 = 0, over56 = 0, nnames = 0, nwebs = 0;
};

static bool g_press = false;

struct StallRec {
    long long n = 0, cyc = 0, npair = 0, nwait = 0, cycwait = 0;
    long long nsetw = 0, nsetr = 0, nreuse = 0, nbank = 0, sbank = 0;
    long long cycfloor = 0;
};

struct ChainRec {
    long long stallhist[32] = {0};
    long long dist[65] = {0};
    long long ndist = 0, sumdist = 0;
    long long nodef = 0;
    long long nslots = 0;
};









static void profile_pair(const std::vector<u8> &bc, const std::vector<u8> &ct,
                         ProfRec &p) {
    if (ct.size() < (offsetof(NVNshaderControl, mPerWarpScratchSize) + 4))
        fail("control blob is too small to profile (%zu bytes)", ct.size());
    u32 co = const_off(ct);
    if (co > bc.size()) fail("ConstBufOffset past the end of the bytecode");
    p.cycles = issue_cycles(bc, co);
    CtlFacts f;
    control_facts(bc, ct, f);
    p.instrs = f.n_real;
    const NVNshaderControl *c = ctl(ct);
    p.temp = (int)c->mProgramRegNum;
    p.lmem = c->mPerWarpScratchSize;

    p.warps = occupancy_of(p.temp);
    p.bytes = bc.size();
    if (g_press) {
        PressFacts pf;
        pressure_facts(bc, ct, pf);
        p.maxlive = pf.maxlive; p.over48 = pf.over48; p.over56 = pf.over56;
        p.nnames = pf.nnames; p.nwebs = pf.nwebs;
    }
}










extern "C" int ub_slot_du(const unsigned char *bc, unsigned int constOff,
                          unsigned char *out, int stride, int *opout, int maxn);





static void report_unexpressed(const DataSet &D,
                               const std::map<std::string, std::string> &all,
                               bool fragment, const std::string &uber_key) {
    const char *sn = stage_name(fragment);
    for (const auto &pr : all)
        if (!D.by_name.count(pr.first))
            fprintf(stderr, "warning: %s: no such option in %s; ignored\n",
                    pr.first.c_str(), D.table_path.c_str());

    static const char *const kSelectors[] = { "gsys_assign_type", "gsys_weight" };
    for (const auto &pr : all) {
        auto oi = D.by_name.find(pr.first);
        if (oi == D.by_name.end()) continue;
        bool sel = false;
        for (const char *s : kSelectors) sel = sel || pr.first == s;
        if (sel) continue;
        const OptionRec &rec = D.options[oi->second];
        if (rec.default_choice_idx >= 0 &&
            (size_t)rec.default_choice_idx < rec.choice_names.size() &&
            rec.choice_names[(size_t)rec.default_choice_idx] == pr.second)
            continue;
        switch (option_reach(D, fragment, uber_key, pr.first)) {
        case REACH_OK:
            break;
        case REACH_NO_SLOT:
            fprintf(stderr,
                    "warning: %s=%s: this option is not a member of the option "
                    "buffer in %s, so no ubershader can carry it - the "
                    "feature will be absent from the %s result\n",
                    pr.first.c_str(), pr.second.c_str(), D.table_path.c_str(),
                    sn);
            break;
        case REACH_UNREAD: {

            std::string ubc, uct;
            uber_paths(fragment, uber_key, ubc, uct);
            fprintf(stderr, "note: %s is never read in %s and doesn't affect "
                            "output\n",
                    pr.first.c_str(), basename_of(ubc).c_str());
            break;
        }
        }
    }
}

static int cmd_native(DataSet &D, bool fragment,
                      const std::string &optfile, const std::string &outdir,
                      const std::string &name, bool gate) {
    std::string txt = slurp_text(optfile);
    std::map<std::string, std::string> all;
    size_t i = 0;
    while (i < txt.size()) {
        size_t e = txt.find('\n', i);
        if (e == std::string::npos) e = txt.size();
        std::string line = txt.substr(i, e - i);
        i = e + 1;
        while (!line.empty() && (line.back() == '\r' || line.back() == ' '))
            line.pop_back();
        if (line.empty()) continue;
        size_t eq = line.find('=');
        if (eq == std::string::npos) continue;
        all[line.substr(0, eq)] = line.substr(eq + 1);
    }

    std::string uber = fragment ? std::string()
                                : (all.count("gsys_weight") ? all["gsys_weight"]
                                                            : std::string());
    report_unexpressed(D, all, fragment, uber);

    std::map<std::string, std::string> ov;
    for (auto &pr : all) {
        auto it = D.by_name.find(pr.first);
        if (it == D.by_name.end()) continue;
        if (std::find(D.c6_order.begin(), D.c6_order.end(), pr.first) ==
            D.c6_order.end())
            continue;
        ov[pr.first] = pr.second;
    }
    std::vector<u32> c6 = D.build_c6(ov, nullptr);

    Composed c;
    compose(D, fragment, uber, c6, name, c);

    const std::string out_name = name.empty() ? content_name(c.bc) : name;
    write_pair(outdir, out_name, c);

    if (name.empty())
        printf("%s/%s_bytecode.bin\n%s/%s_control.bin\n",
               outdir.c_str(), out_name.c_str(),
               outdir.c_str(), out_name.c_str());
    if (!gate) return 0;

    GateResult R;
    verify(c.bc, c.ct,   true, R, nullptr, nullptr,
           c.has_pre ? &c.pre_bc : nullptr, c.has_pre ? &c.pre_ct : nullptr);
    for (auto &r : R.rows)
        printf("  %-14s %-4s  %s\n", std::get<0>(r).c_str(),
               std::get<1>(r) ? "PASS" : "FAIL", std::get<2>(r).c_str());
    u32 co = const_off(c.ct);
    printf("%-30s instrs %5d  cycles %6d  temp %3d  warps %2d  lmem %6u  "
           "bytes %6zu%s\n",
           out_name.c_str(), c.st.n_emit, issue_cycles(c.bc, co),
           c.facts.gpr_count, occupancy_of(c.facts.gpr_count),
           c.facts.lmem_bytes, c.bc.size(),
           c.ro.v11_violations ? "  V11 VIOLATED" : "");
    return R.nbad();
}

static int cmd_gate(const std::string &bcp, const std::string &ctp,
                    const std::string &obc, const std::string &oct) {
    std::vector<u8> bc = read_file(bcp), ct = read_file(ctp);
    GateResult R;
    if (!obc.empty()) {
        std::vector<u8> a = read_file(obc), b = read_file(oct);
        verify(bc, ct, true, R, &a, &b);
    } else verify(bc, ct, true, R);
    for (auto &r : R.rows)
        printf("%-14s %s  %s\n", std::get<0>(r).c_str(),
               std::get<1>(r) ? "PASS" : "FAIL", std::get<2>(r).c_str());

    ProfRec p;
    profile_pair(bc, ct, p);
    printf("profile        instrs %5d  cycles %6d  temp %3d  warps %2d  "
           "lmem %6u  bytes %6zu\n",
           p.instrs, p.cycles, p.temp, p.warps, p.lmem, p.bytes);
    return R.nbad() ? 1 : 0;
}


struct ShipFlag { const char *name; bool *flag; bool dflt; };
static const ShipFlag g_ship_flags[] = {
    { "reorder",       &g_reorder,       true  },
    { "fill",          &g_fill,          true  },
    { "copyprop",      &g_copyprop,      true  },
    { "rp-split",      &g_rp_split,      true  },
    { "rp-defrelax",   &g_rp_defrelax,   true  },
    { "idfold",        &g_idfold,        true  },
    { "cse-mov32i",    &g_cse_mov32i,    true  },
    { "cbfold",        &g_cbfold,        true  },
    { "fmac",          &g_fmac,          true  },
    { "bank",          &g_bank,          true  },
    { "anti",          &g_anti,          true  },

    { "dce2",          &g_dce2,          true  },

    { "texnarrow",     &g_texnarrow,     true  },
};


static const char kUsage[] =
    "usage:\n"
    "  uberspec --options-file F --out DIR [--name N] --uber <bytecode.bin>\n"
    "           --options-table T --option-bank N\n"
    "  uberspec gate <bytecode.bin> <control.bin> [<ref_bc> <ref_ct>]\n"
    "\n"
    "  --quick                  one shot compile without testing optimal\n"
    "                           ~20x faster(good for preview) but suboptimal\n"
    "                           output\n"
    "  --gate                   run structural verification gates\n"
    "  --out DIR --name N       writes <N>_bytecode.bin and <N>_control.bin;\n"
    "                           without --name, N is hash of the emitted code.\n"
    "\n"
    "ubershader inputs(required):\n"
    "  --uber <bytecode.bin>            the program to specialise\n"
    "  --uber-control <control.bin>     (else the _control.bin)\n"
    "  --options-table <options.json>             option -> option-buffer slot\n"
    "  --option-bank N                  the constant bank this stage binds the\n"
    "                                   option block to\n"
    "\n";
static int run(int argc, char **argv) {
    std::string arg_optfile, arg_out, arg_name, arg_data;
    std::string arg_rows, arg_table, arg_csv;
    std::string cmd;
    std::vector<UberArg> uargs;
    int arg_bank = -1;
    bool gate = false;

    std::vector<std::string> pos;
    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        auto next = [&]() -> std::string {
            if (i + 1 >= argc) fail("%s needs a value", a.c_str());
            return argv[++i];
        };

        if (a == "--model") (void)next();
        else if (a == "--options-file") arg_optfile = next();
        else if (a == "--out" || a == "--outdir") arg_out = next();
        else if (a == "--name") arg_name = next();
        else if (a == "--options-table") arg_table = next();
        else if (a == "--uber") uber_arg(uargs, next(), -1, false);
        else if (a == "--uber-control") uber_arg(uargs, next(), -1, true);

        else if (a == "--uber-fragment") uber_arg(uargs, next(), 1, false);
        else if (a == "--uber-fragment-control") uber_arg(uargs, next(), 1, true);
        else if (a == "--uber-vertex") uber_arg(uargs, next(), 0, false);
        else if (a == "--uber-vertex-control") uber_arg(uargs, next(), 0, true);
        else if (a == "--option-bank") arg_bank = atoi(next().c_str());
        else if (a == "--option-bank-fragment") g_uber[1].bank = atoi(next().c_str());
        else if (a == "--option-bank-vertex") g_uber[0].bank = atoi(next().c_str());







        else if (a == "--gate") gate = true;
                else if (a == "--quick") g_quick = true;
        else if (a == "--level") {

            next();
        } else if (a.size() > 2 && a[0] == '-' && a[1] == '-')
            fail("unknown option %s", a.c_str());
        else pos.push_back(a);
    }
    if (!pos.empty()) cmd = pos[0];

    if (cmd == "codegen") {
        printf("%u\n", UBERSPEC_CODEGEN_VER);
        return 0;
    }

    for (const ShipFlag &f : g_ship_flags) *f.flag = true;
    if (g_pa_anti) uber_set_pa_anti(1);

    resolve_uber_args(uargs);
    if (arg_bank >= 0) {

        bool hf = !g_uber[1].bc.empty(), hv = !g_uber[0].bc.empty();
        if (hf == hv)
            fail("--option-bank is for a run with one stage loaded; this one "
                 "has %s - use --option-bank-fragment / --option-bank-vertex",
                 hf ? "both" : "neither");
        g_uber[hf ? 1 : 0].bank = arg_bank;
    }

    if (cmd == "gate") {
        if (pos.size() < 3)
            fail("gate needs <bytecode.bin> <control.bin> "
                 "[<ref_bytecode.bin> <ref_control.bin>]");
        return cmd_gate(pos[1], pos[2], pos.size() > 4 ? pos[3] : "",
                        pos.size() > 4 ? pos[4] : "");
    }

    if (cmd.empty() && arg_optfile.empty()) {
        fprintf(stderr, "%s", kUsage);
        return 1;
    }

    DataSet D;
    D.load(arg_data, arg_table);


    if (!arg_optfile.empty()) {
        if (arg_out.empty()) fail("--out is required");

        bool hf = !g_uber[1].bc.empty(), hv = !g_uber[0].bc.empty();
        if (!hf && !hv)
            fail("no ubershader: pass --uber <bytecode.bin>");
        if (hf && hv)
            fail("ubershaders for both stages were passed; pass only the one "
                 "to specialise - the stage is read out of it");
        bool fragment = hf;
        check_stage(stage_name(fragment));
        return cmd_native(D, fragment, arg_optfile, arg_out, arg_name,
                          gate) ? 1 : 0;
    }
    fprintf(stderr, "%s", kUsage);
    return 1;
}


}

int main(int argc, char **argv) {
    try {
        int rc = ub::run(argc, argv);
        return rc;
    } catch (const std::exception &e) {
        fprintf(stderr, "error: %s\n", e.what());
        return 2;
    }
}
