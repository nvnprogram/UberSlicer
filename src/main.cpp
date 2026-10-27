
#include <exception>
#include <numeric>
#include "emit.h"
#include "sm50/nv_sched_ctl.h"

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

int g_maskw = 5;

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
    std::string table_path;
    std::vector<OptionRec> options;
    std::map<std::string, size_t> by_name;
    std::vector<std::string> c6_order;

    std::map<std::string, int> c6_slot;
    std::vector<std::string> option_order;
    std::map<std::string, size_t> oidx;

    void load(const std::string &tablePath) {
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

template <class I> struct UberCtxT {
    ProgramT<I> prog;
    SpecT<I> sp;
};

static bool g_reorder = false;
static bool g_reorder2 = false;
static bool g_texsb = false;
static bool g_fill = false;
static int  g_fill_rounds = 8;
static bool g_cbfold = false;

template <class I> static std::map<std::string, UberCtxT<I> *> g_ctx;

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
    std::vector<u8> bc = read_file(bcp);
    u32 magic = 0;
    if (bc.size() >= 4) std::memcpy(&magic, bc.data(), 4);
    bool f;
    if (magic == NVN_PROGRAM_MAGIC) {
        f = bytecode_is_fragment(bc, bcp.c_str());
    } else {
        if (bc.size() < 4) fail("%s: too short for an NVN2 shader header", bcp.c_str());
        f = (bc[0] & 0x1f) == 2;
    }
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

enum class IsaId { None, Sm50, Sm86 };

struct InputIsa {
    IsaId id = IsaId::None;
    std::string path;
    std::string what;
};

static const char *isa_gen(IsaId k) { return k == IsaId::Sm50 ? "NVN1" : "NVN2"; }

static IsaId parse_mode(const std::string &s) {
    if (s == "nvn") return IsaId::Sm50;
    if (s == "nvn2") return IsaId::Sm86;
    fail("--mode %s: expected nvn or nvn2", s.c_str());
}

static void reject_container(const std::vector<u8> &b, const std::string &path) {
    if (b.size() < 12) return;
    const char *kind = !std::memcmp(b.data(), "FSHA", 4)   ? "bfsha"
                       : !std::memcmp(b.data(), "BNSH", 4) ? "BNSH"
                                                           : nullptr;
    if (kind)
        fail("%s is a %s container, version %u.%u.%u, not one stage program: "
             "pass the stage's _bytecode.bin and _control.bin", path.c_str(), kind,
             (unsigned)(b[10] | b[11] << 8), (unsigned)b[9], (unsigned)b[8]);
}

static InputIsa read_isa(const std::string &bcp, const std::string &ctp) {
    InputIsa k;
    k.path = ctp;
    if (!exists(ctp)) {
        k.what = "it does not exist";
        return k;
    }
    std::vector<u8> ct = read_file(ctp);
    reject_container(ct, ctp);
    u32 magic = 0, major = 0, minor = 0;
    uint16_t arch = 0;
    if (ct.size() >= 4) std::memcpy(&magic, ct.data(), 4);
    char buf[256];
    if (ct.size() < 16 || magic != NVN_CONTROL_MAGIC) {
        snprintf(buf, sizeof buf, "%zu bytes opening with %08x, where a control "
                 "section opens with %08x", ct.size(), magic, NVN_CONTROL_MAGIC);
        k.what = buf;
        return k;
    }
    std::memcpy(&major, ct.data() + 4, 4);
    std::memcpy(&minor, ct.data() + 8, 4);
    std::memcpy(&arch, ct.data() + 12, 2);
    snprintf(buf, sizeof buf, "control version %u.%u, architecture 0x%x", major,
             minor, (unsigned)arch);
    k.what = buf;
    if (major == 1 && arch == 0x120) k.id = IsaId::Sm50;
    else if ((major == 200 || major == 201) && arch == 0x170) k.id = IsaId::Sm86;
    if (k.id == IsaId::Sm86 && exists(bcp)) {
        std::vector<u8> bc = read_file(bcp);
        reject_container(bc, bcp);
        u32 pm = 0;
        if (bc.size() >= 4) std::memcpy(&pm, bc.data(), 4);
        if (pm == NVN_PROGRAM_MAGIC)
            fail("%s is NVN2 (%s) but %s opens with the NVN1 program magic %08x: "
                 "they are not one program", ctp.c_str(), k.what.c_str(),
                 bcp.c_str(), pm);
    }
    return k;
}

static IsaId detect_isa(const std::string &bcp, const std::string &ctp, IsaId mode) {
    const InputIsa k = read_isa(bcp, ctp);
    if (k.id != IsaId::None) {
        if (mode != IsaId::None && mode != k.id)
            fail("--mode %s, but %s is an %s program (%s)",
                 mode == IsaId::Sm50 ? "nvn" : "nvn2", k.path.c_str(),
                 isa_gen(k.id), k.what.c_str());
        return k.id;
    }
    if (mode != IsaId::None) return mode;
    fail("cannot tell which GPU %s is for (%s); pass --mode nvn or --mode nvn2",
         k.path.c_str(), k.what.c_str());
}

[[noreturn]] static void nvn2_missing(const std::string &path) {
    fail("NVN2 backend not implemented yet: %s is for NVN2", path.c_str());
}

static IsaId uber_isa(const std::vector<UberArg> &v, IsaId mode, std::string &where) {
    IsaId got = IsaId::None;
    for (const UberArg &a : v) {
        if (a.control || !exists(a.path)) continue;
        std::string ctp;
        for (const UberArg &c : v)
            if (c.control && c.key == a.key &&
                (c.stage < 0 || a.stage < 0 || c.stage == a.stage)) {
                ctp = c.path;
                break;
            }
        if (ctp.empty()) ctp = control_sibling(a.path);
        IsaId k = detect_isa(a.path, ctp, mode);
        if (got != IsaId::None && k != got)
            fail("%s is for %s and %s is for %s: one run is for one GPU",
                 where.c_str(), isa_gen(got), a.path.c_str(), isa_gen(k));
        if (got == IsaId::None) { got = k; where = a.path; }
    }
    return got;
}

static void program_isa(const std::string &bcp, const std::string &ctp, IsaId mode) {
    if (detect_isa(bcp, ctp, mode) == IsaId::Sm86) nvn2_missing(bcp);
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

template <class I>
static UberCtxT<I> *get_ctx(DataSet &D, bool fragment, const std::string &uber_key,
                            bool redundancy) {
    (void)D;
    std::string bcp, ctp;
    uber_paths(fragment, uber_key, bcp, ctp);

    std::string key = (fragment ? "F:" : "V:") + bcp + "|" + ctp +
                      (redundancy ? ":6" : ":5") + (g_cbfold ? ":cb" : "") +
                      (g_cse_mov32i ? ":cse" : "");
    auto it = g_ctx<I>.find(key);
    if (it != g_ctx<I>.end()) return it->second;
    UberCtxT<I> *c = new UberCtxT<I>();
    c->prog.load_paths(bcp, ctp);

    std::vector<int> exit_live;
    if (fragment) I::exit_live_regs(c->prog.bc, exit_live);

    int folds = redundancy ? FOLD_ALL : 0;
    c->sp.init(c->prog, uber_bank(fragment), exit_live,
                 true,   g_cbfold, folds,
                 redundancy);
    g_ctx<I>[key] = c;
    return c;
}

template <class I>
static void option_slots_read(const ProgramT<I> &p, int bank, std::set<int> &out) {
    for (int i = 0; i < p.n; i++) {
        typename I::Word q = p.q[i];
        if (I::empty(q)) continue;
        int b, o;

        if (I::cbuf_read(q, p.op[i], &b, &o) && b == bank) out.insert(o >> 2);
    }
}

template <class I> static std::map<std::string, std::set<int>> g_slots_read;
template <class I = Sm50>
static const std::set<int> &uber_slots_read(bool fragment,
                                            const std::string &key) {
    std::string bcp, ctp;
    uber_paths(fragment, key, bcp, ctp);
    auto it = g_slots_read<I>.find(bcp);
    if (it != g_slots_read<I>.end()) return it->second;
    ProgramT<I> p;
    p.load_paths(bcp, ctp);
    std::set<int> s;
    option_slots_read(p, uber_bank(fragment), s);
    return g_slots_read<I>.emplace(bcp, std::move(s)).first->second;
}

enum OptionReach { REACH_OK = 0, REACH_NO_SLOT, REACH_UNREAD };

template <class I = Sm50>
static OptionReach option_reach(const DataSet &D, bool fragment,
                                const std::string &key, const std::string &nm) {
    auto sit = D.c6_slot.find(nm);
    if (sit == D.c6_slot.end()) return REACH_NO_SLOT;
    return uber_slots_read<I>(fragment, key).count(sit->second) ? REACH_OK
                                                            : REACH_UNREAD;
}

static bool g_quick = false;

struct Composed {
    std::vector<u8> bc, ct;
    EmitStats st;
    RegStats rst;
    CtlFacts facts;
    TexNarrowStats tn;
    AnticopyStats ac;
    SinkStats sk;
    VnStats vn;
    std::vector<u8> pre_bc, pre_ct;
    bool has_pre = false;

    bool occ_floored = false;
};

template <class I>
static void compose_tail(bool fragment, Composed &out, int need_warps = 0);

struct TailEntry {
    Composed c;
};
template <class I> static std::map<std::string, TailEntry> g_tail_cache;
template <class I> static void tail_cache_clear() { g_tail_cache<I>.clear(); }

template <class I>
static void compose_one_tail(bool fragment, Composed &out);

template <class I>
static void compose_one(DataSet &D, bool fragment, const std::string &uber_key,
                        const std::vector<u32> &c6, const std::string &name,
                        Composed &out) {
    UberCtxT<I> *c = get_ctx<I>(D, fragment, uber_key, true);
    emit(c->prog, c->sp, c6, name, out.st);
    out.bc = out.st.bc;
    out.ct = out.st.ct;

    std::string key;
    key.reserve(out.bc.size() + out.ct.size() + 1);
    key.push_back(fragment ? 'F' : 'V');
    key.append((const char *)out.bc.data(), out.bc.size());
    key.append((const char *)out.ct.data(), out.ct.size());
    auto tit = g_tail_cache<I>.find(key);
    if (tit != g_tail_cache<I>.end()) {
        EmitStats keep = std::move(out.st);
        out = tit->second.c;
        out.st = std::move(keep);
        return;
    }
    compose_one_tail<I>(fragment, out);
    TailEntry e;
    EmitStats keep = std::move(out.st);
    out.st = EmitStats();
    e.c = out;
    out.st = std::move(keep);
    g_tail_cache<I>.emplace(std::move(key), std::move(e));
}

static const int VN_REACH[] = {1 << 30, 128, 16};

static int g_vn_row = -2;

static bool g_vn_inline = false;

template <class I>
static void compose_one_tail(bool fragment, Composed &out) {

    bool have_ref = false;
    Composed ref;
    if (g_vn && (g_vn_inline || g_vn_row >= 0)) {
        vn_cse<I>(out.bc, out.ct, fragment, out.vn,
               VN_REACH[g_vn_inline ? 0 : g_vn_row]);
    } else if (g_vn && g_vn_row == -2) {
        Composed base;
        bool base_done = false;
        for (size_t z = 0; z < sizeof VN_REACH / sizeof VN_REACH[0]; z++) {
            Composed cand = out;
            vn_cse<I>(cand.bc, cand.ct, fragment, cand.vn, VN_REACH[z]);
            if (!cand.vn.rounds) break;
            if (!base_done) {
                base = out;
                compose_tail<I>(fragment, base);
                base_done = true;
                g_vn_row = -1;
            }
            const Composed stream = cand;
            const int wo = base.occ_floored ? 0
                                            : I::occupancy_of(base.rst.new_decl);
            compose_tail<I>(fragment, cand, wo);
            bool win = !cand.occ_floored &&
                       (base.occ_floored ||
                        (I::occupancy_of(cand.rst.new_decl) >= wo &&
                         I::issue_cycles(cand.bc, I::const_off(cand.ct)) <=
                             I::issue_cycles(base.bc, I::const_off(base.ct))));
            if (win) {
                out.bc = stream.bc; out.ct = stream.ct; out.vn = stream.vn;
                ref = std::move(cand);
                have_ref = true;
                g_vn_row = (int)z;
                break;
            }
        }
        if (!have_ref && base_done) { ref = std::move(base); have_ref = true; }
    }

    auto tail_of = [&](Composed &c) {
        if (have_ref && &c == &out) { EmitStats k = std::move(c.st);
                                      AnticopyStats a = c.ac;
                                      VnStats v = c.vn;
                                      c = ref; c.st = std::move(k);
                                      c.ac = a; c.vn = v; return; }
        compose_tail<I>(fragment, c);
    };

    if (g_anticopy) {
        const Composed base = out;

        auto run = [&](long long budget, Composed &alt) {
            alt = base;
            g_ac_budget = budget;
            for (int round = 0; round < 3; round++) {
                AnticopyStats s1;
                std::vector<u8> keep_bc = alt.bc, keep_ct = alt.ct;
                try {
                    anticopy<I>(alt.bc, alt.ct, fragment, s1);
                } catch (const std::exception &e) {

                    alt.bc.swap(keep_bc); alt.ct.swap(keep_ct);
                    s1 = AnticopyStats();
                }
                alt.ac.applied += s1.applied;
                if (!s1.applied) break;
            }
            g_ac_budget = -1;
        };
        long long budget = -1;
        Composed alt;
        run(budget, alt);
        if (alt.ac.applied == 0) { out.ac = alt.ac; tail_of(out); return; }

        tail_of(out);
        const int wo = I::occupancy_of(out.rst.new_decl);
        const int cb = I::issue_cycles(out.bc, I::const_off(out.ct));
        compose_tail<I>(fragment, alt, wo);

        long long applied = alt.ac.applied;
        for (int step = 0; ; step++) {
            const int wa = alt.occ_floored ? -1 : I::occupancy_of(alt.rst.new_decl);
            if (wa >= wo && I::issue_cycles(alt.bc, I::const_off(alt.ct)) < cb) {
                out = std::move(alt);
                return;
            }
            if (wa >= wo || step >= 3) break;
            applied /= 2;
            if (applied < 1) break;
            Composed next;
            run(applied, next);
            if (next.ac.applied == 0) break;
            compose_tail<I>(fragment, next, wo);
            alt = std::move(next);
        }
        return;
    }
    tail_of(out);
}

template <class I>
static void renumber_sink(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
                          RegStats &st, int need_warps, SinkStats &ss) {
    std::vector<u8> s_bc = bc, s_ct = ct;
    SinkStats s1;
    sink_cheap<I>(s_bc, s_ct, fragment, s1);
    ss.moved += s1.moved;
    if (!s1.moved) {
        renumber<I>(bc, ct, fragment,   true, st, need_warps);
        return;
    }
    RegStats rs;
    renumber<I>(s_bc, s_ct, fragment,   true, rs, need_warps);

    const bool bound_wins = !rs.floored && s1.maxlive0 > 0 &&
                            I::occupancy_of(rs.new_decl) > I::occupancy_of(s1.maxlive0);
    bool keep = true;
    if (!bound_wins) {
        renumber<I>(bc, ct, fragment,   true, st, need_warps);
        if (rs.floored && st.floored) return;
        if (rs.floored) keep = false;
        else if (st.floored) keep = true;
        else {

            int wa = I::occupancy_of(rs.new_decl), wb = I::occupancy_of(st.new_decl);
            keep = wa > wb ||
                   (wa == wb && I::early_cycles() &&
                    I::issue_cycles(s_bc, I::const_off(s_ct)) <=
                        I::issue_cycles(bc, I::const_off(ct)));

            if (wa == wb && !I::early_cycles() && st.rp_tuple && !rs.rp_tuple) keep = true;
        }
    }

    if (keep) { bc.swap(s_bc); ct.swap(s_ct); st = rs; }
}

template <class I>
static void compose_tail_inner(bool fragment, Composed &out, int need_warps);
template <class I>
static void compose_tail(bool fragment, Composed &out, int need_warps) {
    compose_tail_inner<I>(fragment, out, need_warps);
}
template <class I>
static void compose_tail_inner(bool fragment, Composed &out, int need_warps) {

    if (g_reorder || g_fill) {
        out.pre_bc = out.bc;
        out.pre_ct = out.ct;
        out.has_pre = true;
        if (g_reorder) {
            I::reorder(out.bc, out.ct, true);
        }

    }
    if (g_fill && !g_quick) {

        std::vector<u8> nf_bc = out.bc, nf_ct = out.ct;
        I::fill_bubbles(out.bc, out.ct, true, g_fill_rounds);

        std::vector<u8> a_bc = out.bc, a_ct = out.ct;
        RegStats ra;
        renumber_sink<I>(a_bc, a_ct, fragment, ra, need_warps, out.sk);

        RegStats rb;
        renumber_sink<I>(nf_bc, nf_ct, fragment, rb,
                      ra.floored ? need_warps : I::occupancy_of(ra.new_decl), out.sk);
        if (ra.floored && rb.floored) { out.occ_floored = true; return; }

        bool keep = false;
        if (!ra.floored) {
            u32 co_a = I::const_off(a_ct), co_b = I::const_off(nf_ct);
            keep = rb.floored ||
                   (I::occupancy_of(ra.new_decl) >= I::occupancy_of(rb.new_decl) &&
                    I::issue_cycles(a_bc, co_a) <= I::issue_cycles(nf_bc, co_b));
        }
        if (keep) {
            out.bc.swap(a_bc); out.ct.swap(a_ct); out.rst = ra;
        } else {
            out.bc.swap(nf_bc); out.ct.swap(nf_ct); out.rst = rb;
        }
    } else {
        if (g_fill) I::fill_bubbles(out.bc, out.ct, true, g_fill_rounds);
        renumber_sink<I>(out.bc, out.ct, fragment, out.rst, need_warps, out.sk);
        if (out.rst.floored) { out.occ_floored = true; return; }
    }

    if (g_reorder2) {
        std::vector<u8> r_bc = out.bc, r_ct = out.ct;
        I::reorder(r_bc, r_ct, true);
        if (I::issue_cycles(r_bc, I::const_off(r_ct)) <=
            I::issue_cycles(out.bc, I::const_off(out.ct))) {
            out.bc.swap(r_bc);
            out.ct.swap(r_ct);
        }
    }

    dce2<I>(out.bc, out.ct, fragment);
    I::control_rewrite(out.bc, out.ct, out.facts);

    if (g_texnarrow) {
        texnarrow<I>(out.bc, out.ct, fragment, out.tn);
    }
}

template <class I>
static void compose_cp(DataSet &D, bool fragment, const std::string &uber_key,
                       const std::vector<u32> &c6, const std::string &name,
                       Composed &out) {
    if (!g_copyprop) {
        compose_one<I>(D, fragment, uber_key, c6, name, out);
        return;
    }
    Composed with, without;
    compose_one<I>(D, fragment, uber_key, c6, name, with);
    g_copyprop = false;
    compose_one<I>(D, fragment, uber_key, c6, name, without);
    g_copyprop = true;

    u32 ca, cb;
    ca = I::const_off(with.ct);
    cb = I::const_off(without.ct);
    bool keep = I::occupancy_of(with.rst.new_decl) >=
                    I::occupancy_of(without.rst.new_decl) &&
                I::issue_cycles(with.bc, ca) <= I::issue_cycles(without.bc, cb);

    if (I::occupancy_first())
        keep = I::occupancy_of(with.rst.new_decl) > I::occupancy_of(without.rst.new_decl) ||
               (I::occupancy_of(with.rst.new_decl) == I::occupancy_of(without.rst.new_decl) &&
                I::issue_cycles(with.bc, ca) <= I::issue_cycles(without.bc, cb));
    out = keep ? std::move(with) : std::move(without);
}

template <class I>
static bool cheaper(const Composed &a, const Composed &b) {
    int wa = I::occupancy_of(a.rst.new_decl), wb = I::occupancy_of(b.rst.new_decl);
    if (wa != wb) return wa > wb;
    u32 ca = I::const_off(a.ct), cb = I::const_off(b.ct);
    int ya = I::issue_cycles(a.bc, ca), yb = I::issue_cycles(b.bc, cb);
    if (ya != yb) return ya < yb;
    return a.facts.n_real < b.facts.n_real;
}

template <class I>
static void compose_lm(DataSet &D, bool fragment, const std::string &uber_key,
                    const std::vector<u32> &c6, const std::string &name,
                    Composed &out) {
    struct Rung { bool promote, compact; };
    static const Rung rungs[] = {
        { true,  false },
        { false, true  },
        { false, false },
    };
    bool want_cp = g_lmem_copyprop;
    for (const Rung &r : rungs) {
        g_lmem_promote = r.promote;
        g_lmem_compact = r.compact;

        Composed best;
        bool have = false;
        std::exception_ptr err;
        for (int v = (r.promote && want_cp) ? 1 : 0; v >= 0; v--) {
            g_lmem_copyprop = (v != 0);
            Composed c;
            try {
                compose_cp<I>(D, fragment, uber_key, c6, name, c);
            } catch (const std::exception &) {
                if (!err) err = std::current_exception();
                continue;
            }
            if (!have || cheaper<I>(c, best)) {
                best = std::move(c); have = true;
            }
        }
        g_lmem_copyprop = want_cp;
        if (!have) {

            if (r.promote || r.compact) continue;
            g_lmem_promote = g_lmem_compact = true;
            std::rethrow_exception(err);
        }
        g_lmem_promote = g_lmem_compact = true;
        out = std::move(best);
        return;
    }
}

template <class I = Sm50>
static void compose(DataSet &D, bool fragment, const std::string &uber_key,
                    const std::vector<u32> &c6, const std::string &name,
                    Composed &out) {

    renumber_cache_clear<I>();
    I::sched_cache_clear();
    run3_cache_clear<I>();
    tail_cache_clear<I>();
    g_vn_row = -2;

    if (g_quick) {
        g_vn_inline = true;
        compose_one<I>(D, fragment, uber_key, c6, name, out);
        g_vn_inline = false;
        return;
    }
    compose_lm<I>(D, fragment, uber_key, c6, name, out);
}

static void write_pair(const std::string &dir, const std::string &name,
                       const Composed &c) {
    mkdirs(dir);
    spit(dir + "/" + name + "_bytecode.bin", c.bc);
    spit(dir + "/" + name + "_control.bin", c.ct);
}

template <class I>
static std::string content_name(const std::vector<u8> &bc) {
    const size_t from = I::program_start();
    if (bc.size() <= from)
        fail("the emitted bytecode is %zu bytes, which is not a program to "
             "name", bc.size());
    char h[17];
    snprintf(h, sizeof h, "%016llx",
             (unsigned long long)xxh3_64(bc.data() + from, bc.size() - from));
    return std::string(h);
}

struct ProfRec {
    int cycles = 0, instrs = 0, temp = 0, warps = 0;

    u32 lmem = 0;
    size_t bytes = 0;
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
}

template <class I>
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
        switch (option_reach<I>(D, fragment, uber_key, pr.first)) {
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

template <class I>
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
    report_unexpressed<I>(D, all, fragment, uber);

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
    compose<I>(D, fragment, uber, c6, name, c);

    const std::string out_name = name.empty() ? content_name<I>(c.bc) : name;
    write_pair(outdir, out_name, c);

    if (name.empty())
        printf("%s/%s_bytecode.bin\n%s/%s_control.bin\n",
               outdir.c_str(), out_name.c_str(),
               outdir.c_str(), out_name.c_str());
    if (!gate) return 0;

    GateResult R;
    I::verify(c.bc, c.ct,   true, R, nullptr, nullptr,
           c.has_pre ? &c.pre_bc : nullptr, c.has_pre ? &c.pre_ct : nullptr);
    for (auto &r : R.rows)
        printf("  %-14s %-4s  %s\n", std::get<0>(r).c_str(),
               std::get<1>(r) ? "PASS" : "FAIL", std::get<2>(r).c_str());
    u32 co = I::const_off(c.ct);
    printf("%-30s instrs %5d  cycles %6d  temp %3d  warps %2d  lmem %6u  "
           "bytes %6zu  weight %6lld  ipadup %3d\n",
           out_name.c_str(), c.st.n_emit, I::issue_cycles(c.bc, co),
           c.facts.gpr_count, I::occupancy_of(c.facts.gpr_count),
           c.facts.lmem_bytes, c.bc.size(), c.facts.rate_weight,
           c.facts.ipa_redundant);
    return R.nbad();
}

static int cmd_gate_sm86(const std::string &bcp, const std::string &ctp) {
    std::vector<u8> bc = read_file(bcp), ct = read_file(ctp);
    GateResult R;
    Sm86::verify(bc, ct, true, R, nullptr, nullptr, nullptr, nullptr);
    for (auto &r : R.rows)
        printf("%-14s %s  %s\n", std::get<0>(r).c_str(),
               std::get<1>(r) ? "PASS" : "FAIL", std::get<2>(r).c_str());
    u32 co = Sm86::const_off(ct);
    int n = 0;
    for (u32 off = 0x80; off + 16 <= co; off += 16) {
        Sm86::Word w;
        std::memcpy(&w.lo, bc.data() + off, 8);
        std::memcpy(&w.hi, bc.data() + off + 8, 8);
        if (w.lo || w.hi) n++;
    }
    printf("profile        instrs %5d  cycles %6d  temp %3d  warps %2d  "
           "bytes %6zu\n",
           n, Sm86::issue_cycles(bc, co), (int)Sm86::reg_count(ct),
           Sm86::occupancy_of((int)Sm86::reg_count(ct)), bc.size());
    return R.nbad() ? 1 : 0;
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
    "  --mode nvn|nvn2                  the GPU the inputs are for; read from\n"
    "                                   their control section when absent\n"
    "\n";
static int run(int argc, char **argv) {
    std::string arg_optfile, arg_out, arg_name, arg_table;
    std::string cmd;
    std::vector<UberArg> uargs;
    int arg_bank = -1;
    IsaId arg_mode = IsaId::None;
    bool gate = false;

    std::vector<std::string> pos;

    std::vector<std::string> av(argv + 1, argv + argc);
    for (size_t i = 0; i < av.size(); i++) {
        std::string a = av[i];
        auto next = [&]() -> std::string {
            if (i + 1 >= av.size()) fail("%s needs a value", a.c_str());
            return av[++i];
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
        else if (a == "--mode") arg_mode = parse_mode(next());
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
    if (cmd == "codegen-nvn2") {
        printf("%u\n", UBERSPEC_CODEGEN_VER_NVN2);
        return 0;
    }

    g_reorder = g_fill = g_copyprop = g_idfold = g_cse_mov32i = g_cbfold = g_fmac = true;
    g_bank = g_anticopy = g_texnarrow = g_vn = g_reorder2 = g_texsb = true;

    std::string uwhere;
    IsaId run_isa = uber_isa(uargs, arg_mode, uwhere);

    if (run_isa == IsaId::Sm86) {
        g_reorder = g_fill = g_anticopy = false;
        g_vn = g_reorder2 = g_bank = g_texnarrow = false;
        g_cbfold = g_fmac = g_idfold = g_cse_mov32i = g_texsb = false;
        g_spill_max = 0;
    }

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
        if (detect_isa(pos[1], pos[2], arg_mode) == IsaId::Sm86)
            return cmd_gate_sm86(pos[1], pos[2]);
        program_isa(pos[1], pos[2], arg_mode);
        return cmd_gate(pos[1], pos[2], pos.size() > 4 ? pos[3] : "",
                        pos.size() > 4 ? pos[4] : "");
    }

    if (cmd.empty() && arg_optfile.empty()) {
        fprintf(stderr, "%s", kUsage);
        return 1;
    }

    DataSet D;
    D.load(arg_table);

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
        if (run_isa == IsaId::Sm86)
            return cmd_native<Sm86>(D, fragment, arg_optfile, arg_out, arg_name,
                                    gate) ? 1 : 0;
        return cmd_native<Sm50>(D, fragment, arg_optfile, arg_out, arg_name,
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
