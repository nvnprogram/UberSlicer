
#include "sb.h"

#include <algorithm>
#include <climits>
#include <cstring>
#include <map>

#include "deps.h"
#include "issue.h"
#include "machine.h"

namespace ub {
namespace sm86 {
namespace sched {

namespace {

const int NUM_SB = 6;
const int FIRST_SB = 0;
const int LAST_SB = NUM_SB - 1;
const int DUMMY_LAST_NO = INT_MAX;
const int MAX_DEPBAR_COUNT = 63;
const int PROFITABLE_DEPBAR_DISTANCE = 10;
const int PSB_REASSIGN_STALL_LIMIT = 100;

int reg_no(const SReg &r) { return r.cls > RC_R ? -1 : r.no; }
bool needs_rd_protection(int cls) { return cls == RC_R; }

enum PredKind { PRED_ALL = 0, PRED_COMP = 29 };

int pred_kind(int reg, int cond, int cls) {
    int idx = reg + (cls == RC_P ? 1 : 8);
    return cond == PRED_COND_TRUE ? idx : PRED_COMP - idx;
}
bool complementary(int a, int b) { return a + b == PRED_COMP; }
int inst_pred_kind(const SInst &s) {
    return s.pred >= 0 ? pred_kind(s.pred, s.pred_cond, s.pred_cls) : PRED_ALL;
}

const int BIAS_CB = 0, BIAS_UP = 16, BIAS_UR = 24, BIAS_CC = 88, BIAS_P = 92, BIAS_PSEUDO = 101,
          BIAS_R = 105, MAX_NUM_REG = BIAS_R + 256;
int reg_bias(int cls, int no) {
    switch (cls) {
    case RC_CB: return BIAS_CB + no;
    case RC_UP: return BIAS_UP + no;
    case RC_UR: return BIAS_UR + no;
    case RC_CC: return BIAS_CC + no;
    case RC_P: return BIAS_P + no;
    case RC_PSEUDO: return BIAS_PSEUDO + no;
    default: return BIAS_R + no;
    }
}

int vsb_class_idx(int cls) {
    switch (cls) {
    case RC_R: return 0;
    case RC_P: return 1;
    case RC_CC: return 2;
    case RC_CB: return 3;
    case RC_UP: return 4;
    case RC_UR: return 5;
    default: return 6;
    }
}

void erase_one(std::vector<int> &v, int x) {
    auto it = std::find(v.begin(), v.end(), x);
    if (it != v.end()) v.erase(it);
}
bool contains(const std::vector<int> &v, int x) { return std::find(v.begin(), v.end(), x) != v.end(); }

struct BitSet {
    std::vector<uint8_t> b;
    void clear(int n) { b.assign(n, 0); }
    void add(int i) {
        if (i >= (int)b.size()) b.resize(i + 1, 0);
        b[i] = 1;
    }
    bool has(int i) const { return i >= 0 && i < (int)b.size() && b[i]; }
    void empty() { std::fill(b.begin(), b.end(), 0); }
    int population() const { return (int)std::count(b.begin(), b.end(), 1); }
    int next(int from) const {
        for (int i = std::max(0, from); i < (int)b.size(); i++)
            if (b[i]) return i;
        return -1;
    }
    bool equal(const BitSet &o) const {
        size_t n = std::max(b.size(), o.b.size());
        for (size_t i = 0; i < n; i++)
            if (has((int)i) != o.has((int)i)) return false;
        return true;
    }
};

bool is_bar(const SInst &s) { return s.sc.sop == SOP_SM70_BAR; }
bool is_depbar(const SInst &s) { return s.sc.sop == SOP_SM70_DEPBAR; }

bool bar_prunes_rd(const SInst &s) {
    return s.pred < 0 && bar_blocks(s.in.cls);
}

enum { PK_NONE = 0, PK_RD = 1, PK_WR = 2, PK_ANY = 3 };
enum { SUBQ_RD = 0, SUBQ_WR = 1, SUBQ_COUNT = 2, SUBQ_NONE = 3 };
enum { PSB_READ, PSB_WRITE };

const int ORDERED_VQ_FIRST = VQ_ORDERED_FIRST, ORDERED_VQ_LAST = VQ_ORDERED_LAST;
const int ORDERED_VQ_COUNT = ORDERED_VQ_LAST - ORDERED_VQ_FIRST + 1;

struct VsbLists {
    std::vector<int> rd, wr, req;
};

struct VsbInfo {
    int pk = PK_NONE;
    int issueOrder = 0;
    int predKind = PRED_ALL;
    std::vector<std::pair<int, int>> regs;
};

struct RegVsbs {
    std::vector<int> rd, wr;
};

struct Pass {
    SbProg &p;
    SbStats *st;
    int shaderType;

    bool HasLLDepbarInst = false, HasLLNonDepbarInst = false, HasReservedSBInst = false,
         HasReservedSB2Inst = false;

    std::vector<std::vector<int>> defsTable, usesTable;
    std::vector<VsbLists> instTable;
    int lastVsb = 0;
    std::vector<int> protectionKind;

    std::vector<VsbInfo> vinfo;
    RegVsbs regInfo[7][256];
    std::vector<int> prepared;
    std::vector<int> queues[ORDERED_VQ_COUNT * SUBQ_COUNT];
    int lastIssueOrder = 0;

    bool DoDepBar = false, LLsbDesignated = false, DoCrossBlock = true, DoReqAcrossBackedge = true;
    int DoDepbarAcrossBackedge = 1;
    bool DoReqCommit = true, DoCrossBlockOnCallee = true;
    bool HMMAReserved = false, LDGDEPBARReserved = false, LLNonDepbarReserved = false,
         LLNonDepbarReservedKnob = false, LLNonDepbarReservedBB = false;
    int HMMAPsb = -1, LLNonDepbarPsb = -1;
    int firstLlsbPsb = 0;
    int psbConsumeInst[NUM_SB], psbConsumeInstNo[NUM_SB], psbExpectedTepid[NUM_SB];
    char psbWriteProtection[NUM_SB];
    std::vector<int> psbProducerInsts[NUM_SB];
    int earliestCarryOut[NUM_SB];
    BitSet writeRegSet;

    struct DepbarItem {
        int count = 0, countOther = 0, predKind = PRED_ALL;
    };
    std::vector<DepbarItem> depTab;
    int firstValidDepbarReg = 0, lastValidDepbarReg = MAX_NUM_REG;

    int leCnt = 0, llAfter = 0, distDepbars = 0, beforeIp = -1, consumerIp = -1;

    struct RegPsbInfo {
        int rd = 0, wr = 0, depbarCnt = 0;
    };
    struct PsbInfo {
        bool used = false;
        BitSet rdRegs, wrRegs;
    };
    std::vector<std::vector<RegPsbInfo>> lvOut;
    PsbInfo lvIn[NUM_SB];
    std::vector<int> lvInRdMask, lvInWrMask;
    std::vector<BitSet> liveRegsLlsb, liveRegsPsb;
    std::map<int, BitSet> llndRdMap, llndWrMap;
    std::vector<std::vector<int>> blockIdxPerFuncLastPsb;

    int curBlock = -1;

    Pass(SbProg &fp, SbStats *fst, int fShader) : p(fp), st(fst), shaderType(fShader) {}

    void hit() {
        if (st) st->assertHits++;
    }

    SInst &S(int node) { return p.nodes[node].s; }
    bool is_inst(int node) const { return node >= 0 && p.nodes[node].kind == SBN_INST; }
    SbBlock &B(int node) { return p.blocks[p.nodes[node].block]; }
    SbBlock &bix(int index) { return p.blocks[index - 1]; }

    VsbLists &lists(int node) {
        int io = S(node).instOrder;
        if (io >= (int)instTable.size()) instTable.resize(io + 1);
        return instTable[io];
    }
    void vm_init(const SbBlock &b) {
        defsTable.assign(b.vsbCount + 1, {});
        usesTable.assign(b.vsbCount + 1, {});
        int maxIo = 0;
        for (int k = p.first_inst((int)(&b - &p.blocks[0])); k != b.eb; k = p.nodes[k].next)
            maxIo = std::max(maxIo, S(k).instOrder);
        instTable.assign(maxIo + 1, VsbLists());
        lastVsb = 0;
    }
    void ensure_vsb(int vsb) {
        if (vsb >= (int)defsTable.size()) {
            defsTable.resize(vsb + 1);
            usesTable.resize(vsb + 1);
        }
        if (vsb >= (int)vinfo.size()) vinfo.resize(vsb + 1);
        if (vsb >= (int)protectionKind.size()) protectionKind.resize(vsb + 1, SUBQ_NONE);
    }
    int new_vsb() {
        ensure_vsb(lastVsb + 1);
        return ++lastVsb;
    }
    void add_rd_vsb(int ip, int vsb) {
        defsTable[vsb].push_back(ip);
        std::vector<int> &l = lists(ip).rd;
        l.insert(l.begin(), vsb);
    }
    void add_wr_vsb(int ip, int vsb) {
        defsTable[vsb].push_back(ip);
        std::vector<int> &l = lists(ip).wr;
        l.insert(l.begin(), vsb);
    }
    void add_req_vsb(int ip, int vsb) {
        std::vector<int> &u = usesTable[vsb];
        u.erase(std::remove(u.begin(), u.end(), ip), u.end());
        u.push_back(ip);
        std::vector<int> &l = lists(ip).req;
        erase_one(l, vsb);
        l.insert(l.begin(), vsb);
    }
    void inst_delete_vsb(int ip, int vsb) {
        VsbLists &l = lists(ip);
        erase_one(l.rd, vsb);
        erase_one(l.wr, vsb);
        erase_one(l.req, vsb);
    }
    void delete_vsb(int vsb) {
        std::vector<int> &d = defsTable[vsb];
        while (!d.empty()) {
            int ip = d.back();
            d.pop_back();
            inst_delete_vsb(ip, vsb);
        }
        std::vector<int> &u = usesTable[vsb];
        while (!u.empty()) {
            int ip = u.back();
            u.pop_back();
            inst_delete_vsb(ip, vsb);
        }
    }
    int single_def(int vsb) {
        if (defsTable[vsb].empty()) {
            hit();
            return -1;
        }
        if (defsTable[vsb].size() != 1) hit();
        return defsTable[vsb].front();
    }

    bool vt_prepared(int vsb) const { return contains(prepared, vsb - 1); }
    bool vt_live(int vsb) const {
        return vsb < (int)vinfo.size() && vinfo[vsb].pk != PK_NONE && !vt_prepared(vsb);
    }
    int vt_pk(int vsb) const { return vt_live(vsb) ? vinfo[vsb].pk : PK_NONE; }

    void protect_reg(int ip, int no, int cls, int vsb, int pk) {
        int ci = vsb_class_idx(cls);
        RegVsbs &r = regInfo[ci][no & 255];
        if (pk & PK_WR)
            if (!contains(r.wr, vsb - 1)) r.wr.push_back(vsb - 1);
        if (pk & PK_RD)
            if (!contains(r.rd, vsb - 1)) r.rd.push_back(vsb - 1);
        VsbInfo &v = vinfo[vsb];
        std::pair<int, int> key(ci, no & 255);
        if (std::find(v.regs.begin(), v.regs.end(), key) == v.regs.end()) v.regs.push_back(key);
        v.pk |= pk;
        if (S(ip).pred >= 0) v.predKind = inst_pred_kind(S(ip));
    }
    void release_protected(int vsb) {
        VsbInfo &v = vinfo[vsb];
        if (v.pk == PK_NONE) hit();
        std::sort(v.regs.begin(), v.regs.end());
        for (auto &cr : v.regs) {
            RegVsbs &r = regInfo[cr.first][cr.second];
            if (v.pk & PK_RD) erase_one(r.rd, vsb - 1);
            if (v.pk & PK_WR) erase_one(r.wr, vsb - 1);
        }
        v.regs.clear();
        v.pk = PK_NONE;
    }
    void prepare_release(int vsb) {
        if (!contains(prepared, vsb - 1)) prepared.push_back(vsb - 1);
    }
    void commit_release() {
        std::vector<int> pr = prepared;
        prepared.clear();
        for (int v : pr) release_protected(v + 1);
    }

    void add_reg_vsbs(std::vector<int> &vsbs, int no, int cls, int pk) {
        const RegVsbs &r = regInfo[vsb_class_idx(cls)][no & 255];
        if (pk & PK_RD)
            for (int v : r.rd)
                if (!contains(vsbs, v + 1)) vsbs.push_back(v + 1);
        if (pk & PK_WR)
            for (int v : r.wr)
                if (!contains(vsbs, v + 1)) vsbs.push_back(v + 1);
    }

    int sovq_idx_inst(int ip) {
        int q = S(ip).sc.vq;
        return (q >= ORDERED_VQ_FIRST && q <= ORDERED_VQ_LAST) ? q - ORDERED_VQ_FIRST : -1;
    }
    int sovq_idx_vsb(int vsb) {
        int d = single_def(vsb);
        return d < 0 ? -1 : sovq_idx_inst(d);
    }
    std::vector<int> *queue(int qi, int subq) {
        int k = qi * SUBQ_COUNT + subq;
        if (subq >= SUBQ_COUNT) hit();
        if (k < 0 || k >= ORDERED_VQ_COUNT * SUBQ_COUNT) return nullptr;
        return &queues[k];
    }

    bool avoid_req_compl(int ip, int vsb) {
        const SInst &s = S(ip);
        return s.pred >= 0 && complementary(inst_pred_kind(s), vinfo[vsb].predKind);
    }

    void analyze_operands(int ip, bool inputs, std::vector<int> &vsbs) {
        const SInst &s = S(ip);
        if (inputs) {
            uint8_t ord[SINST_MAX_REGS];
            int n = rev_regs(s, ord);
            for (int k = 0; k < n; k++) {
                const SReg &r = s.regs[ord[k]];
                if (r.def) continue;
                int no = reg_no(r);
                if (no >= 0) add_reg_vsbs(vsbs, no, r.cls, PK_WR);
            }
        } else {
            for (int k = 0; k < s.nregs; k++) {
                const SReg &r = s.regs[k];
                if (!r.def) break;
                int no = reg_no(r);
                if (no >= 0) add_reg_vsbs(vsbs, no, r.cls, PK_ANY);
            }
        }
    }

    void produce_vsb(int ip, bool input, BitSet &writeR, BitSet &writeUR) {
        const SInst &s = S(ip);
        if (input) {
            uint8_t ord[SINST_MAX_REGS];
            int n = rev_regs(s, ord);
            for (int k = 0; k < n; k++) {
                const SReg &r = s.regs[ord[k]];
                if (r.def) continue;
                int no = reg_no(r);
                if (no >= 0 && needs_rd_protection(r.cls) && !(r.cls == RC_R && writeR.has(no)) &&
                    !(r.cls == RC_UR && writeUR.has(no))) {
                    int v = new_vsb();
                    add_rd_vsb(ip, v);
                    protect_reg(ip, no, r.cls, v, PK_RD);
                }
            }
        } else {
            for (int k = 0; k < s.nregs; k++) {
                const SReg &r = s.regs[k];
                if (!r.def) break;
                int no = reg_no(r);
                if (no >= 0) {
                    int v = new_vsb();
                    add_wr_vsb(ip, v);
                    protect_reg(ip, no, r.cls, v, PK_WR);
                    if (needs_rd_protection(r.cls)) {
                        if (r.cls == RC_R) writeR.add(no);
                        else if (r.cls == RC_UR) writeUR.add(no);
                    }
                }
            }
        }
    }

    bool can_track_cross_block_on_callee(const SbBlock &b) {
        if (!DoCrossBlockOnCallee) return false;
        int last = p.last_node((int)(&b - &p.blocks[0]));
        if (!is_inst(last)) return false;
        const SInst &s = S(last);
        if (!(sb_is_ret(s) || sb_is_retc(s))) return false;
        const SbFunc &f = p.funcs[b.func];
        if (f.abi) return false;

        bool progExit = f.main ? true : sb_ret_is_exit(s);
        return !progExit;
    }

    bool is_final_exit(const SInst &s) {
        return (sb_is_ret(s) || sb_is_retc(s)) && sb_ret_is_exit(s) && shaderType != ST_GS;
    }

    void reset_vsb_pred_if_redef(int ip) {
        const SInst &s = S(ip);
        for (int k = 0; k < s.nregs; k++) {
            const SReg &r = s.regs[k];
            if (!r.def) break;
            int no = reg_no(r);
            if (no >= 0 && (r.cls == RC_P || r.cls == RC_UP)) {
                int kt = pred_kind(no, PRED_COND_TRUE, r.cls), kf = pred_kind(no, PRED_COND_FALSE, r.cls);
                for (int v = 1; v <= lastVsb; v++)
                    if (vt_live(v) && (vinfo[v].predKind == kt || vinfo[v].predKind == kf)) vinfo[v].predKind = PRED_ALL;
            }
        }
    }

    void vsb_do_it(int bi) {
        SbBlock &b = p.blocks[bi];
        BitSet writeR, writeUR;
        for (int ip = p.first_inst(bi); ip != b.eb; ip = p.nodes[ip].next) {
            SInst &s = S(ip);
            std::vector<int> inputVsbs, outputVsbs;
            analyze_operands(ip, true, inputVsbs);
            analyze_operands(ip, false, outputVsbs);
            for (int vsb : inputVsbs) {
                if (avoid_req_compl(ip, vsb)) {
                    s.flags |= GF_PROHIBIT_REUSE;
                    continue;
                }
                add_req_vsb(ip, vsb);
                release_protected(vsb);
                erase_one(outputVsbs, vsb);
                int def = single_def(vsb);
                if (def >= 0) {
                    std::vector<int> rd = lists(def).rd;
                    for (int r : rd) {
                        if (vt_live(r)) {
                            delete_vsb(r);
                            release_protected(r);
                            erase_one(outputVsbs, r);
                        }
                    }
                }
            }
            for (int vsb : outputVsbs) {
                int virtq = sovq_idx_vsb(vsb);
                if (avoid_req_compl(ip, vsb)) continue;
                if (virtq == sovq_idx_inst(ip) && virtq >= 0) continue;
                add_req_vsb(ip, vsb);
                release_protected(vsb);
            }
            if (p.nodes[ip].next == b.eb) {
                if (sb_is_call(s) || sb_is_ret(s) || sb_is_retc(s)) {
                    if (is_final_exit(s)) {
                        if (!sb_is_retc(s)) {
                            for (int v = 1; v <= lastVsb; v++) {
                                if (vt_live(v)) {
                                    if (!usesTable[v].empty()) hit();
                                    delete_vsb(v);
                                    prepare_release(v);
                                }
                            }
                            commit_release();
                        }
                    } else if (!(can_track_cross_block_on_callee(b))) {
                        for (int v = 1; v <= lastVsb; v++) {
                            if (vt_live(v)) {
                                add_req_vsb(ip, v);
                                release_protected(v);
                            }
                        }
                    }
                }
            }
            writeR.clear(257);
            writeUR.clear(65);
            if (s.flags & GF_NEEDS_WRITE_SB) produce_vsb(ip, false, writeR, writeUR);
            if (s.flags & GF_NEEDS_READ_SB) produce_vsb(ip, true, writeR, writeUR);
            if (HasLLNonDepbarInst && p.nodes[ip].next == b.eb) {
                for (int v = 1; v <= lastVsb; v++) {
                    if (vt_pk(v) != PK_WR) continue;
                    if (!usesTable[v].empty()) hit();
                    if (defsTable[v].empty()) continue;
                    int def = defsTable[v].front();
                    const SInst &d = S(def);
                    if ((d.flags & GF_IS_LONG_LAT_MEM_READ) && !(d.flags & GF_USE_HIGH_COST_SB)) {
                        bool HasVsbUse = false;
                        for (int w : lists(def).wr)
                            if (!usesTable[w].empty()) {
                                HasVsbUse = true;
                                break;
                            }
                        if (!HasVsbUse) {
                            b.xBlockLLNonDepbar = true;
                            break;
                        }
                    }
                }
            }
            reset_vsb_pred_if_redef(ip);
        }
    }

    void separate_analyze(std::vector<int> &latest, const std::vector<int> &vsbs) {
        for (int vsb : vsbs) {
            int subq = vsb < (int)protectionKind.size() ? protectionKind[vsb] : SUBQ_NONE;
            int virtq = sovq_idx_vsb(vsb);
            if (virtq < 0) continue;
            std::vector<int> *q = queue(virtq, subq);
            if (q && contains(*q, vsb)) {
                int &acc = latest[virtq * SUBQ_COUNT + subq];
                if (acc < vinfo[vsb].issueOrder) acc = vinfo[vsb].issueOrder;
            }
        }
    }

    void separate_prune(std::vector<int> &vsbs, std::vector<int> &latest) {
        std::vector<int> temp;
        for (int qi = 0; qi < ORDERED_VQ_COUNT; qi++) {
            std::vector<int> &rq = queues[qi * SUBQ_COUNT + SUBQ_RD];
            while (!rq.empty()) {
                int vsb = rq.front();
                int io = vinfo[vsb].issueOrder;
                if (!(io < latest[qi * SUBQ_COUNT + SUBQ_RD] || io <= latest[qi * SUBQ_COUNT + SUBQ_WR])) break;
                rq.erase(rq.begin());
                temp.push_back(vsb);
                delete_vsb(vsb);
            }
            std::vector<int> &wq = queues[qi * SUBQ_COUNT + SUBQ_WR];
            while (!wq.empty()) {
                int vsb = wq.front();
                int io = vinfo[vsb].issueOrder;
                if (!(io < latest[qi * SUBQ_COUNT + SUBQ_WR])) break;
                wq.erase(wq.begin());
                temp.push_back(vsb);
                delete_vsb(vsb);
            }
        }

        std::sort(vsbs.begin(), vsbs.end());
        std::sort(temp.begin(), temp.end());
        {
            std::vector<int> out;
            size_t i = 0, j = 0;
            while (i < vsbs.size() && j < temp.size()) {
                if (vsbs[i] == temp[j]) {
                    i++;
                    j++;
                } else if (vsbs[i] < temp[j]) {
                    out.push_back(vsbs[i++]);
                } else {
                    j++;
                }
            }
            while (i < vsbs.size()) out.push_back(vsbs[i++]);
            vsbs = out;
        }
        for (int vsb : vsbs) {
            int qi = sovq_idx_vsb(vsb);
            if (qi < 0) continue;
            int subq = vsb < (int)protectionKind.size() ? protectionKind[vsb] : SUBQ_NONE;
            std::vector<int> *q = queue(qi, subq);
            if (q) erase_one(*q, vsb);
        }
    }

    void separate_enqueue(int ip) {
        VsbLists &l = lists(ip);
        if (l.rd.empty() && l.wr.empty()) return;
        int qi = sovq_idx_inst(ip);
        if (qi < 0) return;
        ++lastIssueOrder;
        for (int v : l.rd) {
            vinfo[v].issueOrder = lastIssueOrder;
            protectionKind[v] = SUBQ_RD;
            queues[qi * SUBQ_COUNT + SUBQ_RD].push_back(v);
        }
        for (int v : l.wr) {
            vinfo[v].issueOrder = lastIssueOrder;
            protectionKind[v] = SUBQ_WR;
            queues[qi * SUBQ_COUNT + SUBQ_WR].push_back(v);
        }
    }

    void do_separate_pruning(int bi) {
        SbBlock &b = p.blocks[bi];
        std::vector<int> latest(ORDERED_VQ_COUNT * SUBQ_COUNT, -1);
        for (int ip = p.first_inst(bi); ip != b.eb; ip = p.nodes[ip].next) {
            if (is_bar(S(ip)) && bar_prunes_rd(S(ip))) {
                int qi = sovq_idx_inst(ip);
                if (qi > 0) {
                    std::vector<int> &q = queues[qi * SUBQ_COUNT + SUBQ_RD];
                    while (!q.empty()) {
                        int vsb = q.front();
                        q.erase(q.begin());
                        delete_vsb(vsb);
                    }
                }
            }
            std::vector<int> vsbs = lists(ip).req;
            if (!vsbs.empty()) {
                std::fill(latest.begin(), latest.end(), -1);
                separate_analyze(latest, vsbs);
                separate_prune(vsbs, latest);
            }
            separate_enqueue(ip);
        }
    }

    void assign_vsb(int bi) {
        vm_init(p.blocks[bi]);
        vinfo.assign(p.blocks[bi].vsbCount + 2, VsbInfo());
        for (auto &c : regInfo)
            for (auto &r : c) {
                r.rd.clear();
                r.wr.clear();
            }
        prepared.clear();
        for (auto &q : queues) q.clear();
        lastIssueOrder = 0;
        protectionKind.assign(p.blocks[bi].vsbCount + 2, SUBQ_NONE);
        vsb_do_it(bi);
        do_separate_pruning(bi);
    }

    int long_latency_sb() const { return LAST_SB; }
    int hmma_reserved_sb() {
        if (HMMAPsb == -1) HMMAPsb = LLsbDesignated ? long_latency_sb() - 1 : LAST_SB;
        return HMMAPsb;
    }
    int ldgdepbar_reserved_sb() const { return FIRST_SB; }
    int llnd_reserved_sb() {
        if (LLNonDepbarPsb == -1) {
            if (HMMAReserved) LLNonDepbarPsb = hmma_reserved_sb() - 1;
            else LLNonDepbarPsb = LLsbDesignated ? long_latency_sb() - 1 : LAST_SB;
        }
        return LLNonDepbarPsb;
    }
    int first_sb() const { return LDGDEPBARReserved ? ldgdepbar_reserved_sb() + 1 : FIRST_SB; }
    int last_non_ll_sb() const { return LLsbDesignated ? long_latency_sb() - 1 : LAST_SB; }
    int last_sb() {
        if (LLNonDepbarReservedBB) return llnd_reserved_sb() - 1;
        if (HMMAReserved) return hmma_reserved_sb() - 1;
        return LLsbDesignated ? long_latency_sb() - 1 : LAST_SB;
    }
    bool available(int psb) const { return psbConsumeInstNo[psb] == -1 && !lvIn[psb].used; }
    bool live(int psb) const { return !available(psb); }
    void release_psb(int psb) {
        psbConsumeInst[psb] = -1;
        psbConsumeInstNo[psb] = -1;
        psbWriteProtection[psb] = 0;
    }
    int inst_order(int ip) { return S(ip).instOrder; }
    int ta(int ip) { return S(ip).ta; }

    void set_required(int ip, int sb, bool ll = false, bool pred = false) {
        if (!is_inst(ip)) {
            hit();
            return;
        }
        SInst &s = S(ip);
        s.reqSB |= (uint8_t)(1u << sb);
        if (ll) s.flags |= GF_REQ_LONG_LATENCY_SB;
        if (pred) s.flags |= GF_REQ_PREDICATED_SB;
    }

    void update_sb_required(int ip, int psb, bool set) {
        if (set) {
            bool ll = false, pr = false;
            if (!psbProducerInsts[psb].empty()) {
                const SInst &d = S(psbProducerInsts[psb].back());
                if (d.wrSB >= 0 && d.wrSB == psb) {
                    if (d.flags & GF_IS_LONG_LATENCY) ll = true;
                    if (d.flags & GF_IS_PREDICATED) pr = true;
                }
            }
            set_required(ip, psb, ll, pr);
        } else {
            SInst &s = S(ip);
            s.reqSB &= (uint8_t)~(1u << psb);
            bool clearLL = true, clearPred = true;
            for (int ii = 0; ii < NUM_SB; ii++) {
                if (!(s.reqSB & (1u << ii)) || psbProducerInsts[ii].empty()) continue;
                const SInst &d = S(psbProducerInsts[ii].back());
                if (d.wrSB >= 0 && d.wrSB == ii) {
                    if (d.flags & GF_IS_LONG_LATENCY) clearLL = false;
                    if (d.flags & GF_IS_PREDICATED) clearPred = false;
                }
            }
            if (clearLL) s.flags &= ~GF_REQ_LONG_LATENCY_SB;
            if (clearPred) s.flags &= ~GF_REQ_PREDICATED_SB;
        }
    }
    void update_sb_required_mask(int ip, int mask) {
        for (int ii = 0; ii < NUM_SB; ii++)
            if (mask & (1 << ii)) update_sb_required(ip, ii, true);
    }

    void set_consume(int psb, int ip, int ipNo) {
        int no;
        if (ip < 0) {
            no = DUMMY_LAST_NO;
        } else {
            no = inst_order(ip);
            update_sb_required(ip, psb, true);
        }
        psbConsumeInst[psb] = ip;
        psbConsumeInstNo[psb] = no;
        (void)ipNo;
    }
    void unset_consume(int psb, int ip, int ipNo) {
        if (available(psb)) hit();
        if (ip >= 0 && ipNo != DUMMY_LAST_NO) update_sb_required(ip, psb, false);
        release_psb(psb);
    }
    void require_psb(int psb, int ip, int ipNo) {
        if (psbConsumeInstNo[psb] == -1) {
            set_consume(psb, ip, ipNo);
        } else {
            int oldNo = psbConsumeInstNo[psb], old = psbConsumeInst[psb];
            if (oldNo > ipNo) {
                unset_consume(psb, old, oldNo);
                set_consume(psb, ip, ipNo);
            }
        }
    }

    int consume_no(int psb) {
        if (!live(psb)) return -1;
        return psbConsumeInstNo[psb];
    }

    int earliest_consumer(const std::vector<int> &vsbs) {
        int no = DUMMY_LAST_NO, ip = -1;
        for (int v : vsbs) {
            int cno = DUMMY_LAST_NO, first = -1;
            if (!usesTable[v].empty()) {
                first = usesTable[v].front();
                cno = inst_order(first);
            }
            if (no > cno) {
                no = cno;
                ip = first;
            }
        }
        return ip;
    }
    int earliest_no(int ip) { return ip >= 0 ? inst_order(ip) : DUMMY_LAST_NO; }

    int tepid(int ip, bool rd) { return ta(ip) + (rd ? read_sb_latency(S(ip)) : write_sb_latency(S(ip))); }
    int inst_time_avail(int ip) { return ip < 0 ? INT_MAX : ta(ip); }
    static int expected_stall(int tep, int t) { return t == INT_MAX ? 0 : std::max(0, tep - t); }

    int stall_delta(int producing, int consuming, int rdwr, int psb) {
        if (!live(psb)) hit();
        int psbTepid = psbExpectedTepid[psb];
        int psbT = inst_time_avail(psbConsumeInst[psb]);
        int psbStall = expected_stall(psbTepid, psbT);
        int vsbTepid = tepid(producing, rdwr == PSB_READ);
        int maxTepid = std::max(vsbTepid, psbTepid);
        int minT = std::min(inst_time_avail(consuming), psbT);
        int newStall = expected_stall(maxTepid, minT);
        if (newStall < psbStall) hit();
        return newStall - psbStall;
    }

    int smallest_delta_for_reassign(int psb, int &newPsb, int firstCand) {
        int smallest = DUMMY_LAST_NO;
        for (int ii = firstCand; ii <= last_sb(); ii++) {
            if (!live(ii) || ii == psb) continue;
            int d = 0;
            for (int prod : psbProducerInsts[psb]) {
                const SInst &ps = S(prod);
                if (ps.wrSB >= 0 && ps.wrSB == psb)
                    d = std::max(d, stall_delta(prod, psbConsumeInst[psb], PSB_WRITE, ii));
                else
                    d = std::max(d, stall_delta(prod, psbConsumeInst[psb], PSB_READ, ii));
            }
            if (smallest > d) {
                smallest = d;
                newPsb = ii;
                if (smallest == 0) break;
            }
        }
        return smallest;
    }

    void reassign_psb(int psb, int newPsb) {
        std::vector<int> prods = psbProducerInsts[psb];
        for (int prod : prods) {
            const SInst &ps = S(prod);
            if (ps.rdSB >= 0 && ps.rdSB == psb) assign_psb_to_vsb(newPsb, lists(prod).rd, prod, PSB_READ);
            if (S(prod).wrSB >= 0 && S(prod).wrSB == psb) assign_psb_to_vsb(newPsb, lists(prod).wr, prod, PSB_WRITE);
        }
        psbProducerInsts[psb].clear();
        if (psbConsumeInst[psb] >= 0) {
            update_sb_required(psbConsumeInst[psb], psb, false);
            psbConsumeInst[psb] = -1;
        }
        psbConsumeInstNo[psb] = -1;
    }

    int smallest_stall_delta_psb(int ip, const std::vector<int> &vsbs, int rdwr, int firstCand) {
        int psb = -1;
        int ec = earliest_consumer(vsbs);
        int smallest = DUMMY_LAST_NO;
        for (int ii = firstCand; ii <= last_sb(); ii++) {
            if (!live(ii)) {
                if (ii == llnd_reserved_sb()) continue;
                hit();
            }
            int d = stall_delta(ip, ec, rdwr, ii);
            if (smallest > d || psb == -1) {
                smallest = d;
                psb = ii;
                if (smallest == 0) break;
            }
        }
        if (smallest > PSB_REASSIGN_STALL_LIMIT && psb >= 0) {
            int newPsb = -1;
            int ns = smallest_delta_for_reassign(psb, newPsb, firstCand);
            if (ns < smallest && newPsb >= 0) reassign_psb(psb, newPsb);
        }
        return psb;
    }

    int same_consume_psb(int ip, const std::vector<int> &vsbs, int rdwr) {
        int ec = earliest_consumer(vsbs);
        int eno = earliest_no(ec);
        for (int ii = first_sb(); ii <= last_sb(); ii++) {
            if (consume_no(ii) != eno) continue;
            if (eno == DUMMY_LAST_NO) {
                if (earliestCarryOut[ii] <= inst_order(ip)) continue;
                if (DoCrossBlock && (rdwr == PSB_WRITE || psbWriteProtection[ii])) continue;
            }
            return ii;
        }
        return -1;
    }

    int available_psb(int start) {
        for (int ii = start; ii <= last_sb(); ii++)
            if (available(ii)) return ii;
        return -1;
    }
    int psb_from_lvin(int start) {
        int r = -1;
        for (int ii = start; ii <= last_sb(); ii++) {
            if (psbConsumeInstNo[ii] == -1 && lvIn[ii].used) {
                r = ii;
                if (lvIn[ii].wrRegs.population() == 0) break;
            }
        }
        return r;
    }
    bool vsb_no_use_inside_bb(const std::vector<int> &vsbs) {
        for (int v : vsbs)
            if (!usesTable[v].empty()) return false;
        return true;
    }

    int heuristic_psb(int ip, const std::vector<int> &vsbs, int rdwr) {
        const SInst &s = S(ip);
        if (DoDepBar && rdwr == PSB_WRITE && (s.flags & GF_USE_HIGH_COST_SB)) {
            return long_latency_sb();
        } else if (LLNonDepbarReservedBB && rdwr == PSB_WRITE && (s.flags & GF_IS_LONG_LAT_MEM_READ)) {
            if (vsb_no_use_inside_bb(vsbs)) {
                int psb = llnd_reserved_sb();
                SbBlock &b = B(ip);
                if (DoCrossBlock && lvIn[psb].used && b.loopHdrIdx == b.index) {
                    set_required(ip, psb);
                    clear_lvin(ip, psb);
                }
                return psb;
            }
        } else if (HMMAReserved && (s.flags & GF_USE_RESERVED_SB)) {
            return hmma_reserved_sb();
        }
        int psb = same_consume_psb(ip, vsbs, rdwr);
        if (psb != -1) return psb;
        int firstPsb = first_sb();
        if (rdwr == PSB_WRITE && (s.flags & GF_IS_LONG_LAT_MEM_READ)) {
            firstPsb = std::max(firstLlsbPsb, first_sb());
            firstPsb = std::min(firstPsb, last_sb());
        }
        psb = available_psb(firstPsb);
        if (LLNonDepbarReserved && psb == llnd_reserved_sb() && vsb_no_use_inside_bb(vsbs)) psb = -1;
        if (psb != -1) return psb;
        if (DoCrossBlock) {
            psb = psb_from_lvin(firstPsb);
            if (psb != -1) {
                if (rdwr == PSB_WRITE && (s.flags & GF_IS_LONG_LAT_MEM_READ)) {
                    set_required(ip, psb);
                    clear_lvin(ip, psb);
                }
                return psb;
            }
        }
        psb = smallest_stall_delta_psb(ip, vsbs, rdwr, firstPsb);
        if (psb < 0) hit();
        return psb;
    }

    void assign_psb_to_vsb(int psb, std::vector<int> vsbs, int ip, int rdwr) {
        if (psb < 0) return;
        SInst &s = S(ip);
        if (rdwr == PSB_READ) s.rdSB = (int8_t)psb;
        else s.wrSB = (int8_t)psb;
        psbProducerInsts[psb].push_back(ip);
        psbExpectedTepid[psb] = std::max(psbExpectedTepid[psb], tepid(ip, rdwr == PSB_READ));
        psbWriteProtection[psb] |= (rdwr == PSB_WRITE);
        if (DoDepBar && rdwr == PSB_WRITE && produces_llsb(ip)) {
            increase_depbar_count(ip);
            if (beforeIp >= 0) llAfter++;
        }
        for (int v : vsbs) {
            if (usesTable[v].empty()) {
                require_psb(psb, -1, DUMMY_LAST_NO);
            } else {
                std::vector<int> uses = usesTable[v];
                for (int u : uses) require_psb(psb, u, inst_order(u));
            }
        }
    }

    int llsb() const { return LAST_SB; }
    bool produces_llsb(int ip) { return is_inst(ip) && S(ip).wrSB >= 0 && S(ip).wrSB == llsb(); }
    bool consumes_llsb(int ip) { return is_inst(ip) && (S(ip).reqSB & (1u << llsb())); }

    void increase_depbar_count(int ip) {
        for (int jj = firstValidDepbarReg; jj <= lastValidDepbarReg; jj++) {
            if (depTab[jj].count > 0) depTab[jj].count++;
            if (depTab[jj].countOther > 0) depTab[jj].countOther++;
        }
        const SInst &s = S(ip);
        for (int k = 0; k < s.nregs; k++) {
            const SReg &r = s.regs[k];
            if (!r.def) break;
            int no = reg_no(r);
            if (no < 0) continue;
            int idx = reg_bias(r.cls, no);
            int oldCount = depTab[idx].count, oldPred = depTab[idx].predKind;
            depTab[idx].predKind = inst_pred_kind(s);
            depTab[idx].count = 1;
            if (oldCount > 0 && oldPred != depTab[idx].predKind) depTab[idx].countOther = oldCount;
        }
    }
    int depbar_cnt(int ip, int no, int cls) {
        int idx = reg_bias(cls, no);
        int c = depTab[idx].count;
        if (c > 0) {
            const SInst &s = S(ip);
            if (s.pred >= 0 && complementary(inst_pred_kind(s), depTab[idx].predKind)) c = depTab[idx].countOther;
        }
        return c - 1;
    }
    void reduce_depbar_cnt(int cnt) {
        if (cnt == 0) {
            for (int jj = firstValidDepbarReg; jj <= lastValidDepbarReg; jj++) depTab[jj] = DepbarItem();
            return;
        }
        for (int jj = firstValidDepbarReg; jj <= lastValidDepbarReg; jj++) {
            if (depTab[jj].count > cnt) depTab[jj].count = 0;
            if (depTab[jj].countOther > cnt) depTab[jj].countOther = 0;
        }
    }
    int smallest_depbar_count(int ip) {
        int r = -1;
        const SInst &s = S(ip);
        for (int k = 0; k < s.nregs; k++) {
            int no = reg_no(s.regs[k]);
            if (no < 0) continue;
            int t = depbar_cnt(ip, no, s.regs[k].cls);
            if (t != -1 && (r == -1 || r > t)) r = t;
        }
        return r;
    }
    void require_if_consume_llsb(int ip) {
        if (!is_inst(ip) || consumes_llsb(ip)) return;
        const SInst &s = S(ip);
        for (int k = 0; k < s.nregs; k++) {
            const SReg &r = s.regs[k];
            int no = reg_no(r);
            if (no >= 0 && depbar_cnt(ip, no, r.cls) >= 0 && !(r.def && (s.flags & GF_USE_HIGH_COST_SB)))
                set_required(ip, llsb(), true);
        }
    }
    void reset_depbar_pred_if_redef(int ip) {
        const SInst &s = S(ip);
        for (int k = 0; k < s.nregs; k++) {
            const SReg &r = s.regs[k];
            if (!r.def) break;
            int no = reg_no(r);
            if (no >= 0 && (r.cls == RC_P || r.cls == RC_UP)) {
                int kt = pred_kind(no, PRED_COND_TRUE, r.cls), kf = pred_kind(no, PRED_COND_FALSE, r.cls);
                for (int jj = firstValidDepbarReg; jj <= lastValidDepbarReg; jj++)
                    if (depTab[jj].predKind == kt || depTab[jj].predKind == kf) depTab[jj].predKind = PRED_ALL;
            }
        }
    }

    void dep_init() {
        leCnt = llAfter = distDepbars = 0;
        beforeIp = consumerIp = -1;
    }
    bool dep_is_set() const { return beforeIp >= 0; }
    bool dep_profitable() const { return distDepbars >= PROFITABLE_DEPBAR_DISTANCE; }
    void dep_set(int cnt, int ip) {
        dep_init();
        leCnt = cnt;
        beforeIp = consumerIp = ip;
    }
    void dep_set_distance(int ip) {
        distDepbars = 0;
        if (beforeIp >= 0) {
            distDepbars = ta(ip) - ta(beforeIp);
            if (distDepbars < 0) hit();
        }
    }
    int better_ip_to_insert_before(int ip) {
        int prevIp = ip;
        while (prevIp >= 0 && !(produces_llsb(prevIp) || consumes_llsb(prevIp))) {
            prevIp = p.nodes[prevIp].prev;
            if (prevIp < 0 || p.nodes[prevIp].kind == SBN_LAB) break;
            if (ta(ip) - ta(prevIp) > PROFITABLE_DEPBAR_DISTANCE) break;
            if (!(S(prevIp).flags & GF_DECOUPLED)) return p.nodes[prevIp].next;
        }
        return ip;
    }
    int new_depbar(int after, int sb, int cnt, int mask) {
        SbNode n;
        n.kind = SBN_INST;
        build_sinst(make_depbar(sb, cnt, mask), shaderType, false, &n.s);
        n.s.number = -1;
        n.s.ta = 0;
        n.s.instOrder = 0;
        n.s.rdSB = n.s.wrSB = -1;
        n.s.reqSB = 0;
        n.depSb = sb;
        n.depCnt = cnt;
        n.depMask = mask;
        return p.insert_after(after, n);
    }
    void insert_depbar_before(int cnt, int ip) {
        ip = better_ip_to_insert_before(ip);
        int prevIp = p.nodes[ip].prev;
        if (prevIp < 0) return;
        if (cnt > MAX_DEPBAR_COUNT) cnt = MAX_DEPBAR_COUNT;
        int d = new_depbar(prevIp, llsb(), cnt, 0);
        S(d).flags |= GF_REQ_LONG_LATENCY_SB;
        p.nodes[d].depConsumer = consumerIp;
    }
    void dep_generate_previous() {
        if (!dep_is_set() || leCnt <= 0) hit();
        insert_depbar_before(leCnt, beforeIp);
        dep_init();
    }
    void dep_require_previous() {
        set_required(beforeIp, llsb(), true);
        dep_init();
    }
    void dep_generate_or_require() {
        if (dep_profitable()) dep_generate_previous();
        else dep_require_previous();
    }
    void dep_merge(int cnt) {
        leCnt = cnt - llAfter;
        if (leCnt == 0) dep_require_previous();
    }
    void insert_profitable_depbar(int cnt, int ip) {
        if (!dep_is_set()) {
            if (cnt == 0) set_required(ip, llsb(), true);
            else dep_set(cnt, ip);
            return;
        }
        if (cnt == 0) {
            if (llAfter == 0 && !dep_profitable()) {
                dep_merge(cnt);
                consumerIp = ip;
            } else {
                dep_generate_previous();
                set_required(ip, llsb(), true);
            }
            return;
        }
        if (cnt < llAfter) {
            dep_generate_previous();
            dep_set(cnt, ip);
            return;
        }
        if (!dep_profitable()) {
            dep_merge(cnt);
            consumerIp = ip;
            return;
        }
        dep_generate_previous();
        dep_set(cnt, ip);
    }
    int generate_depbar_on_llsb_consumer(int ip) {
        dep_set_distance(ip);
        require_if_consume_llsb(ip);
        int used = -1;
        if (consumes_llsb(ip)) {
            SInst &s = S(ip);
            s.reqSB &= (uint8_t)~(1u << llsb());
            s.flags &= ~GF_REQ_LONG_LATENCY_SB;
            used = smallest_depbar_count(ip);
            if (used == -1) used = 0;
            insert_profitable_depbar(used, ip);
            reduce_depbar_cnt(used);
        }
        return used;
    }

    void clear_lvin(int ip, int psb) {
        (void)ip;
        PsbInfo &l = lvIn[psb];
        l.used = false;
        for (int r = l.rdRegs.next(0); r >= 0; r = l.rdRegs.next(r + 1)) lvInRdMask[r] &= ~(1 << psb);
        l.rdRegs.empty();
        for (int r = l.wrRegs.next(0); r >= 0; r = l.wrRegs.next(r + 1)) lvInWrMask[r] &= ~(1 << psb);
        l.wrRegs.empty();
    }
    void clear_all_lvin() {
        std::fill(lvInRdMask.begin(), lvInRdMask.end(), 0);
        std::fill(lvInWrMask.begin(), lvInWrMask.end(), 0);
        for (PsbInfo &l : lvIn) {
            l.used = false;
            l.rdRegs.empty();
            l.wrRegs.empty();
        }
    }
    void merge_lvin_from(const SbBlock &pred, int reg, int psb) {
        const RegPsbInfo &o = lvOut[pred.index][reg];
        if (o.rd & (1 << psb)) {
            lvInRdMask[reg] |= 1 << psb;
            lvIn[psb].used = true;
            lvIn[psb].rdRegs.add(reg);
        }
        if (o.wr & (1 << psb)) {
            lvInWrMask[reg] |= 1 << psb;
            lvIn[psb].used = true;
            lvIn[psb].wrRegs.add(reg);
        }
    }
    bool require_if_consume_lvin_reg(int ip, int psb) {
        if (!is_inst(ip)) return false;
        const SInst &s = S(ip);
        for (int k = 0; k < s.nregs; k++) {
            const SReg &r = s.regs[k];
            int no = reg_no(r);
            if (no < 0) continue;
            int b = reg_bias(r.cls, no);
            if ((r.def && (lvInRdMask[b] & (1 << psb))) || (lvInWrMask[b] & (1 << psb))) {
                set_required(ip, psb);
                clear_lvin(ip, psb);
                return true;
            }
        }
        return false;
    }
    void set_block_idx_last_psb(const SbBlock &b, int ip) {
        const SInst &s = S(ip);
        std::vector<int> &t = blockIdxPerFuncLastPsb[b.func];
        if (s.wrSB >= 0) t[s.wrSB] = std::max(b.index, t[s.wrSB]);
        if (s.rdSB >= 0) t[s.rdSB] = std::max(b.index, t[s.rdSB]);
    }

    bool can_track_cross_block(int bi) {
        SbBlock &cur = p.blocks[bi];
        if (can_track_cross_block_on_callee(cur)) return true;
        if (cur.succ.empty()) return false;
        int back = -1;
        if (p.hasBackEdge) {
            for (int sv : cur.succ)
                if (p.blocks[sv].index <= cur.index) {
                    back = sv;
                    break;
                }
        }
        if (back >= 0) {
            const SbBlock &h = p.blocks[back];
            if (cur.index == cur.loopRegion && h.index == h.loopHdrIdx && h.predCount == 2) {
                if (!loop_single_entry(p, cur.loopHdrIdx, cur.loopRegion)) return false;
            } else {
                return false;
            }
        }
        int last = p.last_node(bi);
        if (is_inst(last)) {
            const SInst &s = S(last);
            if (sb_is_call(s)) return false;
            if ((sb_is_ret(s) || sb_is_retc(s)) && !is_final_exit(s)) return false;
        }
        if (cur.samRam) return false;
        return true;
    }

    void copy_llnd_psb_regs(const SbBlock &b, int psb) {
        if (!llndRdMap.count(b.index)) llndRdMap[b.index] = lvIn[psb].rdRegs;
        if (!llndWrMap.count(b.index)) llndWrMap[b.index] = lvIn[psb].wrRegs;
    }

    bool do_backedge_depbar_on_loop_header(const SbBlock &b) {
        if (!DoDepBar || !DoDepbarAcrossBackedge) return false;
        if (b.index != b.loopHdrIdx) return false;
        if (b.loopHdrIdx == b.loopRegion && b.loopHdrIdx == b.index) return DoDepbarAcrossBackedge >= 1;
        if (b.loopHdrIdx != b.loopRegion) return DoDepbarAcrossBackedge == 2;
        return false;
    }

    void process_depbar_cnt_at_lab(const SbBlock &b) {
        for (DepbarItem &d : depTab) d = DepbarItem();
        const BitSet &lr = liveRegsLlsb[b.index];
        for (int reg = lr.next(0); reg >= 0; reg = lr.next(reg + 1)) {
            int cnt = 0;
            for (int pr : b.pred) {
                int c = lvOut[p.blocks[pr].index][reg].depbarCnt;
                if (cnt == 0) cnt = c;
                else if (c > 0) cnt = std::min(cnt, c);
            }
            if (cnt > 0) {
                if (b.loopHdrIdx == b.index && !do_backedge_depbar_on_loop_header(b)) depTab[reg].count = 1;
                else depTab[reg].count = cnt;
            }
        }
    }
    void process_lvin_at_lab(const SbBlock &b) {
        clear_all_lvin();
        const BitSet &lr = liveRegsPsb[b.index];
        for (int psb = first_sb(); psb <= last_non_ll_sb(); psb++)
            for (int pr : b.pred)
                for (int reg = lr.next(0); reg >= 0; reg = lr.next(reg + 1)) merge_lvin_from(p.blocks[pr], reg, psb);
    }
    void process_lab(const SbBlock &b) {
        if (DoDepBar) process_depbar_cnt_at_lab(b);
        process_lvin_at_lab(b);
        if (!LLNonDepbarReservedKnob && LLNonDepbarReserved)
            LLNonDepbarReservedBB = b.xBlockLLNonDepbar || lvIn[llnd_reserved_sb()].used;
        if (b.index == b.loopHdrIdx) copy_llnd_psb_regs(b, llnd_reserved_sb());
    }

    int live_psb_mask() {
        int m = 0;
        for (int ii = first_sb(); ii <= last_non_ll_sb(); ii++)
            if (!available(ii)) m |= 1 << ii;
        return m;
    }
    int live_llsb_mask() {
        if (!DoDepBar) return 0;
        for (int jj = firstValidDepbarReg; jj <= lastValidDepbarReg; jj++)
            if (depTab[jj].count > 0) return 1 << llsb();
        return 0;
    }
    bool psb_from_ll_non_depbar(int psb) {
        for (int prod : psbProducerInsts[psb]) {
            const SInst &d = S(prod);
            if (d.wrSB >= 0 && d.wrSB == psb && !(d.flags & GF_USE_HIGH_COST_SB) && (d.flags & GF_IS_LONG_LAT_MEM_READ))
                return true;
        }
        return false;
    }
    int finish_psb_mask(int lastIp, int liveMask) {
        int m = 0;
        int t = is_inst(lastIp) ? ta(lastIp) : 0;
        for (int psb = 0; psb <= LAST_SB; psb++)
            if ((liveMask & (1 << psb)) && psbConsumeInstNo[psb] != -1 && psbExpectedTepid[psb] <= t &&
                !psb_from_ll_non_depbar(psb))
                m |= 1 << psb;
        return m;
    }

    bool convergent_write(const SInst &s, const SReg &r) {
        (void)s;
        (void)r;
        return true;
    }
    int must_req_psb_mask(int liveMask) {
        int m = 0;
        for (int psb = 0; psb <= LAST_SB; psb++) {
            if (!(liveMask & (1 << psb))) continue;
            for (int prod : psbProducerInsts[psb]) {
                const SInst &d = S(prod);
                for (int k = 0; k < d.nregs; k++) {
                    const SReg &r = d.regs[k];
                    if (r.cls != RC_UR && r.cls != RC_UP) continue;
                    if (r.attr & SR_GUARD) continue;
                    if (!r.def) continue;
                    if (!convergent_write(d, r)) {
                        m |= 1 << psb;
                        break;
                    }
                }
                if (m & (1 << psb)) break;
            }
        }
        return m;
    }

    void update_lvout_for_reg(const SbBlock &b, int cls, int no, bool rd, int psb) {
        int reg = reg_bias(cls, no);
        if (rd) lvOut[b.index][reg].rd |= 1 << psb;
        else lvOut[b.index][reg].wr |= 1 << psb;
        for (int sv : b.succ) liveRegsPsb[p.blocks[sv].index].add(reg);
        if (can_track_cross_block_on_callee(b)) liveRegsPsb[b.index].add(reg);
    }
    void update_lvout_for_inst(const SbBlock &b, int ip, bool input, int psb) {
        const SInst &s = S(ip);
        if (input) {
            uint8_t ord[SINST_MAX_REGS];
            int n = rev_regs(s, ord);
            for (int k = 0; k < n; k++) {
                const SReg &r = s.regs[ord[k]];
                if (r.def) continue;
                int no = reg_no(r);
                if (no >= 0 && needs_rd_protection(r.cls) && !writeRegSet.has(reg_bias(r.cls, no)))
                    update_lvout_for_reg(b, r.cls, no, true, psb);
            }
        } else {
            for (int k = 0; k < s.nregs; k++) {
                const SReg &r = s.regs[k];
                if (!r.def) break;
                int no = reg_no(r);
                if (no >= 0) update_lvout_for_reg(b, r.cls, no, false, psb);
            }
        }
    }
    void update_lvout_for_bb(SbBlock &b, int finishMask) {
        b.processedLvOutPsb = true;
        if (DoDepBar) {
            for (int jj = firstValidDepbarReg; jj <= lastValidDepbarReg; jj++) {
                if (depTab[jj].count > 0) {
                    if (can_track_cross_block_on_callee(b)) liveRegsLlsb[b.index].add(jj);
                    for (int sv : b.succ) liveRegsLlsb[p.blocks[sv].index].add(jj);
                    lvOut[b.index][jj].depbarCnt = depTab[jj].count;
                }
            }
        }
        for (int psb = first_sb(); psb <= last_non_ll_sb(); psb++) {
            if (finishMask & (1 << psb)) continue;
            if (lvIn[psb].used) {
                for (int r = lvIn[psb].rdRegs.next(0); r >= 0; r = lvIn[psb].rdRegs.next(r + 1)) {
                    lvOut[b.index][r].rd |= 1 << psb;
                    for (int sv : b.succ) liveRegsPsb[p.blocks[sv].index].add(r);
                }
                for (int r = lvIn[psb].wrRegs.next(0); r >= 0; r = lvIn[psb].wrRegs.next(r + 1)) {
                    lvOut[b.index][r].wr |= 1 << psb;
                    for (int sv : b.succ) liveRegsPsb[p.blocks[sv].index].add(r);
                }
            }
            if (psbConsumeInstNo[psb] != -1) {
                for (int prod : psbProducerInsts[psb]) {
                    const SInst &d = S(prod);
                    writeRegSet.clear(MAX_NUM_REG + 1);
                    if (d.wrSB >= 0) {
                        for (int k = 0; k < d.nregs; k++) {
                            const SReg &r = d.regs[k];
                            if (!r.def) break;
                            int no = reg_no(r);
                            if (no >= 0) writeRegSet.add(reg_bias(r.cls, no));
                        }
                        if (d.wrSB == psb) update_lvout_for_inst(b, prod, false, psb);
                    }
                    if (d.rdSB >= 0 && d.rdSB == psb) update_lvout_for_inst(b, prod, true, psb);
                }
            }
        }
    }

    int add_depbar_after(int mask, int after) {
        if (mask == 0) {
            hit();
            return -1;
        }
        int ii = 0, lMask = 0;
        for (; ii < NUM_SB; ii++)
            if (mask & (1 << ii)) {
                lMask = mask & ~(1 << ii);
                break;
            }
        int d = new_depbar(after, ii, 0, lMask);
        if (LLsbDesignated && (mask & (1 << long_latency_sb()))) S(d).flags |= GF_REQ_LONG_LATENCY_SB;
        return d;
    }

    void require_psb_at_last_ip(int lastIp, int mask) {
        if (is_inst(lastIp)) {
            const SInst &s = S(lastIp);
            if (sb_is_ret(s) && is_final_exit(s)) return;
            bool flow = ori_flow(s);
            bool own = (s.rdSB >= 0 && (mask & (1 << s.rdSB))) || (s.wrSB >= 0 && (mask & (1 << s.wrSB)));
            if (flow || !own) {
                update_sb_required_mask(lastIp, mask);
                return;
            }
        }
        add_depbar_after(mask, lastIp);
    }

    static bool ori_flow(const SInst &s);

    void req_at_start(int mask, int bi) {
        SbBlock &b = p.blocks[bi];
        int first = p.nodes[b.lab].next;
        if (first == b.eb) {
            add_depbar_after(mask, b.lab);
            return;
        }
        update_sb_required_mask(first, mask);
    }

    bool need_recheck_psb_in_loop(const SbBlock &h, int psb) {
        if (blockIdxPerFuncLastPsb[h.func][psb] < h.index) return false;
        if (psb == llnd_reserved_sb()) {
            BitSet rd = lvIn[psb].rdRegs, wr = lvIn[psb].wrRegs;
            const BitSet &mr = llndRdMap[h.index], &mw = llndWrMap[h.index];
            for (size_t i = 0; i < rd.b.size(); i++)
                if (rd.b[i] && !mr.has((int)i)) rd.b[i] = 0;
            for (size_t i = 0; i < wr.b.size(); i++)
                if (wr.b[i] && !mw.has((int)i)) wr.b[i] = 0;
            if (rd.equal(lvIn[psb].rdRegs) && wr.equal(lvIn[psb].wrRegs)) return false;
        }
        return true;
    }

    void req_across_backedge(int bi, int liveMask) {
        if (liveMask == 0) return;
        SbBlock &b = p.blocks[bi];
        if (b.succ.empty()) {
            hit();
            return;
        }
        int hb = b.succ[0];
        if (p.blocks[hb].index != b.loopHdrIdx) {
            if (b.succ.size() < 2) {
                hit();
                return;
            }
            hb = b.succ[1];
        }
        SbBlock &h = p.blocks[hb];
        process_lab(h);
        bool Removed[NUM_SB];
        for (int ii = 0; ii < NUM_SB; ii++) Removed[ii] = !need_recheck_psb_in_loop(h, ii);
        bool backedgeDepbar = do_backedge_depbar_on_loop_header(h);
        int ipNext;
        for (int ip = p.nodes[h.lab].next; ip >= 0 && ip != h.eb; ip = ipNext) {
            ipNext = p.nodes[ip].next;
            bool RemovedDepbar = false;
            SInst &s = S(ip);
            int rdSb = s.rdSB, wrSb = s.wrSB;
            for (int ii = 0; ii < NUM_SB; ii++) {
                if (!(liveMask & (1 << ii)) || Removed[ii]) continue;
                if (is_depbar(s)) {
                    const SbNode &n = p.nodes[ip];
                    if (n.depCnt > 0 && n.depSb == ii && backedgeDepbar) {
                        p.unlink(ip);
                        RemovedDepbar = true;
                        break;
                    } else if (n.depSb == ii || (n.depMask & (1 << ii))) {
                        if (n.depCnt != 0) hit();
                        Removed[ii] = true;
                        continue;
                    }
                }
                if (DoDepBar && ii == llsb()) {
                    if (!backedgeDepbar) {
                        require_if_consume_llsb(ip);
                        if (consumes_llsb(ip)) {
                            reduce_depbar_cnt(0);
                            Removed[ii] = true;
                            continue;
                        }
                    } else {
                        int c = generate_depbar_on_llsb_consumer(ip);
                        if (produces_llsb(ip) && (s.flags & GF_USE_HIGH_COST_SB)) {
                            increase_depbar_count(ip);
                            if (beforeIp >= 0) llAfter++;
                        } else if (c == 0) {
                            Removed[ii] = true;
                        }
                        continue;
                    }
                }
                if (s.reqSB & (1 << ii)) {
                    Removed[ii] = true;
                    continue;
                }
                if ((rdSb >= 0 && rdSb == ii) || (wrSb >= 0 && wrSb == ii)) {
                    update_sb_required(ip, ii, true);
                    Removed[ii] = true;
                    continue;
                }
                if (require_if_consume_lvin_reg(ip, ii)) {
                    Removed[ii] = true;
                    continue;
                }
            }
            if (DoDepBar && !RemovedDepbar) reset_depbar_pred_if_redef(ip);
        }
        int remaining = 0;
        for (int ii = 0; ii < NUM_SB; ii++)
            if ((liveMask & (1 << ii)) && !Removed[ii]) remaining |= 1 << ii;
        if (backedgeDepbar) {
            bool avoid = true;
            for (int jj = firstValidDepbarReg; jj <= lastValidDepbarReg; jj++) {
                int nc = depTab[jj].count, oc = lvOut[h.index][jj].depbarCnt;
                if (nc > 0 && nc != oc) {
                    if (h.loopHdrIdx == h.loopRegion && h.loopHdrIdx == h.index) {
                        lvOut[h.index][jj].depbarCnt = nc;
                    } else {
                        lvOut[h.index][jj].depbarCnt = 1;
                        avoid = false;
                    }
                }
            }
            if (avoid) remaining &= ~(1 << llsb());
        }
        if (remaining) require_psb_at_last_ip(p.nodes[h.eb].prev, remaining);
    }

    void process_live_psbs_at_end(int bi) {
        SbBlock &b = p.blocks[bi];
        int lastIp = p.nodes[b.eb].prev;
        int liveNonLL = live_psb_mask();
        int liveLL = live_llsb_mask();
        int liveMask = liveNonLL | liveLL;
        if (liveMask == 0) {
            b.processedLvOutPsb = true;
            return;
        }
        int req = 0;
        int mustReq = must_req_psb_mask(liveMask);
        int finish = mustReq;
        if (DoReqCommit) finish |= finish_psb_mask(lastIp, liveNonLL);
        if (can_track_cross_block(bi)) {
            update_lvout_for_bb(b, finish);
            if (b.index == b.loopRegion) {
                if (DoDepBar && dep_is_set()) dep_generate_previous();
                req_across_backedge(bi, liveMask & ~finish);
                req = finish;
            } else {
                req = finish;
            }
        } else {
            require_psb_at_last_ip(lastIp, liveMask);
            return;
        }
        lastIp = p.nodes[b.eb].prev;
        if (lastIp == b.lab || req == 0) return;
        bool NonExitRet = false;
        if (is_inst(lastIp)) {
            const SInst &s = S(lastIp);
            NonExitRet = (sb_is_ret(s) || sb_is_retc(s)) && !is_final_exit(s);
        }
        bool SuccLoopHeader = false;
        for (int sv : b.succ)
            if (p.blocks[sv].loopHdrIdx == p.blocks[sv].index) {
                SuccLoopHeader = true;
                break;
            }
        if (mustReq) {
            require_psb_at_last_ip(lastIp, mustReq);
            req &= ~mustReq;
        }
        if (req == 0) return;
        if (DoCrossBlock && !SuccLoopHeader && !NonExitRet) {
            for (int sv : b.succ) req_at_start(req, sv);
        } else {
            require_psb_at_last_ip(lastIp, req);
        }
    }

    void propagate_lvout_of_ret_at_call(int bi) {
        SbBlock &b = p.blocks[bi];
        if (b.callee < 0 || b.callee >= (int)p.funcs.size()) return;
        const SbFunc &f = p.funcs[b.callee];
        if (f.abi) return;
        for (int rb = f.first; rb <= f.last; rb++) {
            SbBlock &r = p.blocks[rb];
            if (!can_track_cross_block_on_callee(r)) continue;
            if (!r.processedLvOutPsb) hit();
            if (DoDepBar) {
                const BitSet &lr = liveRegsLlsb[r.index];
                for (int reg = lr.next(0); reg >= 0; reg = lr.next(reg + 1)) {
                    int bc = lvOut[b.index][reg].depbarCnt, rc = lvOut[r.index][reg].depbarCnt;
                    bc = (bc == 0 || rc == 0) ? std::max(bc, rc) : std::min(bc, rc);
                    lvOut[b.index][reg].depbarCnt = bc;
                    for (int sv : b.succ) liveRegsLlsb[p.blocks[sv].index].add(reg);
                }
            }
            const BitSet &lp = liveRegsPsb[r.index];
            for (int reg = lp.next(0); reg >= 0; reg = lp.next(reg + 1)) {
                int sr = lvOut[r.index][reg].rd, sw = lvOut[r.index][reg].wr;
                std::vector<int> &t = blockIdxPerFuncLastPsb[b.func];
                if (sr) {
                    lvOut[b.index][reg].rd |= sr;
                    for (int ii = 0; ii < NUM_SB; ii++)
                        if (sr & (1 << ii)) t[ii] = std::max(b.index, t[ii]);
                }
                if (sw) {
                    lvOut[b.index][reg].wr |= sw;
                    for (int ii = 0; ii < NUM_SB; ii++)
                        if (sw & (1 << ii)) t[ii] = std::max(b.index, t[ii]);
                }
                for (int sv : b.succ) liveRegsPsb[p.blocks[sv].index].add(reg);
            }
        }
    }

    void release_required_psb(int ip) {
        const SInst &s = S(ip);
        for (int ii = first_sb(); ii <= LAST_SB; ii++) {
            if (s.reqSB & (1 << ii)) {
                release_psb(ii);
                psbProducerInsts[ii].clear();
                clear_lvin(ip, ii);
            }
        }
    }

    void assign_physical(int bi) {
        SbBlock &b = p.blocks[bi];
        curBlock = bi;
        for (int ii = 0; ii < NUM_SB; ii++) {
            psbConsumeInst[ii] = -1;
            psbConsumeInstNo[ii] = -1;
            psbExpectedTepid[ii] = 0;
            psbWriteProtection[ii] = 0;
            psbProducerInsts[ii].clear();
            earliestCarryOut[ii] = INT_MAX;
        }
        b.processedLvOutPsb = false;
        process_lab(b);
        for (int ip = p.first_inst(bi); ip != b.eb; ip = p.nodes[ip].next) {
            release_required_psb(ip);
            if (DoDepBar) generate_depbar_on_llsb_consumer(ip);
            for (int ii = first_sb(); ii <= last_non_ll_sb(); ii++) {
                if (require_if_consume_lvin_reg(ip, ii)) {
                    if (psbConsumeInstNo[ii] != -1) unset_consume(ii, psbConsumeInst[ii], psbConsumeInstNo[ii]);
                    psbProducerInsts[ii].clear();
                }
            }
            std::vector<int> rd = lists(ip).rd, wr = lists(ip).wr;
            if (!rd.empty()) {
                int psb = heuristic_psb(ip, rd, PSB_READ);
                assign_psb_to_vsb(psb, rd, ip, PSB_READ);
            }
            if (!wr.empty()) {
                int psb = heuristic_psb(ip, wr, PSB_WRITE);
                assign_psb_to_vsb(psb, wr, ip, PSB_WRITE);
            }
            set_block_idx_last_psb(b, ip);
            if (DoDepBar) reset_depbar_pred_if_redef(ip);
        }
        process_live_psbs_at_end(bi);
        if (DoCrossBlockOnCallee && is_inst(p.last_node(bi)) && sb_is_call(S(p.last_node(bi))))
            propagate_lvout_of_ret_at_call(bi);
        if (DoDepBar && dep_is_set()) dep_generate_previous();
    }

    int max_vsbs(int ip) {
        const SInst &s = S(ip);
        int wr = 0, rd = 0;
        if (s.flags & GF_NEEDS_WRITE_SB)
            for (int k = 0; k < s.nregs && s.regs[k].def; k++) wr++;
        if (s.flags & GF_NEEDS_READ_SB)
            for (int k = s.nregs - 1; k >= 0 && !s.regs[k].def; k--) rd++;
        return wr * 1000 + rd;
    }

    void run() {

        for (SbNode &n : p.nodes) {
            if (n.kind != SBN_INST) continue;
            n.s.rdSB = n.s.wrSB = -1;
            n.s.reqSB = 0;
            n.s.flags &= ~(GF_PROHIBIT_REUSE | GF_REQ_LONG_LATENCY_SB | GF_REQ_PREDICATED_SB);
        }

        for (int bi = 0; bi < (int)p.blocks.size(); bi++) {
            SbBlock &b = p.blocks[bi];
            int order = 1, vsbs = 0;
            for (int ip = p.first_inst(bi); ip != b.eb; ip = p.nodes[ip].next) {
                SInst &s = S(ip);
                s.instOrder = order++;
                int m = max_vsbs(ip);
                int wr = m / 1000, rd = m % 1000;
                vsbs += wr + rd;
                if ((s.flags & GF_USE_HIGH_COST_SB) && wr > 0) HasLLDepbarInst = true;
                if (!(s.flags & GF_USE_HIGH_COST_SB) && (s.flags & GF_IS_LONG_LAT_MEM_READ) && wr > 0)
                    HasLLNonDepbarInst = true;
                if (s.flags & GF_USE_RESERVED_SB) HasReservedSBInst = true;
                if (s.flags & GF_USE_RESERVED_SB2) HasReservedSB2Inst = true;
            }
            b.vsbCount = vsbs + 1;
        }

        DoDepBar = HasLLDepbarInst;
        LLsbDesignated = DoDepBar;
        HMMAReserved = HasReservedSBInst;
        LDGDEPBARReserved = HasReservedSB2Inst;
        LLNonDepbarReserved = HasLLNonDepbarInst && DoCrossBlock;
        LLNonDepbarReservedBB = LDGDEPBARReserved;
        int off = (LLsbDesignated && HMMAReserved && LDGDEPBARReserved) ? 5 : 4;
        firstLlsbPsb = NUM_SB - off;
        depTab.assign(MAX_NUM_REG + 1, DepbarItem());
        firstValidDepbarReg = 0;
        lastValidDepbarReg = MAX_NUM_REG;
        dep_init();
        int nb = (int)p.blocks.size();
        lvOut.assign(nb + 1, std::vector<RegPsbInfo>(MAX_NUM_REG + 1));
        lvInRdMask.assign(MAX_NUM_REG + 1, 0);
        lvInWrMask.assign(MAX_NUM_REG + 1, 0);
        liveRegsLlsb.assign(nb + 1, BitSet());
        liveRegsPsb.assign(nb + 1, BitSet());
        for (int i = 0; i <= nb; i++) {
            liveRegsLlsb[i].clear(MAX_NUM_REG + 1);
            liveRegsPsb[i].clear(MAX_NUM_REG + 1);
        }
        blockIdxPerFuncLastPsb.assign(p.funcs.size(), std::vector<int>(NUM_SB, 0));
        for (int fi : func_order()) {
            const SbFunc &f = p.funcs[fi];
            for (int bi = f.first; bi <= f.last; bi++) {
                assign_vsb(bi);
                assign_physical(bi);
            }
        }
    }

    std::vector<int> func_order() {
        int nf = (int)p.funcs.size();
        std::vector<std::vector<int>> called(nf);
        for (int fi = 0; fi < nf; fi++)
            for (int bi = p.funcs[fi].first; bi <= p.funcs[fi].last; bi++)
                for (int k = p.first_inst(bi); k != p.blocks[bi].eb; k = p.nodes[k].next) {
                    if (!sb_is_call(S(k))) continue;
                    int c = p.blocks[bi].callee;
                    if (c >= 0 && c < nf && !contains(called[fi], c)) called[fi].insert(called[fi].begin(), c);
                }
        std::vector<int> order, state(nf, 0);
        std::vector<std::pair<int, size_t>> stack;
        auto visit = [&](int root) {
            stack.push_back({root, 0});
            state[root] = -1;
            while (!stack.empty()) {
                int f = stack.back().first;
                size_t &k = stack.back().second;
                if (k < called[f].size()) {
                    int c = called[f][k++];
                    if (state[c] == 0) {
                        state[c] = -1;
                        stack.push_back({c, 0});
                    }
                    continue;
                }
                order.push_back(f);
                state[f] = 1;
                stack.pop_back();
            }
        };
        if (nf > 0) visit(0);
        for (int fi = 0; fi < nf; fi++)
            if (state[fi] == 0) visit(fi);
        return order;
    }
};

bool Pass::ori_flow(const SInst &s) { return ori_kind(s).flow; }

}

Word make_depbar(int sb, int cnt, int mask) {
    Word w = {0x0000d0400000791aull, 0x000fc80000000000ull};
    Inst in;
    if (!decode(w, &in)) return w;
    auto put = [&](const char *name, int64_t v) {
        int k = val_index(in.cls, name);
        if (k >= 0) set(in, k, v);
    };
    put("sbidx", sb);
    put("cnt", cnt);
    put("scoreboard_list", mask);
    return in.w;
}

void assign_scoreboards(SbProg &p, int shader_type, SbStats *stats) {
    Pass ps(p, stats, shader_type);
    ps.run();
}

}
}
}
