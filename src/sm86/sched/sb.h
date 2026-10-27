
#ifndef UB_SM86_SCHED_SB_H
#define UB_SM86_SCHED_SB_H

#include <cstdint>
#include <vector>

#include "deps.h"
#include "prog.h"

namespace ub {
namespace sm86 {
namespace sched {

enum SbNodeKind { SBN_LAB, SBN_INST, SBN_EB };

struct SbNode {
    uint8_t kind = SBN_INST;
    int prev = -1, next = -1;
    int block = -1;
    SInst s;

    int depSb = 0, depCnt = 0, depMask = 0;
    int depConsumer = -1;
    int relBlock = -1;
};

struct SbBlock {
    int lab = -1, eb = -1;
    int func = 0;
    int index = 0;

    std::vector<int> succ, pred;
    int predCount = 0;
    int loopHdrIdx = 0, loopRegion = 0, loopNestLvl = 0, offset = 0;

    int target = -1;
    std::vector<int> jmxTargets;
    int callee = -1;
    bool samRam = false;

    int vsbCount = 0;
    bool xBlockLLNonDepbar = false;
    bool processedLvOutPsb = false;

    bool maxHazard = false;
};

struct SbFunc {
    int first = 0, last = -1;
    bool main = false;
    bool abi = false;
};

struct SbProg {
    std::vector<SbNode> nodes;
    std::vector<SbBlock> blocks;
    std::vector<SbFunc> funcs;
    bool hasLoops = false, hasIrregularLoops = false, hasCalls = false, hasBackEdge = false;

    int add_block(int func);
    int append_inst(int block, const SInst &s);

    int insert_after(int at, const SbNode &n);
    void unlink(int node);

    int insert_block_after(int b);
    int first_inst(int block) const { return nodes[blocks[block].lab].next; }
    int last_node(int block) const { return nodes[blocks[block].eb].prev; }
};

bool sb_is_jmp(const SInst &s);
bool sb_is_cond_flow(const SInst &s);
bool sb_is_jmx(const SInst &s);
bool sb_is_call(const SInst &s);
bool sb_is_ret(const SInst &s);
bool sb_is_retc(const SInst &s);
bool sb_ret_is_exit(const SInst &s);

void analyze_cfg(SbProg &p);

bool loop_single_entry(const SbProg &p, int bixHead, int bixTail);

struct SbStats {
    long long assertHits = 0;

    bool regroupLowered = false;

    bool beyondFromLowered = false;
};

void assign_scoreboards(SbProg &p, int shader_type, SbStats *stats);

void opex_replay(SbProg &p, DepsCtx ctx, SbStats *stats);

void optimize_wait_opex(SbProg &p, int shader_type, SbStats *stats);

void legalize_wait_opex(SbProg &p, int shader_type, SbStats *stats);

int warpsync_after_break_regions(SbProg &p, int shader_type);

void add_padding(SbProg &p, int shader_type);

void set_opex(SbProg &p, int shader_type);

void assign_reuse(SbProg &p);

void relocate(SbProg &p);

int write_control(SbProg &p);

void invert_branch(SInst &s, int shader_type);

Word make_nop();
Word make_bra();

std::vector<char> sb_varying_ldc(const SbProg &p);

void sb_ldc_latency(SbProg &p);

std::vector<char> sb_may_diverge(const SbProg &p);

Word make_depbar(int sb, int cnt, int mask);

}
}
}

#endif
