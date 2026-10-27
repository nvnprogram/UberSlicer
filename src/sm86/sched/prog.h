
#ifndef UB_SM86_SCHED_PROG_H
#define UB_SM86_SCHED_PROG_H

#include <cstdint>

#include "../sm86.h"
#include "classify.h"

namespace ub {
namespace sm86 {
namespace sched {

enum RegClass {
    RC_INVALID = 0, RC_CB = 1, RC_UP = 2, RC_UR = 3, RC_CC = 4, RC_P = 5, RC_R = 6,
    RC_ACTIVEM = 7, RC_OUT = 8, RC_STATE = 9, RC_PSEUDO = 10
};

enum {
    SR_GUARD = 1,
    SR_BINDLESS = 2,
    SR_BASE = 4
};

struct SReg {
    uint8_t cls;
    uint8_t def;
    uint8_t opd;
    uint8_t first_def;
    int16_t no;
    uint8_t attr;
};

static const int SINST_MAX_REGS = 40;

enum { PRED_COND_TRUE = 0, PRED_COND_FALSE = 1 };

struct SInst {
    Word w;
    Inst in;
    SchedClass sc;
    bool ok;

    int nregs;
    SReg regs[SINST_MAX_REGS];

    int8_t pred;
    uint8_t pred_cls;
    uint8_t pred_cond;

    int number;

    int instOrder;
    int ta;
    int depStage;
    int8_t rdSB, wrSB;
    uint8_t reqSB;
    uint32_t flags;

    int waitTa;
    int depbarCommit;
    int maxCcOrP;
    int cumuWait;
    int waitLatency;
    uint8_t endGroup;
    int8_t resToUse;

    uint8_t drain;
    uint8_t uschedInfo;
    uint8_t batchT;
    uint8_t opRdSB, opWrSB;
    uint8_t reuse;
};

void build_sinst(const Word &w, int shader_type, bool half_track, SInst *s);

void nop_stand_in(SInst *s, bool lastInBlock, int shader_type);

bool bar_blocks(int cls);

}
}
}

#endif
