
#ifndef UBERSPEC_NV_SCHED_CTL_H
#define UBERSPEC_NV_SCHED_CTL_H

#define SCHED_CTL_BITS  21
#define SCHED_CTL_MASK  0x1FFFFFu
#define SCHED_WAIT_MASK 0x1Fu

static const int SCHED_WAIT_DEC[32] = {
    15, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 15, 6, 8, 15
};


static inline int sched_wait_code(unsigned long long hdr, int s)
{
    return (int)((hdr >> (SCHED_CTL_BITS * s)) & SCHED_WAIT_MASK);
}

#endif
