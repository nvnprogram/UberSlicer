#pragma once
#include "nv_attributes.h"
#include "nv_shader_header.h"
#include <stddef.h>

#include <cstdint>

#define NVN_NUM_TEX_UNITS   32

#define NVN_CONTROL_MAGIC 0x98761234u
#define NVN_PROGRAM_MAGIC 0x12345678u

enum NVNshaderStage {
    NVN_SHADER_STAGE_VERTEX = 0,
    NVN_SHADER_STAGE_FRAGMENT = 1,
    NVN_SHADER_STAGE_GEOMETRY = 2,
    NVN_SHADER_STAGE_TESS_CONTROL = 3,
    NVN_SHADER_STAGE_TESS_EVALUATION = 4,
    NVN_SHADER_STAGE_COMPUTE = 5
};

struct NVNshaderControl {
    uint32_t magic;

    uint32_t mMajorVer;
    uint32_t mMinorVer;

    uint32_t arch;
    uint32_t impl;

    uint32_t mGlasmOffset;
    uint32_t mGlasmSize;
    uint32_t mGlasmUnk0;
    uint32_t mGlasmUnk1;
    uint8_t padding1[0x6f0 - 0x24];

    uint32_t unk2;
    uint32_t unk3;

    uint32_t mProgramSize;

    uint32_t mConstBufSize;
    uint32_t mConstBufOffset;

    uint32_t mShaderSize;

    uint32_t mProgramOffset;
    uint32_t mProgramRegNum;
    uint32_t mPerWarpScratchSize;

    NVNshaderStage mShaderStage;

    uint8_t early_fragment_tests;
    uint8_t post_depth_coverage;

    uint8_t padding2[0x2];

    uint8_t writesDepth;

    uint8_t padding3[0x15];

    uint32_t numColourResults;

    uint8_t padding4[0x10];

    union {
        struct {
            uint8_t paddingFragUnk[2];
            uint8_t per_sample_invocation;
        } frag;
        struct
        {
            uint32_t block_dims[3];
            uint32_t shared_mem_sz;
            uint32_t local_pos_mem_sz;
            uint32_t local_neg_mem_sz;
            uint32_t crs_sz;
            uint32_t num_barriers;
        } comp;
    };

    uint8_t  pad1[0x91];
    uint8_t  numSamplerRefs;
    uint8_t  pad2[0xa];
    uint8_t  samplerUnitBindings[NVN_NUM_TEX_UNITS];
    uint8_t  pad3[0x54];
    uint8_t  endPadding[0x8];
};

static_assert(sizeof(NVNshaderControl) == 2176,
              "NVNshaderControl must match the 2176-byte control blob");

#define NVN_CTL_AT(f, off) \
    static_assert(offsetof(NVNshaderControl, f) == (off), \
                  "NVNshaderControl::" #f " moved")
NVN_CTL_AT(magic, 0x000);
NVN_CTL_AT(mGlasmOffset, 0x014);
NVN_CTL_AT(unk2, 0x6f0);
NVN_CTL_AT(mProgramSize, 0x6f8);
NVN_CTL_AT(mConstBufSize, 0x6fc);
NVN_CTL_AT(mConstBufOffset, 0x700);
NVN_CTL_AT(mShaderSize, 0x704);
NVN_CTL_AT(mProgramOffset, 0x708);
NVN_CTL_AT(mProgramRegNum, 0x70c);
NVN_CTL_AT(mPerWarpScratchSize, 0x710);
NVN_CTL_AT(mShaderStage, 0x714);
NVN_CTL_AT(early_fragment_tests, 0x718);
NVN_CTL_AT(post_depth_coverage, 0x719);
NVN_CTL_AT(writesDepth, 0x71c);
NVN_CTL_AT(numColourResults, 0x734);
NVN_CTL_AT(frag.per_sample_invocation, 0x74a);
NVN_CTL_AT(numSamplerRefs, 0x7f9);
NVN_CTL_AT(samplerUnitBindings, 0x804);
#undef NVN_CTL_AT

struct GPUProgramHeader {
    uint32_t magic;
    uint8_t padding[0x30 - 0x4];
    NvShaderHeader nvsh;

};
static_assert(sizeof(GPUProgramHeader) == 0x30 + 0x50,
              "GPUProgramHeader must be the 0x30 prefix plus the 0x50 SPH");
