#pragma once
#include <stddef.h>

#include <cstdint>

#define NVN2_CONTROL_MAJOR 201
#define NVN2_CONTROL_MINOR 20

struct NVN2shaderControl {
    uint32_t magic;

    uint32_t mMajorVer;
    uint32_t mMinorVer;

    uint16_t arch;
    uint8_t padding1[0x30 - 0xe];

    uint32_t mControlSize;
    uint8_t padding2[0x4];

    uint32_t mProgramSize;

    uint32_t mConstBufSize;
    uint32_t mConstBufOffset;

    uint32_t mShaderSize;
    uint8_t padding3[0x4];

    uint32_t mProgramRegNum;
    uint8_t padding4[0x7c - 0x50];

    uint32_t debugBuildId[4];
    uint8_t padding5[0x98 - 0x8c];

    uint32_t mControlSize2;
    uint8_t padding6[0xbc - 0x9c];

    uint32_t mEmbeddedOffset;
    uint32_t mEmbeddedSize;
    uint8_t padding7[0x4];

    uint32_t mExtensionOffset;
    uint32_t mExtensionSize;
    uint8_t padding8[0x4];

    uint32_t mDataEnd;

    uint32_t mJumpTableOffset;
    uint32_t mJumpTableSize;
};

static_assert(sizeof(NVN2shaderControl) == 0xe0,
              "NVN2shaderControl must match the 0xe0-byte control header");

#define NVN2_CTL_AT(f, off) \
    static_assert(offsetof(NVN2shaderControl, f) == (off), \
                  "NVN2shaderControl::" #f " moved")
NVN2_CTL_AT(magic, 0x00);
NVN2_CTL_AT(mMajorVer, 0x04);
NVN2_CTL_AT(mMinorVer, 0x08);
NVN2_CTL_AT(arch, 0x0c);
NVN2_CTL_AT(mControlSize, 0x30);
NVN2_CTL_AT(mProgramSize, 0x38);
NVN2_CTL_AT(mConstBufSize, 0x3c);
NVN2_CTL_AT(mConstBufOffset, 0x40);
NVN2_CTL_AT(mShaderSize, 0x44);
NVN2_CTL_AT(mProgramRegNum, 0x4c);
NVN2_CTL_AT(debugBuildId, 0x7c);
NVN2_CTL_AT(mControlSize2, 0x98);
NVN2_CTL_AT(mEmbeddedOffset, 0xbc);
NVN2_CTL_AT(mEmbeddedSize, 0xc0);
NVN2_CTL_AT(mExtensionOffset, 0xc8);
NVN2_CTL_AT(mExtensionSize, 0xcc);
NVN2_CTL_AT(mDataEnd, 0xd4);
NVN2_CTL_AT(mJumpTableOffset, 0xd8);
NVN2_CTL_AT(mJumpTableSize, 0xdc);
#undef NVN2_CTL_AT
