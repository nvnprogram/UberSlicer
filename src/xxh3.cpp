// xxh3.cpp - XXH3_64bits, the hash this project names shader programs by.
// Derived from xxHash <https://github.com/Cyan4973/xxHash>:
//
//   xxHash - Extremely Fast Hash algorithm
//   Copyright (C) 2012-2021 Yann Collet
//   SPDX-License-Identifier: BSD-2-Clause
//
//   Redistribution and use in source and binary forms, with or without
//   modification, are permitted provided that the following conditions are
//   met:
//
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//
//   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
//   "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
//   LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
//   A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
//   OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
//   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
//   LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
//   DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
//   THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
//   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
//   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#include "uber.h"

namespace ub {

static inline u32 rd32(const u8 *p) {
    return (u32)p[0] | ((u32)p[1] << 8) | ((u32)p[2] << 16) | ((u32)p[3] << 24);
}
static inline u64 rd64(const u8 *p) {
    return (u64)rd32(p) | ((u64)rd32(p + 4) << 32);
}
static inline u64 swap64(u64 x) {
    return ((x & 0x00000000000000FFull) << 56) |
           ((x & 0x000000000000FF00ull) << 40) |
           ((x & 0x0000000000FF0000ull) << 24) |
           ((x & 0x00000000FF000000ull) <<  8) |
           ((x & 0x000000FF00000000ull) >>  8) |
           ((x & 0x0000FF0000000000ull) >> 24) |
           ((x & 0x00FF000000000000ull) >> 40) |
           ((x & 0xFF00000000000000ull) >> 56);
}
static inline u64 rotl64(u64 x, int r) {
    return (x << r) | (x >> (64 - r));
}
static inline u64 mul32to64(u64 a, u64 b) {
    return (u64)(u32)a * (u64)(u32)b;
}

static inline u64 mul128_fold64(u64 a, u64 b) {
    u64 lo_lo = mul32to64(a, b);
    u64 hi_lo = mul32to64(a >> 32, b);
    u64 lo_hi = mul32to64(a, b >> 32);
    u64 hi_hi = mul32to64(a >> 32, b >> 32);
    u64 cross = (lo_lo >> 32) + (hi_lo & 0xFFFFFFFFull) + lo_hi;
    u64 upper = (hi_lo >> 32) + (cross >> 32) + hi_hi;
    u64 lower = (cross << 32) | (lo_lo & 0xFFFFFFFFull);
    return lower ^ upper;
}

static const u32 P32_1 = 0x9E3779B1u;
static const u32 P32_2 = 0x85EBCA77u;
static const u32 P32_3 = 0xC2B2AE3Du;
static const u64 P64_1 = 0x9E3779B185EBCA87ull;
static const u64 P64_2 = 0xC2B2AE3D27D4EB4Full;
static const u64 P64_3 = 0x165667B19E3779F9ull;
static const u64 P64_4 = 0x85EBCA77C2B2AE63ull;
static const u64 P64_5 = 0x27D4EB2F165667C5ull;

static const u8 kSecret[192] = {
0xb8,0xfe,0x6c,0x39,0x23,0xa4,0x4b,0xbe,0x7c,0x01,0x81,0x2c,0xf7,0x21,0xad,0x1c,
0xde,0xd4,0x6d,0xe9,0x83,0x90,0x97,0xdb,0x72,0x40,0xa4,0xa4,0xb7,0xb3,0x67,0x1f,
0xcb,0x79,0xe6,0x4e,0xcc,0xc0,0xe5,0x78,0x82,0x5a,0xd0,0x7d,0xcc,0xff,0x72,0x21,
0xb8,0x08,0x46,0x74,0xf7,0x43,0x24,0x8e,0xe0,0x35,0x90,0xe6,0x81,0x3a,0x26,0x4c,
0x3c,0x28,0x52,0xbb,0x91,0xc3,0x00,0xcb,0x88,0xd0,0x65,0x8b,0x1b,0x53,0x2e,0xa3,
0x71,0x64,0x48,0x97,0xa2,0x0d,0xf9,0x4e,0x38,0x19,0xef,0x46,0xa9,0xde,0xac,0xd8,
0xa8,0xfa,0x76,0x3f,0xe3,0x9c,0x34,0x3f,0xf9,0xdc,0xbb,0xc7,0xc7,0x0b,0x4f,0x1d,
0x8a,0x51,0xe0,0x4b,0xcd,0xb4,0x59,0x31,0xc8,0x9f,0x7e,0xc9,0xd9,0x78,0x73,0x64,
0xea,0xc5,0xac,0x83,0x34,0xd3,0xeb,0xc3,0xc5,0x81,0xa0,0xff,0xfa,0x13,0x63,0xeb,
0x17,0x0d,0xdd,0x51,0xb7,0xf0,0xda,0x49,0xd3,0x16,0x55,0x26,0x29,0xd4,0x68,0x9e,
0x2b,0x16,0xbe,0x58,0x7d,0x47,0xa1,0xfc,0x8f,0xf8,0xb8,0xd1,0x7a,0xd0,0x31,0xce,
0x45,0xcb,0x3a,0x8f,0x95,0x16,0x04,0x28,0xaf,0xd7,0xfb,0xca,0xbb,0x4b,0x40,0x7e,
};

static const size_t SECRET_LEN   = sizeof kSecret;
static const size_t STRIPE_LEN   = 64;
static const size_t ACC_NB       = 8;
static const size_t CONSUME_RATE = 8;
static const size_t LASTACC_OFF  = 7;
static const size_t MERGEACC_OFF = 11;
static const size_t MIDSIZE_MAX  = 240;
static const size_t MIDSIZE_START = 3;
static const size_t MIDSIZE_LAST  = 17;
static const size_t SECRET_SIZE_MIN = 136;

static inline u64 xxh64_avalanche(u64 h) {
    h ^= h >> 33; h *= P64_2;
    h ^= h >> 29; h *= P64_3;
    h ^= h >> 32;
    return h;
}
static inline u64 xxh3_avalanche(u64 h) {
    h ^= h >> 37; h *= 0x165667919E3779F9ull; h ^= h >> 32;
    return h;
}
static inline u64 rrmxmx(u64 h, u64 len) {
    h ^= rotl64(h, 49) ^ rotl64(h, 24);
    h *= 0x9FB21C651E98DF25ull;
    h ^= (h >> 35) + len;
    h *= 0x9FB21C651E98DF25ull;
    return h ^ (h >> 28);
}

static u64 len_1to3(const u8 *in, size_t len) {
    u32 c = ((u32)in[0] << 16) | ((u32)in[len >> 1] << 24) |
            ((u32)in[len - 1]) | ((u32)len << 8);
    return xxh64_avalanche((u64)c ^ (u64)(rd32(kSecret) ^ rd32(kSecret + 4)));
}
static u64 len_4to8(const u8 *in, size_t len) {
    u64 in1 = rd32(in), in2 = rd32(in + len - 4);
    u64 bitflip = rd64(kSecret + 8) ^ rd64(kSecret + 16);
    return rrmxmx((in2 + (in1 << 32)) ^ bitflip, (u64)len);
}
static u64 len_9to16(const u8 *in, size_t len) {
    u64 lo = rd64(in)           ^ (rd64(kSecret + 24) ^ rd64(kSecret + 32));
    u64 hi = rd64(in + len - 8) ^ (rd64(kSecret + 40) ^ rd64(kSecret + 48));
    return xxh3_avalanche((u64)len + swap64(lo) + hi + mul128_fold64(lo, hi));
}
static u64 len_0to16(const u8 *in, size_t len) {
    if (len > 8) return len_9to16(in, len);
    if (len >= 4) return len_4to8(in, len);
    if (len) return len_1to3(in, len);
    return xxh64_avalanche(rd64(kSecret + 56) ^ rd64(kSecret + 64));
}

static inline u64 mix16(const u8 *in, const u8 *sec) {
    return mul128_fold64(rd64(in) ^ rd64(sec), rd64(in + 8) ^ rd64(sec + 8));
}

static u64 len_17to128(const u8 *in, size_t len) {
    u64 acc = (u64)len * P64_1;
    if (len > 32) {
        if (len > 64) {
            if (len > 96) {
                acc += mix16(in + 48, kSecret + 96);
                acc += mix16(in + len - 64, kSecret + 112);
            }
            acc += mix16(in + 32, kSecret + 64);
            acc += mix16(in + len - 48, kSecret + 80);
        }
        acc += mix16(in + 16, kSecret + 32);
        acc += mix16(in + len - 32, kSecret + 48);
    }
    acc += mix16(in, kSecret);
    acc += mix16(in + len - 16, kSecret + 16);
    return xxh3_avalanche(acc);
}

static u64 len_129to240(const u8 *in, size_t len) {
    u64 acc = (u64)len * P64_1;
    size_t rounds = len / 16, i;
    for (i = 0; i < 8; i++) acc += mix16(in + 16 * i, kSecret + 16 * i);
    acc = xxh3_avalanche(acc);
    for (; i < rounds; i++)
        acc += mix16(in + 16 * i, kSecret + 16 * (i - 8) + MIDSIZE_START);
    acc += mix16(in + len - 16, kSecret + SECRET_SIZE_MIN - MIDSIZE_LAST);
    return xxh3_avalanche(acc);
}

static void accumulate_512(u64 *acc, const u8 *in, const u8 *sec) {
    for (size_t i = 0; i < ACC_NB; i++) {
        u64 v = rd64(in + 8 * i);
        u64 k = v ^ rd64(sec + 8 * i);
        acc[i ^ 1] += v;
        acc[i] += mul32to64(k, k >> 32);
    }
}
static void scramble(u64 *acc, const u8 *sec) {
    for (size_t i = 0; i < ACC_NB; i++) {
        u64 a = acc[i];
        a ^= a >> 47;
        a ^= rd64(sec + 8 * i);
        a *= P32_1;
        acc[i] = a;
    }
}
static u64 mix2accs(const u64 *acc, const u8 *sec) {
    return mul128_fold64(acc[0] ^ rd64(sec), acc[1] ^ rd64(sec + 8));
}
static u64 merge_accs(const u64 *acc, const u8 *sec, u64 start) {
    u64 r = start;
    for (size_t i = 0; i < 4; i++) r += mix2accs(acc + 2 * i, sec + 16 * i);
    return xxh3_avalanche(r);
}

static u64 hash_long(const u8 *in, size_t len) {
    u64 acc[ACC_NB] = { P32_3, P64_1, P64_2, P64_3, P64_4, P32_2, P64_5, P32_1 };
    size_t stripes_per_block = (SECRET_LEN - STRIPE_LEN) / CONSUME_RATE;
    size_t block_len = STRIPE_LEN * stripes_per_block;
    size_t nblocks = (len - 1) / block_len;
    for (size_t n = 0; n < nblocks; n++) {
        const u8 *b = in + n * block_len;
        for (size_t s = 0; s < stripes_per_block; s++)
            accumulate_512(acc, b + s * STRIPE_LEN, kSecret + s * CONSUME_RATE);
        scramble(acc, kSecret + SECRET_LEN - STRIPE_LEN);
    }
    size_t nstripes = ((len - 1) - block_len * nblocks) / STRIPE_LEN;
    const u8 *tail = in + nblocks * block_len;
    for (size_t s = 0; s < nstripes; s++)
        accumulate_512(acc, tail + s * STRIPE_LEN, kSecret + s * CONSUME_RATE);
    accumulate_512(acc, in + len - STRIPE_LEN,
                   kSecret + SECRET_LEN - STRIPE_LEN - LASTACC_OFF);
    return merge_accs(acc, kSecret + MERGEACC_OFF, (u64)len * P64_1);
}

u64 xxh3_64(const void *data, size_t len) {
    const u8 *in = (const u8 *)data;
    if (len <= 16) return len_0to16(in, len);
    if (len <= 128) return len_17to128(in, len);
    if (len <= MIDSIZE_MAX) return len_129to240(in, len);
    return hash_long(in, len);
}

}
