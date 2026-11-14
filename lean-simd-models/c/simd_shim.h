/*
 * lean-simd-models: the C side of the trusted instruction bindings.
 *
 * Each macro below is one line that calls exactly one CPU instruction through
 * a compiler builtin. The Lean declarations in SimdModels/Trusted.lean name
 * these macros in `@[extern c inline]` patterns; the Lean body of each
 * declaration is the model that the proofs use.
 *
 * Trusted: that the compiler lowers each builtin to the named instruction,
 * and that the instruction behaves as its Lean model says. Both are tested
 * (see tests/ and validation/), not proven.
 *
 * This header must be force-included (`-include`) when compiling any
 * Lean-generated C that uses the bindings.
 */
#ifndef SIMDMODELS_SHIM_H
#define SIMDMODELS_SHIM_H

#if defined(__aarch64__)
/* A64 CRC32CB / CRC32CH / CRC32CW / CRC32CX (needs +crc) */
#define SIMDMODELS_CRC32C_U8(c, v)  __builtin_arm_crc32cb((c), (v))
#define SIMDMODELS_CRC32C_U16(c, v) __builtin_arm_crc32ch((c), (v))
#define SIMDMODELS_CRC32C_U32(c, v) __builtin_arm_crc32cw((c), (v))
#define SIMDMODELS_CRC32C_U64(c, v) __builtin_arm_crc32cd((c), (v))
/* A64 PMULL (64x64 -> 128 carry-less multiply; needs +aes), low and high halves */
#define SIMDMODELS_CLMUL_LO(a, b) ((unsigned long long)(__uint128_t)__builtin_neon_vmull_p64((a), (b)))
#define SIMDMODELS_CLMUL_HI(a, b) ((unsigned long long)((__uint128_t)__builtin_neon_vmull_p64((a), (b)) >> 64))

#elif defined(__x86_64__) && defined(__SSE4_2__) && defined(__PCLMUL__)
/* SSE4.2 CRC32 r32, r/m8|16|32 and CRC32 r64, r/m64 */
#define SIMDMODELS_CRC32C_U8(c, v)  __builtin_ia32_crc32qi((c), (v))
#define SIMDMODELS_CRC32C_U16(c, v) __builtin_ia32_crc32hi((c), (v))
#define SIMDMODELS_CRC32C_U32(c, v) __builtin_ia32_crc32si((c), (v))
#define SIMDMODELS_CRC32C_U64(c, v) ((unsigned int)__builtin_ia32_crc32di((c), (v)))
/* PCLMULQDQ xmm, xmm, 0x00 on the low quadwords; low and high halves of the result */
typedef long long simdmodels_v2di __attribute__((__vector_size__(16), __aligned__(16)));
#define SIMDMODELS_CLMUL_LO(a, b) ((unsigned long long)(__builtin_ia32_pclmulqdq128((simdmodels_v2di){(long long)(a), 0}, (simdmodels_v2di){(long long)(b), 0}, 0))[0])
#define SIMDMODELS_CLMUL_HI(a, b) ((unsigned long long)(__builtin_ia32_pclmulqdq128((simdmodels_v2di){(long long)(a), 0}, (simdmodels_v2di){(long long)(b), 0}, 0))[1])

#else
/* No binding on this target: the hardware paths must never be dispatched to. */
#define SIMDMODELS_CRC32C_U8(c, v)  (__builtin_trap(), (unsigned int)0)
#define SIMDMODELS_CRC32C_U16(c, v) (__builtin_trap(), (unsigned int)0)
#define SIMDMODELS_CRC32C_U32(c, v) (__builtin_trap(), (unsigned int)0)
#define SIMDMODELS_CRC32C_U64(c, v) (__builtin_trap(), (unsigned int)0)
#define SIMDMODELS_CLMUL_LO(a, b) (__builtin_trap(), (unsigned long long)0)
#define SIMDMODELS_CLMUL_HI(a, b) (__builtin_trap(), (unsigned long long)0)
#endif

#endif
