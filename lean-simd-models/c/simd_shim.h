/*
 * lean-simd-models: the C side of the trusted instruction bindings.
 *
 * Each typed inline function below lowers to one CPU instruction through a
 * compiler builtin, wrapped by a macro named in `SimdModels/Trusted.lean` via
 * `@[extern c inline]`; the Lean body of each declaration is the model that the
 * proofs use.
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

#include <stdint.h>

#if defined(__aarch64__)

#if defined(__ARM_FEATURE_CRC32) && defined(__ARM_FEATURE_AES)
#define SIMDMODELS_TARGET __attribute__((__always_inline__))
#else
#define SIMDMODELS_TARGET __attribute__((__target__("crc,aes")))
#endif

/* A64 CRC32CB / CRC32CH / CRC32CW / CRC32CX */
static inline SIMDMODELS_TARGET uint32_t simdmodels_crc32c_u8(uint32_t c, uint8_t v) {
  return __builtin_arm_crc32cb(c, v);
}
static inline SIMDMODELS_TARGET uint32_t simdmodels_crc32c_u16(uint32_t c, uint16_t v) {
  return __builtin_arm_crc32ch(c, v);
}
static inline SIMDMODELS_TARGET uint32_t simdmodels_crc32c_u32(uint32_t c, uint32_t v) {
  return __builtin_arm_crc32cw(c, v);
}
static inline SIMDMODELS_TARGET uint32_t simdmodels_crc32c_u64(uint32_t c, uint64_t v) {
  return __builtin_arm_crc32cd(c, v);
}

/* A64 PMULL (64x64 -> 128 carry-less multiply), low and high 64-bit halves */
static inline SIMDMODELS_TARGET uint64_t simdmodels_clmul_lo(uint64_t a, uint64_t b) {
  return (uint64_t)(__uint128_t)__builtin_neon_vmull_p64(a, b);
}
static inline SIMDMODELS_TARGET uint64_t simdmodels_clmul_hi(uint64_t a, uint64_t b) {
  return (uint64_t)(((__uint128_t)__builtin_neon_vmull_p64(a, b)) >> 64);
}

#elif defined(__x86_64__)

#if defined(__SSE4_2__) && defined(__PCLMUL__)
#define SIMDMODELS_TARGET __attribute__((__always_inline__))
#else
#define SIMDMODELS_TARGET __attribute__((__target__("sse4.2,pclmul")))
#endif

typedef long long simdmodels_v2di __attribute__((__vector_size__(16), __aligned__(16)));

/* SSE4.2 CRC32 r32, r/m8|16|32 and CRC32 r64, r/m64 */
static inline SIMDMODELS_TARGET uint32_t simdmodels_crc32c_u8(uint32_t c, uint8_t v) {
  return __builtin_ia32_crc32qi(c, v);
}
static inline SIMDMODELS_TARGET uint32_t simdmodels_crc32c_u16(uint32_t c, uint16_t v) {
  return __builtin_ia32_crc32hi(c, v);
}
static inline SIMDMODELS_TARGET uint32_t simdmodels_crc32c_u32(uint32_t c, uint32_t v) {
  return __builtin_ia32_crc32si(c, v);
}
static inline SIMDMODELS_TARGET uint32_t simdmodels_crc32c_u64(uint32_t c, uint64_t v) {
  return (uint32_t)__builtin_ia32_crc32di(c, v);
}

/* PCLMULQDQ xmm, xmm, 0x00 on the low quadwords; low and high 64-bit halves */
static inline SIMDMODELS_TARGET uint64_t simdmodels_clmul_lo(uint64_t a, uint64_t b) {
  simdmodels_v2di va = {(long long)a, 0};
  simdmodels_v2di vb = {(long long)b, 0};
  return (uint64_t)__builtin_ia32_pclmulqdq128(va, vb, 0)[0];
}
static inline SIMDMODELS_TARGET uint64_t simdmodels_clmul_hi(uint64_t a, uint64_t b) {
  simdmodels_v2di va = {(long long)a, 0};
  simdmodels_v2di vb = {(long long)b, 0};
  return (uint64_t)__builtin_ia32_pclmulqdq128(va, vb, 0)[1];
}

#else

/* No binding on this target: the hardware paths must never be dispatched to. */
static inline uint32_t simdmodels_crc32c_u8(uint32_t c, uint8_t v) {
  (void)c; (void)v; __builtin_trap(); return 0;
}
static inline uint32_t simdmodels_crc32c_u16(uint32_t c, uint16_t v) {
  (void)c; (void)v; __builtin_trap(); return 0;
}
static inline uint32_t simdmodels_crc32c_u32(uint32_t c, uint32_t v) {
  (void)c; (void)v; __builtin_trap(); return 0;
}
static inline uint32_t simdmodels_crc32c_u64(uint32_t c, uint64_t v) {
  (void)c; (void)v; __builtin_trap(); return 0;
}
static inline uint64_t simdmodels_clmul_lo(uint64_t a, uint64_t b) {
  (void)a; (void)b; __builtin_trap(); return 0;
}
static inline uint64_t simdmodels_clmul_hi(uint64_t a, uint64_t b) {
  (void)a; (void)b; __builtin_trap(); return 0;
}

#endif

#define SIMDMODELS_CRC32C_U8(c, v)  simdmodels_crc32c_u8((c), (v))
#define SIMDMODELS_CRC32C_U16(c, v) simdmodels_crc32c_u16((c), (v))
#define SIMDMODELS_CRC32C_U32(c, v) simdmodels_crc32c_u32((c), (v))
#define SIMDMODELS_CRC32C_U64(c, v) simdmodels_crc32c_u64((c), (v))
#define SIMDMODELS_CLMUL_LO(a, b)   simdmodels_clmul_lo((a), (b))
#define SIMDMODELS_CLMUL_HI(a, b)   simdmodels_clmul_hi((a), (b))

#endif
