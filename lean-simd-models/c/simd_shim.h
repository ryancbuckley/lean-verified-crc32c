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

#include <stddef.h>
#include <stdint.h>

/* Unaligned byte load (LDRB Wt / MOVZX r32, m8). */
static inline __attribute__((__always_inline__)) uint8_t
simdmodels_load_u8_ptr(const uint8_t *p, size_t i) {
  return p[i];
}

/* Unaligned little-endian 64-bit load (LDR Xt / MOV r64, m64, or half of LDR Qt / MOVDQU).
 * Exposes a single i64 load in LLVM IR so CGSCC inlining and SLPVectorizer can
 * form 128-bit vector loads across adjacent 64-bit halves (unlike 8 separate
 * byte loads through a [0 x i8] flexible array member). */
static inline __attribute__((__always_inline__)) uint64_t
simdmodels_load_u64_le_ptr(const uint8_t *p, size_t i) {
  uint64_t v;
  __builtin_memcpy(&v, p + i, sizeof(v));
#if defined(__BYTE_ORDER__) && defined(__ORDER_BIG_ENDIAN__) && \
    (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__)
  v = __builtin_bswap64(v);
#endif
  return v;
}

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

/* CPU-feature detection for the hardware paths: nonzero only if this CPU has
 * both the CRC32C and the 64x64 carry-less-multiply instructions bound above.
 * Setting the environment variable SIMDMODELS_DISABLE_HW (to anything) forces
 * zero, so the fallback path can be tested on any machine. */
extern char *getenv(const char *);
#if defined(__aarch64__) && defined(__linux__)
extern unsigned long getauxval(unsigned long);
#endif
static inline uint8_t simdmodels_cpu_has_crc_clmul(void) {
  if (getenv("SIMDMODELS_DISABLE_HW") != 0) return 0;
#if defined(__aarch64__) && defined(__APPLE__)
  return 1; /* every Apple arm64 CPU has FEAT_CRC32 and FEAT_PMULL */
#elif defined(__aarch64__) && defined(__linux__)
  unsigned long caps = getauxval(16 /* AT_HWCAP */);
  return (caps & (1ul << 7) /* HWCAP_CRC32 */) && (caps & (1ul << 4) /* HWCAP_PMULL */);
#elif defined(__x86_64__)
  return __builtin_cpu_supports("sse4.2") && __builtin_cpu_supports("pclmul");
#else
  return 0;
#endif
}
#define SIMDMODELS_CPU_HAS_CRC_CLMUL() simdmodels_cpu_has_crc_clmul()

#define SIMDMODELS_CRC32C_U8(c, v)  simdmodels_crc32c_u8((c), (v))
#define SIMDMODELS_CRC32C_U16(c, v) simdmodels_crc32c_u16((c), (v))
#define SIMDMODELS_CRC32C_U32(c, v) simdmodels_crc32c_u32((c), (v))
#define SIMDMODELS_CRC32C_U64(c, v) simdmodels_crc32c_u64((c), (v))
#define SIMDMODELS_CLMUL_LO(a, b)   simdmodels_clmul_lo((a), (b))
#define SIMDMODELS_CLMUL_HI(a, b)   simdmodels_clmul_hi((a), (b))
/* Raw byte pointer into a ByteArray's payload without forming or dereferencing
 * a `lean_sarray_object *` (which asserts on `m_header` / `m_size` when !NDEBUG
 * and requires 8-byte alignment in C/UBSan when `cxx/leanmemcpy.cc` passes a
 * headerless borrowed pointer `p - offsetof(lean_sarray_object, m_data)` for an
 * arbitrarily aligned caller pointer `p`). Unsigned `uintptr_t` arithmetic
 * recovers `p` exactly without pointer-overflow or alignment UB. */
#define SIMDMODELS_SARRAY_BYTES(a) \
  ((const uint8_t *)((uintptr_t)(a) + offsetof(lean_sarray_object, m_data)))

#define SIMDMODELS_LOAD_U8(a, i) \
  simdmodels_load_u8_ptr(SIMDMODELS_SARRAY_BYTES(a), (size_t)(i))
#define SIMDMODELS_LOAD_U64_LE(a, i) \
  simdmodels_load_u64_le_ptr(SIMDMODELS_SARRAY_BYTES(a), (size_t)(i))

#endif
