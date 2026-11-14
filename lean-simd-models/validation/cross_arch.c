// Cross-architecture check of the trusted bindings in c/simd_shim.h plus full
// 128-bit carry-less multiply quadrant selectors (`0x00, 0x01, 0x10, 0x11` and
// ignored immediate bits `0xFE, 0xEF, 0xFF`).
// Evaluates all operations on a fixed sequence of edge and random inputs and
// writes the raw results to stdout. Build it for two architectures and
// compare the outputs byte for byte:
//   clang -O2 -arch arm64 ... ; clang -O2 -arch x86_64 -msse4.2 -mpclmul ...
// The AArch64 results are separately checked against the Lean models by
// tests/HwDiff.lean, so equal outputs put the x86-64 bindings on the same
// footing. Usage: cross_arch [random-pairs]
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "../c/simd_shim.h"

#if defined(__aarch64__)
#include <arm_neon.h>
static inline void clmul_quad(uint64_t a0, uint64_t a1, uint64_t b0, uint64_t b1,
                              int imm, uint64_t *lo, uint64_t *hi) {
  uint64_t sa = (imm & 0x01) ? a1 : a0;
  uint64_t sb = (imm & 0x10) ? b1 : b0;
  __uint128_t r;
  if ((imm & 0x11) == 0x11) {
    poly64x2_t va = {a0, a1}, vb = {b0, b1};
    r = (__uint128_t)vmull_high_p64(va, vb);
  } else {
    r = (__uint128_t)vmull_p64((poly64_t)sa, (poly64_t)sb);
  }
  *lo = (uint64_t)r;
  *hi = (uint64_t)(r >> 64);
}
#elif defined(__x86_64__)
#if defined(__SSE4_2__) && defined(__PCLMUL__)
#define XARCH_TARGET
#else
#define XARCH_TARGET __attribute__((__target__("sse4.2,pclmul")))
#endif
#define DEF_CLMUL_IMM(NAME, IMM)                                                 \
  static inline XARCH_TARGET void NAME(uint64_t a0, uint64_t a1, uint64_t b0,    \
                                       uint64_t b1, uint64_t *lo, uint64_t *hi) {\
    simdmodels_v2di va = {(long long)a0, (long long)a1};                         \
    simdmodels_v2di vb = {(long long)b0, (long long)b1};                         \
    simdmodels_v2di r = __builtin_ia32_pclmulqdq128(va, vb, (IMM));              \
    *lo = (uint64_t)r[0];                                                        \
    *hi = (uint64_t)r[1];                                                        \
  }
DEF_CLMUL_IMM(clmul_00, 0x00)
DEF_CLMUL_IMM(clmul_01, 0x01)
DEF_CLMUL_IMM(clmul_10, 0x10)
DEF_CLMUL_IMM(clmul_11, 0x11)
DEF_CLMUL_IMM(clmul_fe, 0xFE) /* ignored bits set: behaves as 0x10 */
DEF_CLMUL_IMM(clmul_ef, 0xEF) /* ignored bits set: behaves as 0x01 */
DEF_CLMUL_IMM(clmul_ff, 0xFF) /* ignored bits set: behaves as 0x11 */
#endif

static uint64_t nxt(uint64_t x) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; return x; }

static void emit(uint64_t x, uint64_t y) {
  uint32_t c = (uint32_t)x;
  uint64_t x1 = nxt(x ^ 0xA5A5A5A5A5A5A5A5ull);
  uint64_t y1 = nxt(y ^ 0x5A5A5A5A5A5A5A5Aull);
  uint64_t out[20];
  out[0] = SIMDMODELS_CRC32C_U8(c, (uint8_t)y);
  out[1] = SIMDMODELS_CRC32C_U16(c, (uint16_t)y);
  out[2] = SIMDMODELS_CRC32C_U32(c, (uint32_t)y);
  out[3] = SIMDMODELS_CRC32C_U64(c, y);
  out[4] = SIMDMODELS_CLMUL_LO(x, y);
  out[5] = SIMDMODELS_CLMUL_HI(x, y);
#if defined(__aarch64__)
  clmul_quad(x, x1, y, y1, 0x00, &out[6], &out[7]);
  clmul_quad(x, x1, y, y1, 0x01, &out[8], &out[9]);
  clmul_quad(x, x1, y, y1, 0x10, &out[10], &out[11]);
  clmul_quad(x, x1, y, y1, 0x11, &out[12], &out[13]);
  clmul_quad(x, x1, y, y1, 0xFE, &out[14], &out[15]);
  clmul_quad(x, x1, y, y1, 0xEF, &out[16], &out[17]);
  clmul_quad(x, x1, y, y1, 0xFF, &out[18], &out[19]);
#elif defined(__x86_64__)
  clmul_00(x, x1, y, y1, &out[6], &out[7]);
  clmul_01(x, x1, y, y1, &out[8], &out[9]);
  clmul_10(x, x1, y, y1, &out[10], &out[11]);
  clmul_11(x, x1, y, y1, &out[12], &out[13]);
  clmul_fe(x, x1, y, y1, &out[14], &out[15]);
  clmul_ef(x, x1, y, y1, &out[16], &out[17]);
  clmul_ff(x, x1, y, y1, &out[18], &out[19]);
#endif
  fwrite(out, sizeof out, 1, stdout);
}

int main(int argc, char **argv) {
  long n = argc > 1 ? atol(argv[1]) : 1000000;
  uint64_t e[256]; int ne = 0;
  uint64_t fixed[] = {0, ~0ull, 0xAAAAAAAAAAAAAAAAull, 0x5555555555555555ull, 0x00000000FFFFFFFFull,
                      0xFFFFFFFF00000000ull, 0x0123456789ABCDEFull, 0x8000000000000001ull};
  for (int i = 0; i < 8; i++) e[ne++] = fixed[i];
  for (int i = 0; i < 64; i++) { e[ne++] = 1ull << i; e[ne++] = ~(1ull << i); e[ne++] = (1ull << i) - 1; }
  for (int i = 0; i < ne; i++) for (int j = 0; j < ne; j++) emit(e[i], e[j]);
  uint64_t s = 0x9E3779B97F4A7C15ull ^ 1;
  for (long k = 0; k < n; k++) { s = nxt(s); uint64_t x = s; s = nxt(s); emit(x, s); }
  return 0;
}
