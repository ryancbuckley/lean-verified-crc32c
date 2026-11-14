// Cross-architecture check of the trusted bindings in c/simd_shim.h.
// Evaluates all six macros on a fixed sequence of edge and random inputs and
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

static uint64_t nxt(uint64_t x) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; return x; }

static void emit(uint64_t x, uint64_t y) {
  uint32_t c = (uint32_t)x;
  uint64_t out[6];
  out[0] = SIMDMODELS_CRC32C_U8(c, (uint8_t)y);
  out[1] = SIMDMODELS_CRC32C_U16(c, (uint16_t)y);
  out[2] = SIMDMODELS_CRC32C_U32(c, (uint32_t)y);
  out[3] = SIMDMODELS_CRC32C_U64(c, y);
  out[4] = SIMDMODELS_CLMUL_LO(x, y);
  out[5] = SIMDMODELS_CLMUL_HI(x, y);
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
