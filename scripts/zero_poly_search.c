// Offline search for sparse multiples ("zero polynomials", Chorba) of the
// CRC32C generator G = 0x11EDC6F41. Untrusted: every polynomial kept is
// re-proven to be a multiple of G inside Lean.
//
// Finds Z = x^a + x^b + ... + 1 with G | Z, of weight 3 and 4, up to a
// degree bound. Usage: zero_poly_search <max_degree_bits> [weight4_max]
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define POLY 0x1EDC6F41u  // natural bit order, without x^32

static uint32_t mulx(uint32_t r) { return (r << 1) ^ ((r >> 31) ? POLY : 0); }

// open-addressing hash from residue -> exponent
static uint32_t *keys, *vals; static size_t cap;
static void put(uint32_t k, uint32_t v) {
  size_t i = (k * 2654435761u) & (cap - 1);
  while (vals[i] != UINT32_MAX) { if (keys[i] == k) return; i = (i + 1) & (cap - 1); }
  keys[i] = k; vals[i] = v;
}
static uint32_t get(uint32_t k) {
  size_t i = (k * 2654435761u) & (cap - 1);
  while (vals[i] != UINT32_MAX) { if (keys[i] == k) return vals[i]; i = (i + 1) & (cap - 1); }
  return UINT32_MAX;
}

int main(int argc, char **argv) {
  uint32_t n = argc > 1 ? (uint32_t)strtoul(argv[1], 0, 10) : 1u << 20;
  uint32_t n4 = argc > 2 ? (uint32_t)strtoul(argv[2], 0, 10) : 4096;
  uint32_t *r = malloc(sizeof(uint32_t) * (n + 1));
  cap = 1; while (cap < 4ull * n) cap <<= 1;
  keys = malloc(cap * 4); vals = malloc(cap * 4); memset(vals, 0xff, cap * 4);
  r[0] = 1; for (uint32_t i = 1; i <= n; i++) r[i] = mulx(r[i - 1]);
  for (uint32_t i = 0; i <= n; i++) put(r[i], i);
  // order of x (only reported if within bound)
  for (uint32_t i = 1; i <= n; i++) if (r[i] == 1) { printf("order_of_x %u\n", i); break; }
  // weight 3: x^a + x^b + 1, a > b > 0
  int found = 0;
  for (uint32_t a = 2; a <= n && found < 40; a++) {
    uint32_t b = get(r[a] ^ 1u);
    if (b != UINT32_MAX && b < a && b > 0) { printf("w3 %u %u 0\n", a, b); found++; }
  }
  // weight 4: x^a + x^b + x^c + 1, a > b > c > 0, a <= n4
  found = 0;
  for (uint32_t a = 3; a <= n4 && found < 200; a++)
    for (uint32_t b = 2; b < a; b++) {
      uint32_t c = get(r[a] ^ r[b] ^ 1u);
      if (c != UINT32_MAX && c < b && c > 0) { printf("w4 %u %u %u 0\n", a, b, c); found++; }
    }
  return 0;
}
