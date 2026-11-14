// Weight-6 sparse multiples of the CRC32C generator: x^a+x^b+x^c+x^d+x^e+1,
// a>b>c>d>e>0, a <= N. Meet in the middle: hash all pairs (d,e), probe with
// triples (a,b,c). Untrusted; results are re-proven in Lean.
// Usage: zero_poly_w6 <N> [max_results]
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define POLY 0x1EDC6F41u
static uint32_t mulx(uint32_t r) { return (r << 1) ^ ((r >> 31) ? POLY : 0); }
typedef struct { uint32_t k; uint16_t d, e; uint8_t used; } ent;
int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 300;
  int maxr = argc > 2 ? atoi(argv[2]) : 50;
  uint32_t *r = malloc(4 * (n + 1));
  r[0] = 1; for (int i = 1; i <= n; i++) r[i] = mulx(r[i - 1]);
  size_t cap = 1; while (cap < (size_t)n * n * 2) cap <<= 1;
  ent *t = calloc(cap, sizeof(ent));
  for (int d = 2; d <= n; d++) for (int e = 1; e < d; e++) {
    uint32_t k = r[d] ^ r[e]; size_t i = (k * 2654435761u) & (cap - 1);
    while (t[i].used) i = (i + 1) & (cap - 1);
    t[i].k = k; t[i].d = d; t[i].e = e; t[i].used = 1;
  }
  int found = 0;
  for (int a = 5; a <= n && found < maxr; a++)
    for (int b = 4; b < a; b++) for (int c = 3; c < b; c++) {
      uint32_t k = r[a] ^ r[b] ^ r[c] ^ 1u; size_t i = (k * 2654435761u) & (cap - 1);
      for (; t[i].used; i = (i + 1) & (cap - 1))
        if (t[i].k == k && t[i].d < c) { printf("w6 %d %d %d %d %d 0\n", a, b, c, t[i].d, t[i].e); found++; }
    }
  return 0;
}
