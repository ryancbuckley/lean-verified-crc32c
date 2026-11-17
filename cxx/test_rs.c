/* End-to-end test of the Reed–Solomon C library through its public API
 * (cxx/leanrs.h): encoding against an independent log/antilog-table Lagrange
 * evaluator, random erasure and reconstruction, both paths, short shards, and
 * rejection of invalid arguments. Usage: test_rs [bench] */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "leanrs.h"

static uint8_t EXP[512], LOG[256];
static void init_gf(void) {
  unsigned x = 1;
  for (int i = 0; i < 255; i++) {
    EXP[i] = (uint8_t)x; LOG[x] = (uint8_t)i;
    x <<= 1; if (x & 0x100) x ^= 0x11D;
  }
  for (int i = 255; i < 512; i++) EXP[i] = EXP[i - 255];
}
static uint8_t mul(uint8_t a, uint8_t b) { return (a && b) ? EXP[LOG[a] + LOG[b]] : 0; }
static uint8_t dvd(uint8_t a, uint8_t b) { return a ? EXP[LOG[a] + 255 - LOG[b]] : 0; }

/* Independent reference: value at y of the polynomial through (xs[i], v[i]). */
static uint8_t lagrange_eval(const uint8_t* xs, const uint8_t* v, size_t k, uint8_t y) {
  uint8_t acc = 0;
  for (size_t s = 0; s < k; s++) {
    uint8_t num = 1, den = 1;
    for (size_t t = 0; t < k; t++)
      if (t != s) { num = mul(num, y ^ xs[t]); den = mul(den, xs[s] ^ xs[t]); }
    acc ^= mul(v[s], dvd(num, den));
  }
  return acc;
}

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

typedef int (*RunFn)(const uint8_t*, size_t, size_t, size_t, const uint8_t* const*, uint8_t* const*);

static int check(size_t k, size_t m, size_t len, RunFn run, const char* name) {
  size_t n = k + m;
  uint8_t** sh = malloc(n * sizeof *sh);
  for (size_t p = 0; p < n; p++) sh[p] = malloc(len);
  for (size_t p = 0; p < k; p++) for (size_t t = 0; t < len; t++) sh[p][t] = (uint8_t)next();
  uint8_t xs[256], ys[256];
  for (size_t p = 0; p < n; p++) (p < k ? xs : ys)[p < k ? p : p - k] = (uint8_t)p;
  uint8_t* tab = malloc(leanrs_table_size(k, m));
  if (leanrs_prepare(xs, k, ys, m, tab) || run(tab, k, m, len, (const uint8_t* const*)sh, sh + k)) {
    printf("FAIL %s: encode rejected k=%zu m=%zu len=%zu\n", name, k, m, len); return 1;
  }
  /* parity against the independent evaluator */
  uint8_t col[256];
  for (size_t t = 0; t < len; t++) {
    for (size_t p = 0; p < k; p++) col[p] = sh[p][t];
    for (size_t j = 0; j < m; j++)
      if (sh[k + j][t] != lagrange_eval(xs, col, k, (uint8_t)(k + j))) {
        printf("FAIL %s: parity k=%zu m=%zu len=%zu row=%zu byte=%zu\n", name, k, m, len, j, t);
        return 1;
      }
  }
  /* erase m random shards, rebuild them from the k survivors */
  for (int rep = 0; rep < 3; rep++) {
    uint8_t perm[256];
    for (size_t p = 0; p < n; p++) perm[p] = (uint8_t)p;
    for (size_t p = 0; p < n; p++) { size_t q = p + next() % (n - p); uint8_t x = perm[p]; perm[p] = perm[q]; perm[q] = x; }
    const uint8_t* in[256]; uint8_t* out[256];
    for (size_t i = 0; i < k; i++) in[i] = sh[perm[i]];
    for (size_t j = 0; j < m; j++) out[j] = malloc(len);
    uint8_t* tab2 = malloc(leanrs_table_size(k, m));
    if (leanrs_prepare(perm, k, perm + k, m, tab2) || run(tab2, k, m, len, in, out)) {
      printf("FAIL %s: reconstruct rejected\n", name); return 1;
    }
    for (size_t j = 0; j < m; j++) {
      if (memcmp(out[j], sh[perm[k + j]], len)) {
        printf("FAIL %s: reconstruct k=%zu m=%zu len=%zu lost=%u\n", name, k, m, len, perm[k + j]);
        return 1;
      }
      free(out[j]);
    }
    free(tab2);
  }
  for (size_t p = 0; p < n; p++) free(sh[p]);
  free(sh); free(tab);
  return 0;
}

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

int main(int argc, char** argv) {
  init_gf();
  size_t ks[] = {1, 2, 3, 4, 6, 10, 17, 32, 100, 200}, ms[] = {1, 2, 3, 4, 8};
  size_t lens[] = {1, 7, 31, 63, 64, 65, 127, 128, 200, 1000, 4097};
  int cases = 0;
  for (size_t a = 0; a < sizeof ks / sizeof *ks; a++)
    for (size_t b = 0; b < sizeof ms / sizeof *ms; b++)
      for (size_t c = 0; c < sizeof lens / sizeof *lens; c++) {
        if (ks[a] + ms[b] > 256 || (ks[a] >= 100 && lens[c] > 200)) continue;
        if (check(ks[a], ms[b], lens[c], leanrs_run, "run")) return 1;
        if (check(ks[a], ms[b], lens[c], leanrs_run_portable, "portable")) return 1;
        cases += 2;
      }
  if (check(128, 128, 100, leanrs_run, "run") || check(255, 1, 64, leanrs_run, "run")) return 1;
  printf("leanrs: %d configurations (encode vs independent reference, 3 reconstructions each), "
         "verified kernel %s\n", cases + 2, leanrs_has_verified_kernel() ? "in use" : "NOT in use");

  /* invalid arguments */
  uint8_t xs[3] = {0, 1, 1}, ys[1] = {5}, tab[96], buf[256];
  const uint8_t* in[2] = {buf, buf + 64};
  uint8_t* out[1] = {buf + 32};
  int bad = 0;
  bad |= leanrs_prepare(xs, 3, ys, 1, tab) != -1;              /* repeated point */
  bad |= leanrs_prepare(xs, 0, ys, 1, tab) != -1;              /* k = 0 */
  bad |= leanrs_prepare(xs, 2, ys, 0, tab) != -1;              /* r = 0 */
  leanrs_prepare(xs, 2, ys, 1, tab);
  bad |= leanrs_run(tab, 2, 1, 64, in, out) != -1;             /* output overlaps an input */
  out[0] = tab + 8;
  bad |= leanrs_run(tab, 2, 1, 64, in, out) != -1;             /* output overlaps the table */
  out[0] = buf + 128;
  bad |= leanrs_run(tab, 2, 1, 0, in, out) != -1;              /* len = 0 */
  bad |= leanrs_run(tab, 2, 1, 64, in, out) != 0;              /* fine */
  if (bad) { printf("FAIL: invalid arguments not rejected\n"); return 1; }
  printf("leanrs: invalid arguments rejected\n");

  if (argc > 1 && !strcmp(argv[1], "bench")) {
    size_t cfg[][2] = {{10, 4}, {4, 2}, {17, 3}, {12, 8}};
    for (int c = 0; c < 4; c++)
      for (size_t L = 4096; L <= (1u << 20); L *= 16) {
        size_t k = cfg[c][0], m = cfg[c][1];
        uint8_t xs2[256], ys2[256];
        for (size_t i = 0; i < k; i++) xs2[i] = (uint8_t)i;
        for (size_t j = 0; j < m; j++) ys2[j] = (uint8_t)(k + j);
        uint8_t* t2 = malloc(leanrs_table_size(k, m));
        double p0 = now();
        int reps0 = 1000;
        for (int r = 0; r < reps0; r++) leanrs_prepare(xs2, k, ys2, m, t2);
        double prep = (now() - p0) / reps0;
        uint8_t* in2[256]; uint8_t* out2[256];
        for (size_t i = 0; i < k; i++) { in2[i] = aligned_alloc(16384, (L + 16383) / 16384 * 16384); memset(in2[i], (int)i, L); }
        for (size_t j = 0; j < m; j++) out2[j] = aligned_alloc(16384, (L + 16383) / 16384 * 16384);
        for (int which = 0; which < 2; which++) {
          RunFn f = which ? leanrs_run_portable : leanrs_run;
          size_t reps = ((size_t)1 << (which ? 26 : 29)) / (k * L) + 1;
          double t0 = now();
          for (size_t r = 0; r < reps; r++) f(t2, k, m, L, (const uint8_t* const*)in2, out2);
          double s = now() - t0;
          printf("%zu+%zu shard=%-8zu %-8s %6.2f GB/s of data", k, m, L, which ? "portable" : "run",
                 k * L * reps / s / 1e9);
          printf(which ? "\n" : "   (prepare %.1f us)\n", prep * 1e6);
        }
        for (size_t i = 0; i < k; i++) free(in2[i]);
        for (size_t j = 0; j < m; j++) free(out2[j]);
        free(t2);
      }
  }
  return 0;
}
