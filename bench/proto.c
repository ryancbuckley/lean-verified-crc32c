// Prototype of candidate portable CRC32C kernels, to choose a design before
// proving it. Not part of the verified code. Each kernel is checked against a
// bitwise reference, then timed.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define POLY 0x82F63B78u

static uint32_t raw_bitwise(uint32_t s, const uint8_t *p, size_t n) {
  for (size_t i = 0; i < n; i++) {
    s ^= p[i];
    for (int k = 0; k < 8; k++) s = (s >> 1) ^ ((s & 1) ? POLY : 0);
  }
  return s;
}

static uint32_t T[8][256];
static void init_tables(void) {
  for (uint32_t i = 0; i < 256; i++) {
    uint32_t c = i;
    for (int k = 0; k < 8; k++) c = (c >> 1) ^ ((c & 1) ? POLY : 0);
    T[0][i] = c;
  }
  for (uint32_t i = 0; i < 256; i++)
    for (int t = 1; t < 8; t++) T[t][i] = (T[t - 1][i] >> 8) ^ T[0][T[t - 1][i] & 0xff];
}

static uint32_t raw_table1(uint32_t s, const uint8_t *p, size_t n) {
  for (size_t i = 0; i < n; i++) s = (s >> 8) ^ T[0][(s ^ p[i]) & 0xff];
  return s;
}

static inline uint64_t ld(const uint8_t *p) { uint64_t w; memcpy(&w, p, 8); return w; }

static inline uint32_t step_word_slice8(uint32_t s, uint64_t w) {
  w ^= s;
  return T[7][w & 0xff] ^ T[6][(w >> 8) & 0xff] ^ T[5][(w >> 16) & 0xff] ^ T[4][(w >> 24) & 0xff] ^
         T[3][(w >> 32) & 0xff] ^ T[2][(w >> 40) & 0xff] ^ T[1][(w >> 48) & 0xff] ^ T[0][w >> 56];
}

static uint32_t raw_slice8(uint32_t s, const uint8_t *p, size_t n) {
  while (n >= 8) {
    s = step_word_slice8(s, ld(p));
    p += 8; n -= 8;
  }
  return raw_table1(s, p, n);
}

static inline uint32_t mul_mod(uint32_t a, uint32_t b) {
  uint32_t acc = 0;
  for (int i = 0; i < 32; i++) {
    if (b & 0x80000000u) acc ^= a;
    b <<= 1;
    a = (a >> 1) ^ ((a & 1) ? POLY : 0);
  }
  return acc;
}

static uint32_t pow_mod_x64(size_t ws) {
  uint32_t a = 0x00800000u;
  for (int k = 0; k < 3; k++) a = mul_mod(a, a);  // X^64 mod G
  uint32_t r = 0x80000000u;
  while (ws) {
    if (ws & 1) r = mul_mod(r, a);
    a = mul_mod(a, a);
    ws >>= 1;
  }
  return r;
}

// Single-stream register kernel for Z = x^209 + x^144 + x^54 + x^39 + x^14 + 1.
static uint32_t raw_reg209(uint32_t s, const uint8_t *p, size_t n) {
  if (n < 40) return raw_slice8(s, p, n);
  size_t nw = n / 8;
  uint64_t n1 = s, n2 = 0, n3 = 0, n4 = 0;
  size_t i = 0;
  for (; i + 4 < nw; i++) {
    uint64_t v = ld(p + 8 * i) ^ n1;
    n1 = n2 ^ (v << 1);
    n2 = n3 ^ (v >> 63) ^ (v << 27) ^ (v << 42);
    n3 = n4 ^ (v >> 37) ^ (v >> 22) ^ (v << 3) ^ (v << 17);
    n4 = (v >> 61) ^ (v >> 47);
  }
  uint32_t c = step_word_slice8(0, ld(p + 8 * i) ^ n1);
  c = step_word_slice8(c, ld(p + 8 * i + 8) ^ n2);
  c = step_word_slice8(c, ld(p + 8 * i + 16) ^ n3);
  c = step_word_slice8(c, ld(p + 8 * i + 24) ^ n4);
  return raw_table1(c, p + 8 * nw, n - 8 * nw);
}

// 4-stream interleaved register kernel matching MemcpyCrc32c/Impl/Portable.lean.
static uint32_t raw_reg209_4x(uint32_t s, const uint8_t *p, size_t n) {
  if (n < 8192) return raw_reg209(s, p, n);
  size_t ws = n / 32;
  size_t L = ws * 8;
  uint64_t a1 = s, a2 = 0, a3 = 0, a4 = 0;
  uint64_t b1 = 0, b2 = 0, b3 = 0, b4 = 0;
  uint64_t c1 = 0, c2 = 0, c3 = 0, c4 = 0;
  uint64_t d1 = 0, d2 = 0, d3 = 0, d4 = 0;
  size_t i = 0;
  for (; i + 4 < ws; i++) {
    uint64_t va = ld(p + 8 * i) ^ a1;
    a1 = a2 ^ (va << 1);
    a2 = a3 ^ (va >> 63) ^ (va << 27) ^ (va << 42);
    a3 = a4 ^ (va >> 37) ^ (va >> 22) ^ (va << 3) ^ (va << 17);
    a4 = (va >> 61) ^ (va >> 47);
    uint64_t vb = ld(p + L + 8 * i) ^ b1;
    b1 = b2 ^ (vb << 1);
    b2 = b3 ^ (vb >> 63) ^ (vb << 27) ^ (vb << 42);
    b3 = b4 ^ (vb >> 37) ^ (vb >> 22) ^ (vb << 3) ^ (vb << 17);
    b4 = (vb >> 61) ^ (vb >> 47);
    uint64_t vc = ld(p + 2 * L + 8 * i) ^ c1;
    c1 = c2 ^ (vc << 1);
    c2 = c3 ^ (vc >> 63) ^ (vc << 27) ^ (vc << 42);
    c3 = c4 ^ (vc >> 37) ^ (vc >> 22) ^ (vc << 3) ^ (vc << 17);
    c4 = (vc >> 61) ^ (vc >> 47);
    uint64_t vd = ld(p + 3 * L + 8 * i) ^ d1;
    d1 = d2 ^ (vd << 1);
    d2 = d3 ^ (vd >> 63) ^ (vd << 27) ^ (vd << 42);
    d3 = d4 ^ (vd >> 37) ^ (vd >> 22) ^ (vd << 3) ^ (vd << 17);
    d4 = (vd >> 61) ^ (vd >> 47);
  }
  uint32_t sa = step_word_slice8(0, ld(p + 8 * i) ^ a1);
  sa = step_word_slice8(sa, ld(p + 8 * i + 8) ^ a2);
  sa = step_word_slice8(sa, ld(p + 8 * i + 16) ^ a3);
  sa = step_word_slice8(sa, ld(p + 8 * i + 24) ^ a4);
  uint32_t sb = step_word_slice8(0, ld(p + L + 8 * i) ^ b1);
  sb = step_word_slice8(sb, ld(p + L + 8 * i + 8) ^ b2);
  sb = step_word_slice8(sb, ld(p + L + 8 * i + 16) ^ b3);
  sb = step_word_slice8(sb, ld(p + L + 8 * i + 24) ^ b4);
  uint32_t sc = step_word_slice8(0, ld(p + 2 * L + 8 * i) ^ c1);
  sc = step_word_slice8(sc, ld(p + 2 * L + 8 * i + 8) ^ c2);
  sc = step_word_slice8(sc, ld(p + 2 * L + 8 * i + 16) ^ c3);
  sc = step_word_slice8(sc, ld(p + 2 * L + 8 * i + 24) ^ c4);
  uint32_t sd = step_word_slice8(0, ld(p + 3 * L + 8 * i) ^ d1);
  sd = step_word_slice8(sd, ld(p + 3 * L + 8 * i + 8) ^ d2);
  sd = step_word_slice8(sd, ld(p + 3 * L + 8 * i + 16) ^ d3);
  sd = step_word_slice8(sd, ld(p + 3 * L + 8 * i + 24) ^ d4);
  uint32_t f = pow_mod_x64(ws);
  uint32_t s4 = mul_mod(mul_mod(mul_mod(sa, f) ^ sb, f) ^ sc, f) ^ sd;
  return raw_slice8(s4, p + 4 * L, n - 4 * L);
}

// Word-aligned kernel for Z^64: v[i] = in[i] ^ v[i-65] ^ v[i-155] ^ v[i-170] ^ v[i-195] ^ v[i-209].
// No shifts; the 209-word history lives in an L1-resident scratch buffer.
#define HIST 209
#define CHUNK 2048
static uint32_t raw_xor209(uint32_t s, const uint8_t *p, size_t n) {
  size_t nw = n / 8;
  if (nw < 2 * HIST) return raw_reg209(s, p, n);
  static uint64_t buf[HIST + CHUNK];
  memset(buf, 0, HIST * 8);
  size_t body = nw - HIST;  // words reduced; the last HIST words are left as v ^ in
  size_t done = 0;
  uint64_t first = s;
  while (done < body) {
    size_t k = body - done < CHUNK ? body - done : CHUNK;
    uint64_t *v = buf + HIST;
    for (size_t j = 0; j < k; j++) {
      v[j] = ld(p + 8 * (done + j)) ^ v[(long)j - 65] ^ v[(long)j - 155] ^ v[(long)j - 170] ^
             v[(long)j - 195] ^ v[(long)j - 209];
      if (done + j == 0) v[j] ^= first;
    }
    memmove(buf, buf + k, HIST * 8);
    done += k;
  }
  // tail: the last HIST words, each with its pending history folded in
  static uint64_t tail[HIST + 8];
  uint64_t *h = buf;  // h[HIST + t - d] = v[body + t - d]
  for (size_t t = 0; t < HIST; t++) {
    uint64_t x = ld(p + 8 * (body + t));
    if (t < 65) x ^= h[t + HIST - 65];
    if (t < 155) x ^= h[t + HIST - 155];
    if (t < 170) x ^= h[t + HIST - 170];
    if (t < 195) x ^= h[t + HIST - 195];
    x ^= h[t];
    tail[t] = x;
  }
  uint32_t c = raw_reg209(0, (const uint8_t *)tail, HIST * 8);
  return raw_table1(c, p + 8 * nw, n - 8 * nw);
}

typedef uint32_t (*fn)(uint32_t, const uint8_t *, size_t);
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int cmpd(const void *a, const void *b) { double x = *(double *)a, y = *(double *)b; return x < y ? -1 : x > y; }

int main(void) {
  init_tables();
  size_t maxn = 64u << 20;
  uint8_t *buf = malloc(maxn + 16), *dst = malloc(maxn + 16);
  uint64_t x = 88172645463325252ull;
  for (size_t i = 0; i < maxn; i++) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; buf[i] = (uint8_t)x; }
  struct { const char *name; fn f; } ks[] = {
      {"table1", raw_table1}, {"slice8", raw_slice8}, {"reg209", raw_reg209},
      {"reg209_4x", raw_reg209_4x}, {"xor209", raw_xor209}};
  int nk = (int)(sizeof(ks) / sizeof(ks[0]));
  // correctness
  for (int k = 0; k < nk; k++)
    for (size_t n = 0; n < 20000; n += (n < 600 ? 1 : 137)) {
      uint32_t want = raw_bitwise(0x12345678u + (uint32_t)n, buf + (n % 7), n);
      uint32_t got = ks[k].f(0x12345678u + (uint32_t)n, buf + (n % 7), n);
      if (want != got) { printf("MISMATCH %s n=%zu\n", ks[k].name, n); return 1; }
    }
  for (int k = 1; k < nk; k++)
    if (ks[k].f(7, buf, 1 << 20) != raw_table1(7, buf, 1 << 20)) { printf("MISMATCH %s 1MiB\n", ks[k].name); return 1; }
  printf("all kernels agree with the bitwise reference\n");
  size_t sizes[] = {16, 64, 256, 1024, 4096, 65536, 1 << 20, 64 << 20};
  printf("%-10s", "GB/s");
  for (int s = 0; s < 8; s++) printf("%10zu", sizes[s]);
  printf("\n");
  volatile uint32_t sink = 0;
  for (int k = 0; k <= nk; k++) {
    printf("%-10s", k < nk ? ks[k].name : "memcpy");
    for (int s = 0; s < 8; s++) {
      size_t n = sizes[s];
      size_t reps = (64u << 20) / n; if (reps > 200000) reps = 200000; if (reps < 3) reps = 3;
      double t[9];
      for (int r = 0; r < 9; r++) {
        double a = now();
        for (size_t q = 0; q < reps; q++) {
          if (k < nk) sink ^= ks[k].f(sink, buf, n); else { memcpy(dst, buf, n); sink ^= dst[n / 2]; }
        }
        t[r] = (now() - a) / reps;
      }
      qsort(t, 9, sizeof(double), cmpd);
      printf("%10.2f", n / t[4] / 1e9);
    }
    printf("\n");
  }
  return 0;
}
