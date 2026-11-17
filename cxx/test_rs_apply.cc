// Guard-page, exact-output and throughput test of leanrs_apply (AArch64 only).
// Usage: test_rs_apply [bench]
#include <sys/mman.h>
#include <unistd.h>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

extern "C" void leanrs_apply(const uint8_t* tab, const uint8_t* const* in, uint8_t* const* out,
                             size_t k, size_t r, size_t len);

static uint8_t gmul(uint8_t a, uint8_t b) {
  uint8_t r = 0;
  for (int i = 7; i >= 0; i--) { r = (uint8_t)((r << 1) ^ ((r & 0x80) ? 0x1d : 0)); if ((b >> i) & 1) r ^= a; }
  return r;
}
static uint64_t rng = 88172645463325252ull;
static uint8_t rnd() { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return (uint8_t)rng; }

// A buffer of `n` bytes ending exactly at an inaccessible page, starting right after another.
struct Guarded {
  uint8_t* base; size_t span; uint8_t* p;
  Guarded(size_t n, bool atEnd) {
    size_t pg = (size_t)getpagesize(), body = (n + pg - 1) / pg * pg + pg;
    span = body + 2 * pg;
    base = (uint8_t*)mmap(nullptr, span, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (base == MAP_FAILED) { perror("mmap"); exit(2); }
    mprotect(base, pg, PROT_NONE); mprotect(base + pg + body, pg, PROT_NONE);
    p = atEnd ? base + pg + body - n : base + pg;
  }
  ~Guarded() { munmap(base, span); }
};

static void fillTab(uint8_t* tab, const std::vector<uint8_t>& coef) {
  for (size_t n = 0; n < coef.size(); n++)
    for (int v = 0; v < 16; v++) { tab[n * 32 + v] = gmul(coef[n], (uint8_t)v); tab[n * 32 + 16 + v] = gmul(coef[n], (uint8_t)(v << 4)); }
}

int main(int argc, char** argv) {
  size_t cases = 0;
  for (size_t k : {1, 2, 3, 5, 10, 17})
    for (size_t r : {1, 2, 3, 4, 5})
      for (size_t len : {64, 65, 70, 100, 127, 128, 129, 191, 192, 193, 255, 256, 300, 1000})
        for (int atEnd = 0; atEnd < 2; atEnd++) {
          std::vector<uint8_t> coef(k * r);
          for (auto& c : coef) c = rnd();
          Guarded tab(32 * k * r, atEnd), inP(8 * k, atEnd), outP(8 * r, atEnd);
          fillTab(tab.p, coef);
          std::vector<Guarded*> in, out;
          for (size_t i = 0; i < k; i++) { in.push_back(new Guarded(len, atEnd)); for (size_t t = 0; t < len; t++) in[i]->p[t] = rnd(); memcpy(inP.p + 8 * i, &in[i]->p, 8); }
          for (size_t j = 0; j < r; j++) { out.push_back(new Guarded(len, atEnd)); memset(out[j]->p, 0xA5, len); memcpy(outP.p + 8 * j, &out[j]->p, 8); }
          // the inputs, table and pointer arrays must not be written: make them read-only
          size_t pg = (size_t)getpagesize();
          mprotect(tab.base + pg, tab.span - 2 * pg, PROT_READ);
          mprotect(inP.base + pg, inP.span - 2 * pg, PROT_READ);
          mprotect(outP.base + pg, outP.span - 2 * pg, PROT_READ);
          for (auto g : in) mprotect(g->base + pg, g->span - 2 * pg, PROT_READ);
          leanrs_apply(tab.p, (const uint8_t* const*)inP.p, (uint8_t* const*)outP.p, k, r, len);
          for (size_t j = 0; j < r; j++)
            for (size_t t = 0; t < len; t++) {
              uint8_t want = 0;
              for (size_t i = 0; i < k; i++) want ^= gmul(coef[j * k + i], in[i]->p[t]);
              if (out[j]->p[t] != want) { printf("MISMATCH k=%zu r=%zu len=%zu row=%zu byte=%zu\n", k, r, len, j, t); return 1; }
            }
          for (auto g : in) delete g;
          for (auto g : out) delete g;
          cases++;
        }
  printf("leanrs_apply: %zu guarded cases OK\n", cases);
  if (argc > 1 && !strcmp(argv[1], "bench")) {
    size_t cfg[][2] = {{10, 4}, {4, 2}, {17, 3}, {12, 8}, {10, 1}};
    for (auto& c : cfg)
      for (size_t L : {(size_t)4096, (size_t)65536, (size_t)67616, (size_t)1 << 20}) {
        size_t k = c[0], r = c[1];
        std::vector<uint8_t*> in(k), out(r);
        std::vector<uint8_t> coef(k * r), tab(32 * k * r);
        for (auto& x : coef) x = rnd();
        fillTab(tab.data(), coef);
        size_t al = (L + 16383) / 16384 * 16384;
        for (auto& p : in) { p = (uint8_t*)aligned_alloc(16384, al); for (size_t t = 0; t < L; t++) p[t] = rnd(); }
        for (auto& p : out) p = (uint8_t*)aligned_alloc(16384, al);
        size_t reps = ((size_t)1 << 29) / (k * L) + 1;
        auto t0 = std::chrono::steady_clock::now();
        for (size_t n = 0; n < reps; n++) leanrs_apply(tab.data(), in.data(), out.data(), k, r, L);
        double s = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        printf("%zu+%zu shard=%-8zu %.1f GB/s of data\n", k, r, L, k * L * reps / s / 1e9);
      }
  }
  return 0;
}
