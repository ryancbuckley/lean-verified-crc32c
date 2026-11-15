// In-process differential test of the C++ wrapper against abseil: random
// sizes and alignments, exactly-sized heap buffers (so a sanitizer build
// faults on any read or write outside them), copy checked byte for byte.
// Usage: test_diff [iterations] [seed]
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>

#include "absl/crc/crc32c.h"
#include "leanmemcpy.h"

int main(int argc, char** argv) {
  long iters = argc > 1 ? std::atol(argv[1]) : 200000;
  uint64_t seed = argc > 2 ? std::strtoull(argv[2], nullptr, 10) : 1;
  std::mt19937_64 rng(seed);
  // sizes on either side of every internal threshold
  const size_t edges[] = {0, 1, 7, 8, 9, 15, 16, 17, 31, 32, 39, 40, 41, 47, 48, 95, 96, 97, 191, 192,
                          383, 384, 385, 767, 768, 769, 1151, 1152, 4095, 4096, 4097, 8191, 8192, 8193,
                          24559, 24576, 24577, 65535, 65536, 65537};
  const size_t nedges = sizeof(edges) / sizeof(edges[0]);
  long checked = 0;
  for (long it = 0; it < iters; ++it) {
    size_t n;
    switch (rng() % 8) {
      case 0: n = edges[rng() % nedges]; break;
      case 1: n = edges[rng() % nedges] + rng() % 9; break;
      case 2: n = rng() % 64; break;
      case 3: case 4: n = rng() % 1100; break;
      case 5: n = rng() % 9000; break;
      case 6: n = rng() % 70000; break;
      default: n = rng() % 300;
    }
    // exact-size allocations at a random offset from the allocator's alignment
    size_t so = rng() % 8, d_o = rng() % 8;
    unsigned char* sbuf = static_cast<unsigned char*>(std::malloc(so + n + 1));
    unsigned char* dbuf = static_cast<unsigned char*>(std::malloc(d_o + n + 1));
    unsigned char* src = sbuf + so + 1 - 1;  // src occupies [so, so+n); byte so+n is a guard
    unsigned char* dst = dbuf + d_o;
    for (size_t i = 0; i < so + n + 1; ++i) sbuf[i] = static_cast<unsigned char>(rng());
    std::memset(dbuf, 0x5a, d_o + n + 1);
    uint32_t init = (it % 3 == 0) ? 0 : static_cast<uint32_t>(rng());
    absl::string_view sv(reinterpret_cast<const char*>(src), n);
    uint32_t want = static_cast<uint32_t>(absl::ExtendCrc32c(absl::crc32c_t{init}, sv));
    uint32_t e1 = leanmemcpy::ExtendCrc32c(init, src, n);
    uint32_t e2 = leanmemcpy::ExtendCrc32cPortable(init, src, n);
    uint32_t m1 = leanmemcpy::MemcpyCrc32c(dst, src, n, init);
    bool copy_ok = std::memcmp(dst, src, n) == 0 && dbuf[d_o + n] == 0x5a;
    for (size_t i = 0; i < d_o; ++i) copy_ok = copy_ok && dbuf[i] == 0x5a;
    std::memset(dbuf, 0x5a, d_o + n + 1);
    uint32_t m2 = leanmemcpy::MemcpyCrc32cPortable(dst, src, n, init);
    copy_ok = copy_ok && std::memcmp(dst, src, n) == 0 && dbuf[d_o + n] == 0x5a;
    if (e1 != want || e2 != want || m1 != want || m2 != want || !copy_ok) {
      std::fprintf(stderr, "MISMATCH n=%zu so=%zu do=%zu init=%u want=%u got=%u/%u/%u/%u copy_ok=%d\n",
                   n, so, d_o, init, want, e1, e2, m1, m2, copy_ok);
      return 1;
    }
    std::free(sbuf); std::free(dbuf);
    ++checked;
  }
  std::printf("OK: %ld cases agree with abseil (hardware path available: %d)\n", checked,
              leanmemcpy::HardwareAvailable());
  return 0;
}
