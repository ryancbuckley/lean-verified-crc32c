// In-process differential test of the C/C++ wrapper against Abseil: random
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

  // Explicit null + zero-length checks.
  if (leanmemcpy::ExtendCrc32c(0xDEADBEEFu, nullptr, 0) != 0xDEADBEEFu ||
      leanmemcpy::ExtendCrc32cPortable(0xDEADBEEFu, nullptr, 0) != 0xDEADBEEFu ||
      leanmemcpy::MemcpyCrc32c(nullptr, nullptr, 0, 0xDEADBEEFu) != 0xDEADBEEFu ||
      leanmemcpy::MemcpyCrc32cPortable(nullptr, nullptr, 0, 0xDEADBEEFu) != 0xDEADBEEFu) {
    std::fprintf(stderr, "MISMATCH nullptr count=0\n");
    return 1;
  }

  // Sizes on either side of every internal threshold (portable 40/2048/8192,
  // hardware 16/48/96/384/768/24576, 64 KiB).
  const size_t edges[] = {0, 1, 7, 8, 9, 15, 16, 17, 31, 32, 39, 40, 41, 47, 48, 95, 96, 97,
                          191, 192, 383, 384, 385, 767, 768, 769, 1151, 1152, 2047, 2048, 2049,
                          4095, 4096, 4097, 8191, 8192, 8193, 24559, 24576, 24577,
                          65535, 65536, 65537};
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
    size_t so = rng() % 8, d_o = rng() % 8;
    // Alternate between exact end-of-allocation (`trail = 0`, maximizing ASan
    // redzone sensitivity) and 1-byte sentinel (`trail = 1`).
    size_t trail = static_cast<size_t>(it & 1);
    size_t s_alloc = (so + n + trail == 0) ? 1 : (so + n + trail);
    size_t d_alloc = (d_o + n + trail == 0) ? 1 : (d_o + n + trail);
    unsigned char* sbuf = static_cast<unsigned char*>(std::malloc(s_alloc));
    unsigned char* dbuf = static_cast<unsigned char*>(std::malloc(d_alloc));
    if (!sbuf || !dbuf) std::abort();
    unsigned char* src = sbuf + so;
    unsigned char* dst = dbuf + d_o;
    for (size_t i = 0; i < s_alloc; ++i) sbuf[i] = static_cast<unsigned char>(rng());
    std::memset(dbuf, 0x5a, d_alloc);
    uint32_t init = (it % 3 == 0) ? 0 : static_cast<uint32_t>(rng());
    absl::string_view sv(reinterpret_cast<const char*>(src), n);
    uint32_t want = static_cast<uint32_t>(absl::ExtendCrc32c(absl::crc32c_t{init}, sv));
    uint32_t e1 = leanmemcpy::ExtendCrc32c(init, src, n);
    uint32_t e2 = leanmemcpy::ExtendCrc32cPortable(init, src, n);
    uint32_t m1 = leanmemcpy::MemcpyCrc32c(dst, src, n, init);
    bool copy_ok = (n == 0 || std::memcmp(dst, src, n) == 0) &&
                   (trail == 0 || dbuf[d_o + n] == 0x5a);
    for (size_t i = 0; i < d_o; ++i) copy_ok = copy_ok && dbuf[i] == 0x5a;
    std::memset(dbuf, 0x5a, d_alloc);
    uint32_t m2 = leanmemcpy::MemcpyCrc32cPortable(dst, src, n, init);
    copy_ok = copy_ok && (n == 0 || std::memcmp(dst, src, n) == 0) &&
              (trail == 0 || dbuf[d_o + n] == 0x5a);
    for (size_t i = 0; i < d_o; ++i) copy_ok = copy_ok && dbuf[i] == 0x5a;
    if (e1 != want || e2 != want || m1 != want || m2 != want || !copy_ok) {
      std::fprintf(stderr, "MISMATCH n=%zu so=%zu do=%zu init=%u want=%u got=%u/%u/%u/%u copy_ok=%d\n",
                   n, so, d_o, init, want, e1, e2, m1, m2, copy_ok);
      return 1;
    }
    std::free(sbuf);
    std::free(dbuf);
    ++checked;
  }
  std::printf("OK: %ld cases agree with abseil (hardware path available: %d)\n", checked,
              leanmemcpy::HardwareAvailable());
  return 0;
}
