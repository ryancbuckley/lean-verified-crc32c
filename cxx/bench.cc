// Quick same-process throughput comparison of the verified library and
// abseil through their C++ entry points. Not the full benchmarking protocol
// (no thread pinning or cache flushing); aligned buffers.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

#include "absl/crc/crc32c.h"
#include "leanmemcpy.h"

static double now() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

int main() {
  const size_t sizes[] = {16, 64, 256, 1024, 4096, 65536, 1 << 20, 64 << 20};
  std::vector<char> buf(64 << 20), dst(64 << 20);
  uint64_t x = 88172645463325252ull;
  for (auto& c : buf) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; c = static_cast<char>(x); }
  std::memset(dst.data(), 1, dst.size());
  volatile uint32_t warm = 0;
  for (int i = 0; i < 3000; i++) warm = warm ^ leanmemcpy::ComputeCrc32c(buf.data(), 65536);
  const char* names[] = {"lean MemcpyCrc32c", "absl MemcpyCrc32c", "lean MemcpyCrc32cPortable",
                         "lean ExtendCrc32c", "absl ExtendCrc32c", "lean ExtendCrc32cPortable",
                         "memcpy + absl ComputeCrc32c", "memcpy"};
  std::printf("hardware path available: %d\n%-30s", leanmemcpy::HardwareAvailable(), "GB/s");
  for (size_t n : sizes) std::printf("%9zu", n);
  std::printf("\n");
  for (int k = 0; k < 8; k++) {
    std::printf("%-30s", names[k]);
    for (size_t n : sizes) {
      size_t reps = std::max<size_t>(3, std::min<size_t>(200000, (64u << 20) / n));
      double t[9];
      uint32_t sink = 0;
      const char* s = buf.data();
      char* d = dst.data();
      for (int r = 0; r < 9; r++) {
        double a = now();
        for (size_t q = 0; q < reps; q++) {
          switch (k) {
            case 0: sink = leanmemcpy::MemcpyCrc32c(d, s, n, sink); break;
            case 1: sink = static_cast<uint32_t>(absl::MemcpyCrc32c(d, s, n, absl::crc32c_t{sink})); break;
            case 2: sink = leanmemcpy::MemcpyCrc32cPortable(d, s, n, sink); break;
            case 3: sink = leanmemcpy::ExtendCrc32c(sink, s, n); break;
            case 4: sink = static_cast<uint32_t>(absl::ExtendCrc32c(absl::crc32c_t{sink}, {s, n})); break;
            case 5: sink = leanmemcpy::ExtendCrc32cPortable(sink, s, n); break;
            case 6: std::memcpy(d, s, n);
                    sink = static_cast<uint32_t>(absl::ExtendCrc32c(absl::crc32c_t{sink}, {d, n})); break;
            default: std::memcpy(d, s, n); sink ^= static_cast<unsigned char>(d[n / 2]);
          }
        }
        t[r] = (now() - a) / reps;
      }
      std::sort(t, t + 9);
      std::printf("%9.2f", n / t[4] / 1e9);
    }
    std::printf("\n");
  }
  return 0;
}
