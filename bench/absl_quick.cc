// Quick throughput check of abseil's CRC32C entry points, to compare with
// tests/BenchPortable.lean on the same machine. Not the benchmarking protocol.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

#include "absl/crc/crc32c.h"
#include "absl/strings/string_view.h"

static double now() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

int main() {
  const size_t sizes[] = {16, 64, 256, 1024, 4096, 65536, 1 << 20, 64 << 20};
  std::vector<char> buf(64 << 20), dst(64 << 20);
  uint64_t x = 88172645463325252ull;
  for (auto& c : buf) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; c = static_cast<char>(x); }
  volatile uint32_t warm = 0;
  for (int i = 0; i < 3000; i++) warm = warm ^ static_cast<uint32_t>(absl::ComputeCrc32c({buf.data(), 65536}));
  const char* names[] = {"absl::ExtendCrc32c", "absl::MemcpyCrc32c", "memcpy"};
  for (int k = 0; k < 3; k++) {
    for (size_t n : sizes) {
      size_t reps = std::max<size_t>(3, std::min<size_t>(200000, (64u << 20) / n));
      double t[9];
      uint32_t sink = 0;
      for (int r = 0; r < 9; r++) {
        double a = now();
        for (size_t q = 0; q < reps; q++) {
          if (k == 0) sink = static_cast<uint32_t>(absl::ExtendCrc32c(absl::crc32c_t{sink}, {buf.data(), n}));
          else if (k == 1) sink = static_cast<uint32_t>(absl::MemcpyCrc32c(dst.data(), buf.data(), n, absl::crc32c_t{sink}));
          else { std::memcpy(dst.data(), buf.data(), n); sink ^= static_cast<unsigned char>(dst[n / 2]); }
        }
        t[r] = (now() - a) / reps;
      }
      std::sort(t, t + 9);
      std::printf("%s %zu bytes: %.2f GB/s\n", names[k], n, n / t[4] / 1e9);
    }
  }
  return 0;
}
