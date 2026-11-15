// libFuzzer target: differential fuzzing of every verified entry point against
// Abseil under AddressSanitizer + UndefinedBehaviorSanitizer + SanitizerCoverage.
//
// Every execution checks all four entry points on the same input:
//   1. leancrc32c_extend_crc32c          (dispatched hardware / fallback path)
//   2. leancrc32c_extend_crc32c_portable (portable Chorba / slicing-by-8 path)
//   3. leancrc32c_memcpy_crc32c          (dispatched fused copy + CRC32C)
//   4. leancrc32c_memcpy_crc32c_portable (portable fused copy + CRC32C)
// against absl::ExtendCrc32c, plus byte-for-byte destination equality, prefix
// sentinel preservation, and (alternating 50/50) either exact end-of-buffer
// ASan heap redzones (`trail == 0`) or 8-byte trailing sentinel checks
// (`trail == 8`), across arbitrary source and destination alignments `0..7`,
// zero-length `(nullptr, nullptr, 0)` calls, and lengths straddling every
// internal kernel and multi-stream threshold up to 70,000 bytes.
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>

#include "absl/crc/crc32c.h"
#include "leancrc32c.h"

namespace {

constexpr size_t kThresholds[16] = {
    0,     8,     16,    32,    40,    48,    96,    384,
    768,   1152,  2048,  4096,  8192,  12288, 24576, 65536,
};

void FillSynthetic(uint8_t* dst, size_t n, const uint8_t* seed, size_t seed_len) {
  uint64_t x = 0x9E3779B97F4A7C15ull ^ static_cast<uint64_t>(n);
  for (size_t i = 0; i < seed_len; ++i) {
    x = (x ^ seed[i]) * 0x100000001B3ull;
  }
  size_t i = 0;
  for (; i + 8 <= n; i += 8) {
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    std::memcpy(dst + i, &x, 8);
  }
  if (i < n) {
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    std::memcpy(dst + i, &x, n - i);
  }
}

void CheckAllPaths(uint32_t init, const uint8_t* src, size_t n, size_t d_off,
                   size_t trail, bool use_null_zero) {
  if (n == 0 && use_null_zero) {
    if (leancrc32c::ExtendCrc32c(init, nullptr, 0) != init) std::abort();
    if (leancrc32c::ExtendCrc32cPortable(init, nullptr, 0) != init) std::abort();
    if (leancrc32c::MemcpyCrc32c(nullptr, nullptr, 0, init) != init) std::abort();
    if (leancrc32c::MemcpyCrc32cPortable(nullptr, nullptr, 0, init) != init) std::abort();
    if (init == 0 && leancrc32c::ComputeCrc32c(nullptr, 0) != 0) std::abort();
    return;
  }

  const uint32_t want = static_cast<uint32_t>(
      absl::ExtendCrc32c(absl::crc32c_t{init}, {reinterpret_cast<const char*>(src), n}));

  if (leancrc32c::ExtendCrc32c(init, src, n) != want) std::abort();
  if (leancrc32c::ExtendCrc32cPortable(init, src, n) != want) std::abort();
  if (init == 0 && leancrc32c::ComputeCrc32c(src, n) != want) std::abort();

  const size_t d_alloc = d_off + n + trail;
  uint8_t* dbuf = static_cast<uint8_t*>(std::malloc(d_alloc));
  if (d_alloc != 0 && !dbuf) std::abort();
  uint8_t* dst = dbuf + d_off;

  for (int path = 0; path < 2; ++path) {
    if (d_alloc != 0) std::memset(dbuf, 0xA5, d_alloc);
    const uint32_t got = path == 0 ? leancrc32c::MemcpyCrc32c(dst, src, n, init)
                                   : leancrc32c::MemcpyCrc32cPortable(dst, src, n, init);
    if (got != want) std::abort();
    if (n != 0 && std::memcmp(dst, src, n) != 0) std::abort();
    for (size_t i = 0; i < d_off; ++i) {
      if (dbuf[i] != 0xA5) std::abort();
    }
    for (size_t i = 0; i < trail; ++i) {
      if (dst[n + i] != 0xA5) std::abort();
    }
  }

  std::free(dbuf);
}

}  // namespace

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
  (void)leancrc32c::HardwareAvailable();

  if (size == 0) {
    CheckAllPaths(0, nullptr, 0, 0, 0, true);
    return 0;
  }

  if (size < 8) {
    const size_t s_off = data[0] & 7;
    const size_t d_off = (data[0] >> 3) & 7;
    const size_t trail = (data[0] & 0x40) ? 8 : 0;
    const size_t n = size - 1;
    uint8_t* sbuf = static_cast<uint8_t*>(std::malloc(s_off + n));
    if (s_off + n != 0 && !sbuf) std::abort();
    uint8_t* src = sbuf + s_off;
    if (n != 0) std::memcpy(src, data + 1, n);
    CheckAllPaths(0, src, n, d_off, trail, (data[0] & 0x80) != 0);
    std::free(sbuf);
    return 0;
  }

  const uint8_t mode = data[0];
  uint32_t init;
  std::memcpy(&init, data + 1, 4);
  if (mode & 0x40) init = 0;
  const size_t s_off = data[5] & 7;
  const size_t d_off = (data[5] >> 3) & 7;
  const size_t trail = (data[5] & 0x40) ? 8 : 0;
  const bool use_null_zero = (data[5] & 0x80) != 0;

  size_t n = 0;
  bool synthetic = false;
  const uint8_t kind = mode & 0x1F;
  if ((mode & 0x07) != 0) {
    // 87.5% of inputs: direct coverage-guided payload bytes (0..max_len-8).
    n = size - 8;
  } else if (kind == 24) {
    // ~3.125% of inputs: arbitrary synthetic sizes up to 70,000 bytes.
    const size_t raw16 =
        static_cast<size_t>(data[6]) | (static_cast<size_t>(data[7]) << 8);
    n = raw16 + ((mode & 0x20) ? 4465 : 0);
    synthetic = true;
  } else {
    // ~9.375% of inputs: sniper around every internal kernel/stream threshold.
    const size_t base = kThresholds[(data[6] >> 4) & 15];
    const ptrdiff_t delta =
        static_cast<ptrdiff_t>(data[6] & 15) - 7 +
        static_cast<ptrdiff_t>((data[7] & 7) * ((mode & 0x20) ? 8 : 1));
    const ptrdiff_t cand = static_cast<ptrdiff_t>(base) + delta;
    n = cand > 0 ? static_cast<size_t>(cand) : 0;
    synthetic = true;
  }

  uint8_t* sbuf = static_cast<uint8_t*>(std::malloc(s_off + n));
  if (s_off + n != 0 && !sbuf) std::abort();
  uint8_t* src = sbuf + s_off;
  if (synthetic) {
    FillSynthetic(src, n, data + 8, size - 8);
  } else if (n != 0) {
    std::memcpy(src, data + 8, n);
  }

  CheckAllPaths(init, src, n, d_off, trail, use_null_zero);
  std::free(sbuf);
  return 0;
}
