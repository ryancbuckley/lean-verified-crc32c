// libFuzzer target: the verified library against abseil, on both paths.
//
// Each input drives one comparison of ExtendCrc32c, ExtendCrc32cPortable,
// MemcpyCrc32c and MemcpyCrc32cPortable with absl::ExtendCrc32c, on an
// exactly-sized heap buffer at a fuzzer-chosen alignment, and checks the copy
// byte for byte including guard bytes around the destination.
//
// Input layout: byte 0 = mode, bytes 1..4 = initial CRC, byte 5 = alignments.
//   mode bit 0 clear: the rest of the input is the message (coverage-guided
//     content, lengths up to -max_len).
//   mode bit 0 set: bytes 6..7 give a length up to 70000 and the rest seeds a
//     generator, so sizes around every internal threshold are reached without
//     huge inputs.
#include <cstdint>
#include <cstdlib>
#include <cstring>

#include "absl/crc/crc32c.h"
#include "leanmemcpy.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
  if (size < 8) return 0;
  const uint8_t mode = data[0];
  uint32_t init;
  std::memcpy(&init, data + 1, 4);
  if (mode & 2) init = 0;
  const size_t s_off = data[5] & 7, d_off = (data[5] >> 3) & 7;
  size_t n;
  if (mode & 1) {
    n = (static_cast<size_t>(data[6]) | (static_cast<size_t>(data[7]) << 8)) + ((mode & 4) ? 4465 : 0);
    if (mode & 8) n = n % 1300;
  } else {
    n = size - 8;
  }
  uint8_t* sbuf = static_cast<uint8_t*>(std::malloc(s_off + n));
  uint8_t* dbuf = static_cast<uint8_t*>(std::malloc(d_off + n + 8));
  if ((s_off + n != 0 && !sbuf) || !dbuf) std::abort();
  uint8_t* src = sbuf + s_off;
  uint8_t* dst = dbuf + d_off;
  if (mode & 1) {
    uint64_t x = 0x9E3779B97F4A7C15ull;
    for (size_t i = 8; i < size; ++i) x = (x ^ data[i]) * 0x100000001B3ull;
    for (size_t i = 0; i < n; ++i) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; src[i] = static_cast<uint8_t>(x); }
  } else if (n != 0) {
    std::memcpy(src, data + 8, n);
  }
  const uint32_t want = static_cast<uint32_t>(
      absl::ExtendCrc32c(absl::crc32c_t{init}, {reinterpret_cast<const char*>(src), n}));
  if (leanmemcpy::ExtendCrc32c(init, src, n) != want) std::abort();
  if (leanmemcpy::ExtendCrc32cPortable(init, src, n) != want) std::abort();
  for (int path = 0; path < 2; ++path) {
    std::memset(dbuf, 0xA5, d_off + n + 8);
    const uint32_t got = path == 0 ? leanmemcpy::MemcpyCrc32c(dst, src, n, init)
                                   : leanmemcpy::MemcpyCrc32cPortable(dst, src, n, init);
    if (got != want) std::abort();
    if (n != 0 && std::memcmp(dst, src, n) != 0) std::abort();
    for (size_t i = 0; i < d_off; ++i) if (dbuf[i] != 0xA5) std::abort();
    for (size_t i = 0; i < 8; ++i) if (dst[n + i] != 0xA5) std::abort();
  }
  std::free(sbuf);
  std::free(dbuf);
  return 0;
}
