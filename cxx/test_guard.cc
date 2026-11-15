// Guard-page test of the wrapper's trust assumption. The verified kernels are
// handed caller memory as a byte array with no header, so they must never
// read in front of the data pointer, and never past the end of the data.
//
// Each buffer is placed at multiple alignments against inaccessible guard
// pages: starting at `lo + off` (`off = 0..7`, where `off = 0` immediately
// follows a `PROT_NONE` page and `off = 1..7` is misaligned within 24 bytes of
// the `PROT_NONE` page, so any 24-byte `lean_sarray_object` header access
// faults!) and ending at `hi - n` (immediately before a `PROT_NONE` page, also
// misaligned whenever `n % 8 != 0`). Results are compared with Abseil.
#include <sys/mman.h>
#include <unistd.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

#include "absl/crc/crc32c.h"
#include "leanmemcpy.h"

int main() {
  // Null pointer + zero count must never dereference or fault.
  if (leanmemcpy::ExtendCrc32c(0x13579BDFu, nullptr, 0) != 0x13579BDFu ||
      leanmemcpy::ExtendCrc32cPortable(0x13579BDFu, nullptr, 0) != 0x13579BDFu ||
      leanmemcpy::MemcpyCrc32c(nullptr, nullptr, 0, 0x2468ACE0u) != 0x2468ACE0u ||
      leanmemcpy::MemcpyCrc32cPortable(nullptr, nullptr, 0, 0x2468ACE0u) != 0x2468ACE0u) {
    std::fprintf(stderr, "MISMATCH nullptr count=0\n");
    return 1;
  }

  const size_t page = static_cast<size_t>(sysconf(_SC_PAGESIZE));
  const size_t maxn = 80000;
  const size_t body = ((maxn + 16 + page - 1) / page + 1) * page;
  // layout: [guard page][body][guard page]
  unsigned char* map = static_cast<unsigned char*>(
      mmap(nullptr, body + 2 * page, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0));
  if (map == MAP_FAILED) { std::perror("mmap"); return 2; }
  unsigned char* lo = map + page;
  unsigned char* hi = lo + body;
  uint64_t x = 0x9E3779B97F4A7C15ull;
  for (size_t i = 0; i < body; ++i) {
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    lo[i] = static_cast<unsigned char>(x);
  }
  if (mprotect(map, page, PROT_NONE) != 0 || mprotect(hi, page, PROT_NONE) != 0) {
    std::perror("mprotect");
    return 2;
  }

  std::vector<size_t> sizes;
  for (size_t n = 0; n <= 2200; ++n) sizes.push_back(n);
  for (size_t n = 2200; n <= maxn; n += 97) sizes.push_back(n);
  for (size_t e : {4095u, 4096u, 4097u, 8191u, 8192u, 8193u,
                   24559u, 24576u, 24577u, 24600u, 65535u, 65536u, 65537u}) {
    sizes.push_back(e);
  }
  std::vector<unsigned char> dst(maxn + 16);
  long checked = 0;
  for (size_t n : sizes) {
    // Test exact page start (`lo`), unaligned near-guard start (`lo + (n % 7) + 1`),
    // and exact page end (`hi - n`). Note `offsetof(lean_sarray_object, m_data) == 24`,
    // so `lo + 1..7` still places `m_header` and `m_size` inside the `PROT_NONE` guard page!
    const unsigned char* placements[3] = {lo, lo + (n % 7) + 1, hi - n};
    for (const unsigned char* p : placements) {
      uint32_t init = static_cast<uint32_t>(n * 2654435761u);
      uint32_t want = static_cast<uint32_t>(
          absl::ExtendCrc32c(absl::crc32c_t{init}, {reinterpret_cast<const char*>(p), n}));
      uint32_t a = leanmemcpy::ExtendCrc32c(init, p, n);
      uint32_t b = leanmemcpy::ExtendCrc32cPortable(init, p, n);
      unsigned char* d = dst.data() + (n & 7);
      uint32_t c = leanmemcpy::MemcpyCrc32c(d, p, n, init);
      bool ok = (a == want && b == want && c == want && std::memcmp(d, p, n) == 0);
      uint32_t cp = leanmemcpy::MemcpyCrc32cPortable(d, p, n, init);
      ok = ok && (cp == want && std::memcmp(d, p, n) == 0);
      if (!ok) {
        std::fprintf(stderr, "MISMATCH n=%zu\n", n);
        return 1;
      }
      ++checked;
    }
  }
  std::printf("OK: %ld guarded buffers, no fault, all agree with abseil (hardware path available: %d)\n",
              checked, leanmemcpy::HardwareAvailable());
  return 0;
}
