// Guard-page test of the wrapper's trust assumption. The verified kernels are
// handed caller memory as a byte array with no header, so they must never
// read in front of the data pointer, and never past the end of the data.
//
// Each buffer is placed twice: starting exactly at the beginning of a mapping
// whose preceding page is inaccessible, and ending exactly at an inaccessible
// page. Any read of the header or beyond the data faults (SIGSEGV/SIGBUS).
// Results are also compared with abseil.
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
  const size_t page = static_cast<size_t>(sysconf(_SC_PAGESIZE));
  const size_t maxn = 80000;
  const size_t body = ((maxn + page - 1) / page + 1) * page;
  // layout: [guard page][body][guard page]
  unsigned char* map = static_cast<unsigned char*>(
      mmap(nullptr, body + 2 * page, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0));
  if (map == MAP_FAILED) { std::perror("mmap"); return 2; }
  unsigned char* lo = map + page;
  unsigned char* hi = lo + body;
  uint64_t x = 0x9E3779B97F4A7C15ull;
  for (size_t i = 0; i < body; ++i) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; lo[i] = static_cast<unsigned char>(x); }
  if (mprotect(map, page, PROT_NONE) != 0 || mprotect(hi, page, PROT_NONE) != 0) { std::perror("mprotect"); return 2; }

  std::vector<size_t> sizes;
  for (size_t n = 0; n <= 2200; ++n) sizes.push_back(n);
  for (size_t n = 2200; n <= maxn; n += 97) sizes.push_back(n);
  for (size_t e : {4095u, 4096u, 4097u, 8191u, 8192u, 8193u, 24559u, 24576u, 24577u, 24600u, 65535u, 65536u, 65537u})
    sizes.push_back(e);
  std::vector<unsigned char> dst(maxn + 1);
  long checked = 0;
  for (size_t n : sizes) {
    const unsigned char* placements[2] = {lo, hi - n};  // start-guarded, end-guarded
    for (const unsigned char* p : placements) {
      uint32_t init = static_cast<uint32_t>(n * 2654435761u);
      uint32_t want = static_cast<uint32_t>(
          absl::ExtendCrc32c(absl::crc32c_t{init}, {reinterpret_cast<const char*>(p), n}));
      uint32_t a = leanmemcpy::ExtendCrc32c(init, p, n);
      uint32_t b = leanmemcpy::ExtendCrc32cPortable(init, p, n);
      uint32_t c = leanmemcpy::MemcpyCrc32c(dst.data(), p, n, init);
      if (a != want || b != want || c != want || std::memcmp(dst.data(), p, n) != 0) {
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
