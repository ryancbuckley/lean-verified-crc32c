// leanmemcpy: verified CRC32C and fused copy-and-CRC32C, callable from C++.
//
// The CRC computation is Lean code proven equal to the CRC32C specification
// (see MemcpyCrc32c/CApi.lean, theorem `extendRaw_spec`). The functions below
// have the same contracts as their abseil namesakes, with `uint32_t` in place
// of `absl::crc32c_t`.
//
// Preconditions (not checked, as with abseil and memcpy):
//   - `data` / `src` point to `count` readable bytes;
//   - `dest` points to `count` writable bytes;
//   - for MemcpyCrc32c, the source and destination ranges do not overlap.
// A null pointer is allowed only when `count` is zero.
//
// Thread safety: all functions may be called concurrently from any thread.
#ifndef LEANMEMCPY_H_
#define LEANMEMCPY_H_

#include <cstddef>
#include <cstdint>

namespace leanmemcpy {

// absl::ExtendCrc32c: the CRC32C of (the data `initial_crc` covers) + `data`.
uint32_t ExtendCrc32c(uint32_t initial_crc, const void* data, size_t count) noexcept;

// absl::ComputeCrc32c.
inline uint32_t ComputeCrc32c(const void* data, size_t count) noexcept {
  return ExtendCrc32c(0, data, count);
}

// absl::MemcpyCrc32c: copies `count` bytes from `src` to `dest` with memcpy()
// semantics and returns ExtendCrc32c(initial_crc, src, count).
uint32_t MemcpyCrc32c(void* dest, const void* src, size_t count,
                      uint32_t initial_crc = 0) noexcept;

// The same, always on the portable path (no CRC or carry-less-multiply
// instructions). For tests and benchmarks.
uint32_t ExtendCrc32cPortable(uint32_t initial_crc, const void* data, size_t count) noexcept;
uint32_t MemcpyCrc32cPortable(void* dest, const void* src, size_t count,
                              uint32_t initial_crc = 0) noexcept;

// Whether the dispatched functions use the hardware path on this CPU.
bool HardwareAvailable() noexcept;

}  // namespace leanmemcpy

#endif  // LEANMEMCPY_H_
