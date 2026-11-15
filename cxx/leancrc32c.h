/*
 * leancrc32c: verified CRC32C and fused copy-and-CRC32C, callable from C11 and C++17.
 *
 * The CRC computation is Lean code proven equal to the CRC32C polynomial
 * specification (see MemcpyCrc32c/CApi.lean, theorem `extendRaw_spec`).
 * The functions below match the contracts of their Abseil namesakes
 * (`absl::ExtendCrc32c`, `absl::ComputeCrc32c`, `absl::MemcpyCrc32c`), with
 * `uint32_t` in place of `absl::crc32c_t`.
 *
 * Preconditions (unchecked, as with Abseil and `memcpy`):
 *   - `data` / `src` point to `count` readable bytes;
 *   - `dest` points to `count` writable bytes;
 *   - for `leancrc32c_memcpy_crc32c` / `MemcpyCrc32c`, the source and
 *     destination ranges `[src, src + count)` and `[dest, dest + count)` do
 *     not overlap;
 *   - `count` fits in the address space (`count < SIZE_MAX` is always true for
 *     any valid object).
 * A null pointer (`NULL` / `nullptr`) is permitted when `count == 0`, and
 * arbitrary byte alignments (`align 1`) are permitted for all pointers.
 *
 * Thread safety: all functions are safe to call concurrently from any thread;
 * one-time Lean runtime/module initialization is synchronized internally.
 */
#ifndef LEANCRC32C_H_
#define LEANCRC32C_H_

#ifdef __cplusplus
#include <cstddef>
#include <cstdint>
#define LEANCRC32C_NOEXCEPT noexcept
extern "C" {
#else
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#define LEANCRC32C_NOEXCEPT
#endif

/* C ABI */

uint32_t leancrc32c_extend_crc32c(uint32_t initial_crc, const void* data,
                                  size_t count) LEANCRC32C_NOEXCEPT;

static inline uint32_t leancrc32c_compute_crc32c(const void* data,
                                                 size_t count) LEANCRC32C_NOEXCEPT {
  return leancrc32c_extend_crc32c(0, data, count);
}

uint32_t leancrc32c_memcpy_crc32c(void* dest, const void* src, size_t count,
                                  uint32_t initial_crc) LEANCRC32C_NOEXCEPT;

uint32_t leancrc32c_extend_crc32c_portable(uint32_t initial_crc, const void* data,
                                           size_t count) LEANCRC32C_NOEXCEPT;

uint32_t leancrc32c_memcpy_crc32c_portable(void* dest, const void* src, size_t count,
                                           uint32_t initial_crc) LEANCRC32C_NOEXCEPT;

bool leancrc32c_hardware_available(void) LEANCRC32C_NOEXCEPT;

#ifdef __cplusplus
}  // extern "C"

namespace leancrc32c {

inline uint32_t ExtendCrc32c(uint32_t initial_crc, const void* data, size_t count) noexcept {
  return leancrc32c_extend_crc32c(initial_crc, data, count);
}

inline uint32_t ComputeCrc32c(const void* data, size_t count) noexcept {
  return leancrc32c_extend_crc32c(0, data, count);
}

inline uint32_t MemcpyCrc32c(void* dest, const void* src, size_t count,
                             uint32_t initial_crc = 0) noexcept {
  return leancrc32c_memcpy_crc32c(dest, src, count, initial_crc);
}

inline uint32_t ExtendCrc32cPortable(uint32_t initial_crc, const void* data,
                                     size_t count) noexcept {
  return leancrc32c_extend_crc32c_portable(initial_crc, data, count);
}

inline uint32_t MemcpyCrc32cPortable(void* dest, const void* src, size_t count,
                                     uint32_t initial_crc = 0) noexcept {
  return leancrc32c_memcpy_crc32c_portable(dest, src, count, initial_crc);
}

inline bool HardwareAvailable() noexcept {
  return leancrc32c_hardware_available();
}

}  // namespace leancrc32c
#endif  // __cplusplus

#undef LEANCRC32C_NOEXCEPT

#endif  // LEANCRC32C_H_
