// The C/C++ wrapper around the verified Lean kernels. Everything in this file
// is trusted, not proven. It does three things:
//
//  1. Initializes the Lean runtime and the Lean modules once, caching the
//     hardware-dispatch state (`kStateHw` vs `kStatePortable`) in a single
//     atomic byte so post-startup calls pay one acquire byte load and branch
//     directly to the verified hardware or portable entry point.
//  2. Copies `[src, src + count)` to `dest` when `count > 0` (for
//     `count <= 64`, computes the verified CRC on `src` first and then copies
//     via overlapping fixed-width scalar loads/stores, avoiding both the
//     dynamic `_memcpy` stub and 4 KiB store-to-load virtual-offset aliasing;
//     for `count > 64`, uses `std::memcpy` in an outlined helper).
//  3. Hands caller memory to the Lean CRC entry points as a *borrowed byte
//     array without a header*: a `lean_object*` computed via unsigned
//     `uintptr_t` arithmetic so that `SIMDMODELS_SARRAY_BYTES(a)` recovers the
//     caller's exact pointer `p` at 1-byte alignment. The entry points
//     (MemcpyCrc32c/Impl/CApi.lean and MemcpyCrc32c/Impl/Hw.lean) never read
//     `m_header` or `m_size`, never touch reference counts, and never
//     dereference a `lean_sarray_object*`; scripts/check_capi.sh checks the
//     transitive C call graph and tests this under guard pages, debug
//     assertions, and ASan/UBSan.
#include "leancrc32c.h"

#include <atomic>
#include <cstdlib>
#include <cstring>
#include <pthread.h>

#include <lean/lean.h>

#if defined(__GNUC__) || defined(__clang__)
#define LEANCRC32C_NOINLINE __attribute__((noinline))
#else
#define LEANCRC32C_NOINLINE
#endif

extern "C" {
void lean_initialize_runtime_module();
void lean_io_mark_end_initialization();
lean_object* initialize_leancrc32c_MemcpyCrc32c_Impl_CApi(uint8_t builtin);
// Compiled Lean functions, called by symbol name because Lean cannot
// `@[export]` a function with a borrowed parameter.
uint32_t lp_leancrc32c_Crc32c_extendRaw___redArg(uint32_t c, lean_object* a, size_t len);
uint32_t lp_leancrc32c_Crc32c_extendHwRaw___redArg(uint32_t c, lean_object* a, size_t len);
uint32_t lp_leancrc32c_Crc32c_extendPortableRaw___redArg(uint32_t c, lean_object* a, size_t len);
uint8_t lp_leancrc32c_Crc32c_hwAvailableRaw___redArg();
}

namespace {

constexpr uint8_t kStateUninitialized = 0;
constexpr uint8_t kStateHw = 1;
constexpr uint8_t kStatePortable = 2;

// Constant-initialized dispatch state so calls after startup pay only a single
// acquire byte load, while calls from another TU's static constructor still
// synchronize safely via EnsureInitializedSlow().
std::atomic<uint8_t> g_state{kStateUninitialized};
pthread_once_t g_once = PTHREAD_ONCE_INIT;

void DoInitialize() noexcept {
  lean_initialize_runtime_module();
  lean_object* res = initialize_leancrc32c_MemcpyCrc32c_Impl_CApi(1);
  if (!lean_io_result_is_ok(res)) std::abort();
  lean_dec_ref(res);
  lean_io_mark_end_initialization();
  const uint8_t hw = lp_leancrc32c_Crc32c_hwAvailableRaw___redArg();
  g_state.store(hw ? kStateHw : kStatePortable, std::memory_order_release);
}

LEANCRC32C_NOINLINE uint8_t EnsureInitializedSlow() noexcept {
  pthread_once(&g_once, &DoInitialize);
  return g_state.load(std::memory_order_acquire);
}

#if defined(__GNUC__) || defined(__clang__)
__attribute__((constructor)) void EagerInit() noexcept { EnsureInitializedSlow(); }
#else
const uint8_t g_eager_init = EnsureInitializedSlow();
#endif

// A `lean_object*` whose byte-array payload address (`+ offsetof(..., m_data)`
// in unsigned `uintptr_t` arithmetic) equals `p`. Only `[p, p + count)` is
// valid; the header region in front of `p` must never be touched.
inline lean_object* BorrowAsByteArray(const void* p) noexcept {
  return reinterpret_cast<lean_object*>(reinterpret_cast<uintptr_t>(p) -
                                        offsetof(lean_sarray_object, m_data));
}

inline uint64_t Load64(const uint8_t* p) noexcept {
  uint64_t v;
  std::memcpy(&v, p, 8);
  return v;
}

inline void Store64(uint8_t* p, uint64_t v) noexcept {
  std::memcpy(p, &v, 8);
}

// Copies `1 <= n <= 64` bytes from `src` to `dest` using overlapping
// fixed-width scalar `std::memcpy` loads before stores. Every access stays
// strictly within `[0, n)` at 1-byte alignment (safe next to PROT_NONE guard
// pages and under ASan/UBSan), avoids local `char[]` arrays that would trigger
// `-fstack-protector`, and avoids jumping through the dynamic `_memcpy` stub.
inline void CopyUpTo64(void* dest, const void* src, size_t n) noexcept {
  auto* d = static_cast<uint8_t*>(dest);
  const auto* s = static_cast<const uint8_t*>(src);
  if (n >= 16) {
    const uint64_t l0 = Load64(s);
    const uint64_t l1 = Load64(s + 8);
    if (n == 16) {
      Store64(d, l0);
      Store64(d + 8, l1);
      return;
    }
    if (n <= 32) {
      const uint64_t h0 = Load64(s + n - 16);
      const uint64_t h1 = Load64(s + n - 8);
      Store64(d, l0);
      Store64(d + 8, l1);
      Store64(d + n - 16, h0);
      Store64(d + n - 8, h1);
      return;
    }
    const uint64_t l2 = Load64(s + 16);
    const uint64_t l3 = Load64(s + 24);
    const uint64_t h0 = Load64(s + n - 32);
    const uint64_t h1 = Load64(s + n - 24);
    const uint64_t h2 = Load64(s + n - 16);
    const uint64_t h3 = Load64(s + n - 8);
    Store64(d, l0);
    Store64(d + 8, l1);
    Store64(d + 16, l2);
    Store64(d + 24, l3);
    Store64(d + n - 32, h0);
    Store64(d + n - 24, h1);
    Store64(d + n - 16, h2);
    Store64(d + n - 8, h3);
    return;
  }
  if (n >= 8) {
    const uint64_t lo = Load64(s);
    const uint64_t hi = Load64(s + n - 8);
    Store64(d, lo);
    Store64(d + n - 8, hi);
    return;
  }
  if (n >= 4) {
    uint32_t lo, hi;
    std::memcpy(&lo, s, 4);
    std::memcpy(&hi, s + n - 4, 4);
    std::memcpy(d, &lo, 4);
    std::memcpy(d + n - 4, &hi, 4);
    return;
  }
  const uint8_t b0 = s[0];
  const uint8_t b1 = s[n >> 1];
  const uint8_t b2 = s[n - 1];
  d[0] = b0;
  d[n >> 1] = b1;
  d[n - 1] = b2;
}

LEANCRC32C_NOINLINE uint32_t ExtendCrc32cInit(uint32_t initial_crc, const void* data,
                                              size_t count) noexcept {
  const uint8_t s = EnsureInitializedSlow();
  if (s == kStateHw) {
    return lp_leancrc32c_Crc32c_extendHwRaw___redArg(
        initial_crc, BorrowAsByteArray(data), count);
  }
  return lp_leancrc32c_Crc32c_extendPortableRaw___redArg(
      initial_crc, BorrowAsByteArray(data), count);
}

LEANCRC32C_NOINLINE uint32_t ExtendCrc32cPortableInit(uint32_t initial_crc, const void* data,
                                                      size_t count) noexcept {
  EnsureInitializedSlow();
  return lp_leancrc32c_Crc32c_extendPortableRaw___redArg(
      initial_crc, BorrowAsByteArray(data), count);
}

LEANCRC32C_NOINLINE uint32_t MemcpyCrc32cLarge(void* dest, const void* src, size_t count,
                                               uint32_t initial_crc, uint8_t state) noexcept {
  std::memcpy(dest, src, count);
  if (__builtin_expect(state == kStateHw, 1)) {
    return lp_leancrc32c_Crc32c_extendHwRaw___redArg(
        initial_crc, BorrowAsByteArray(src), count);
  }
  return lp_leancrc32c_Crc32c_extendPortableRaw___redArg(
      initial_crc, BorrowAsByteArray(src), count);
}

LEANCRC32C_NOINLINE uint32_t MemcpyCrc32cInit(void* dest, const void* src, size_t count,
                                              uint32_t initial_crc) noexcept {
  const uint8_t s = EnsureInitializedSlow();
  if (count <= 64) {
    const uint32_t crc =
        (s == kStateHw)
            ? lp_leancrc32c_Crc32c_extendHwRaw___redArg(
                  initial_crc, BorrowAsByteArray(src), count)
            : lp_leancrc32c_Crc32c_extendPortableRaw___redArg(
                  initial_crc, BorrowAsByteArray(src), count);
    CopyUpTo64(dest, src, count);
    return crc;
  }
  return MemcpyCrc32cLarge(dest, src, count, initial_crc, s);
}

LEANCRC32C_NOINLINE uint32_t MemcpyCrc32cPortableLarge(void* dest, const void* src, size_t count,
                                                       uint32_t initial_crc) noexcept {
  std::memcpy(dest, src, count);
  return lp_leancrc32c_Crc32c_extendPortableRaw___redArg(
      initial_crc, BorrowAsByteArray(src), count);
}

LEANCRC32C_NOINLINE uint32_t MemcpyCrc32cPortableInit(void* dest, const void* src, size_t count,
                                                      uint32_t initial_crc) noexcept {
  EnsureInitializedSlow();
  if (count <= 64) {
    const uint32_t crc = lp_leancrc32c_Crc32c_extendPortableRaw___redArg(
        initial_crc, BorrowAsByteArray(src), count);
    CopyUpTo64(dest, src, count);
    return crc;
  }
  return MemcpyCrc32cPortableLarge(dest, src, count, initial_crc);
}

}  // namespace

extern "C" {

uint32_t leancrc32c_extend_crc32c(uint32_t initial_crc, const void* data, size_t count) noexcept {
  if (count == 0) return initial_crc;
  const uint8_t s = g_state.load(std::memory_order_acquire);
  if (__builtin_expect(s == kStateHw, 1)) {
    return lp_leancrc32c_Crc32c_extendHwRaw___redArg(
        initial_crc, BorrowAsByteArray(data), count);
  }
  if (__builtin_expect(s == kStateUninitialized, 0)) {
    return ExtendCrc32cInit(initial_crc, data, count);
  }
  return lp_leancrc32c_Crc32c_extendPortableRaw___redArg(
      initial_crc, BorrowAsByteArray(data), count);
}

uint32_t leancrc32c_extend_crc32c_portable(uint32_t initial_crc, const void* data,
                                           size_t count) noexcept {
  if (count == 0) return initial_crc;
  if (__builtin_expect(g_state.load(std::memory_order_acquire) == kStateUninitialized, 0)) {
    return ExtendCrc32cPortableInit(initial_crc, data, count);
  }
  return lp_leancrc32c_Crc32c_extendPortableRaw___redArg(
      initial_crc, BorrowAsByteArray(data), count);
}

uint32_t leancrc32c_memcpy_crc32c(void* dest, const void* src, size_t count,
                                  uint32_t initial_crc) noexcept {
  if (count == 0) return initial_crc;
  const uint8_t s = g_state.load(std::memory_order_acquire);
  if (__builtin_expect(s == kStateUninitialized, 0)) {
    return MemcpyCrc32cInit(dest, src, count, initial_crc);
  }
  if (count > 64) {
    return MemcpyCrc32cLarge(dest, src, count, initial_crc, s);
  }
  const uint32_t crc =
      (__builtin_expect(s == kStateHw, 1))
          ? lp_leancrc32c_Crc32c_extendHwRaw___redArg(
                initial_crc, BorrowAsByteArray(src), count)
          : lp_leancrc32c_Crc32c_extendPortableRaw___redArg(
                initial_crc, BorrowAsByteArray(src), count);
  CopyUpTo64(dest, src, count);
  return crc;
}

uint32_t leancrc32c_memcpy_crc32c_portable(void* dest, const void* src, size_t count,
                                           uint32_t initial_crc) noexcept {
  if (count == 0) return initial_crc;
  if (__builtin_expect(g_state.load(std::memory_order_acquire) == kStateUninitialized, 0)) {
    return MemcpyCrc32cPortableInit(dest, src, count, initial_crc);
  }
  if (count > 64) {
    return MemcpyCrc32cPortableLarge(dest, src, count, initial_crc);
  }
  const uint32_t crc = lp_leancrc32c_Crc32c_extendPortableRaw___redArg(
      initial_crc, BorrowAsByteArray(src), count);
  CopyUpTo64(dest, src, count);
  return crc;
}

bool leancrc32c_hardware_available(void) noexcept {
  uint8_t s = g_state.load(std::memory_order_acquire);
  if (__builtin_expect(s == kStateUninitialized, 0)) {
    s = EnsureInitializedSlow();
  }
  return s == kStateHw;
}

}  // extern "C"
