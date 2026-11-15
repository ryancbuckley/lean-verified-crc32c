// The C/C++ wrapper around the verified Lean kernels. Everything in this file
// is trusted, not proven. It does three things:
//
//  1. Initializes the Lean runtime and the Lean modules, once.
//  2. Copies with std::memcpy when `count > 0`.
//  3. Hands caller memory to the Lean CRC entry points as a *borrowed byte
//     array without a header*: a `lean_object*` computed via unsigned
//     `uintptr_t` arithmetic so that `SIMDMODELS_SARRAY_BYTES(a)` recovers the
//     caller's exact pointer `p` at 1-byte alignment. The entry points
//     (MemcpyCrc32c/Impl/CApi.lean) never read `m_header` or `m_size`, never
//     touch reference counts, and never dereference a `lean_sarray_object*`;
//     scripts/check_capi.sh checks the transitive C call graph and tests this
//     under guard pages, debug assertions, and ASan/UBSan.
#include "leanmemcpy.h"

#include <atomic>
#include <cstdlib>
#include <cstring>
#include <pthread.h>

#include <lean/lean.h>

extern "C" {
void lean_initialize_runtime_module();
void lean_io_mark_end_initialization();
lean_object* initialize_leanmemcpy_MemcpyCrc32c_Impl_CApi(uint8_t builtin);
// Compiled Lean functions, called by symbol name because Lean cannot
// `@[export]` a function with a borrowed parameter.
uint32_t lp_leanmemcpy_Crc32c_extendRaw___redArg(uint32_t c, lean_object* a, size_t len);
uint32_t lp_leanmemcpy_Crc32c_extendPortableRaw___redArg(uint32_t c, lean_object* a, size_t len);
uint8_t lp_leanmemcpy_Crc32c_hwAvailableRaw___redArg();
}

namespace {

// Constant-initialized flag so calls after startup pay only an acquire byte
// load, while calls from another TU's static constructor still synchronize
// safely via EnsureInitializedSlow().
std::atomic<bool> g_ready{false};
pthread_once_t g_once = PTHREAD_ONCE_INIT;

void DoInitialize() noexcept {
  lean_initialize_runtime_module();
  lean_object* res = initialize_leanmemcpy_MemcpyCrc32c_Impl_CApi(1);
  if (!lean_io_result_is_ok(res)) std::abort();
  lean_dec_ref(res);
  lean_io_mark_end_initialization();
  g_ready.store(true, std::memory_order_release);
}

#if defined(__GNUC__) || defined(__clang__)
__attribute__((noinline))
#endif
void EnsureInitializedSlow() noexcept {
  pthread_once(&g_once, &DoInitialize);
}

inline void EnsureInitialized() noexcept {
  if (__builtin_expect(!g_ready.load(std::memory_order_acquire), 0)) {
    EnsureInitializedSlow();
  }
}

#if defined(__GNUC__) || defined(__clang__)
__attribute__((constructor)) void EagerInit() noexcept { EnsureInitializedSlow(); }
#else
const bool g_eager_init = (EnsureInitializedSlow(), true);
#endif

// A `lean_object*` whose byte-array payload address (`+ offsetof(..., m_data)`
// in unsigned `uintptr_t` arithmetic) equals `p`. Only `[p, p + count)` is
// valid; the header region in front of `p` must never be touched.
inline lean_object* BorrowAsByteArray(const void* p) noexcept {
  return reinterpret_cast<lean_object*>(reinterpret_cast<uintptr_t>(p) -
                                        offsetof(lean_sarray_object, m_data));
}

}  // namespace

extern "C" {

uint32_t leanmemcpy_extend_crc32c(uint32_t initial_crc, const void* data, size_t count) noexcept {
  if (count == 0) return initial_crc;
  EnsureInitialized();
  return lp_leanmemcpy_Crc32c_extendRaw___redArg(initial_crc, BorrowAsByteArray(data), count);
}

uint32_t leanmemcpy_extend_crc32c_portable(uint32_t initial_crc, const void* data,
                                           size_t count) noexcept {
  if (count == 0) return initial_crc;
  EnsureInitialized();
  return lp_leanmemcpy_Crc32c_extendPortableRaw___redArg(
      initial_crc, BorrowAsByteArray(data), count);
}

uint32_t leanmemcpy_memcpy_crc32c(void* dest, const void* src, size_t count,
                                  uint32_t initial_crc) noexcept {
  if (count == 0) return initial_crc;
  EnsureInitialized();
  std::memcpy(dest, src, count);
  return lp_leanmemcpy_Crc32c_extendRaw___redArg(initial_crc, BorrowAsByteArray(src), count);
}

uint32_t leanmemcpy_memcpy_crc32c_portable(void* dest, const void* src, size_t count,
                                           uint32_t initial_crc) noexcept {
  if (count == 0) return initial_crc;
  EnsureInitialized();
  std::memcpy(dest, src, count);
  return lp_leanmemcpy_Crc32c_extendPortableRaw___redArg(
      initial_crc, BorrowAsByteArray(src), count);
}

bool leanmemcpy_hardware_available(void) noexcept {
  EnsureInitialized();
  return lp_leanmemcpy_Crc32c_hwAvailableRaw___redArg() != 0;
}

}  // extern "C"
