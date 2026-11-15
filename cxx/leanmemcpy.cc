// The C++ wrapper around the verified Lean kernels. Everything in this file
// is trusted, not proven. It does three things:
//
//  1. Initializes the Lean runtime and the Lean modules, once.
//  2. Copies with std::memcpy.
//  3. Hands caller memory to the Lean CRC entry points as a *borrowed byte
//     array without a header*: a `lean_object*` computed so that the array's
//     data pointer is the caller's pointer. The entry points
//     (MemcpyCrc32c/Impl/CApi.lean) never read the array's size or reference
//     count; scripts/check_capi.sh checks the generated C for that, and the
//     sanitizer tests would fault if they did.
#include "leanmemcpy.h"

#include <cstdlib>
#include <cstring>

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

namespace leanmemcpy {
namespace {

bool InitializeLean() {
  lean_initialize_runtime_module();
  lean_object* res = initialize_leanmemcpy_MemcpyCrc32c_Impl_CApi(1);
  if (!lean_io_result_is_ok(res)) std::abort();
  lean_dec_ref(res);
  lean_io_mark_end_initialization();
  return true;
}

// Thread-safe one-time initialization (C++11 magic static).
inline void EnsureInitialized() {
  static const bool initialized = InitializeLean();
  (void)initialized;
}

// A `lean_object*` whose byte-array data pointer is `p`. Only the data
// pointer is valid; the header in front of it is whatever memory precedes `p`
// and must never be touched.
inline lean_object* BorrowAsByteArray(const void* p) {
  return reinterpret_cast<lean_object*>(reinterpret_cast<uintptr_t>(p) -
                                        offsetof(lean_sarray_object, m_data));
}

}  // namespace

uint32_t ExtendCrc32c(uint32_t initial_crc, const void* data, size_t count) noexcept {
  if (count == 0) return initial_crc;
  EnsureInitialized();
  return lp_leanmemcpy_Crc32c_extendRaw___redArg(initial_crc, BorrowAsByteArray(data), count);
}

uint32_t ExtendCrc32cPortable(uint32_t initial_crc, const void* data, size_t count) noexcept {
  if (count == 0) return initial_crc;
  EnsureInitialized();
  return lp_leanmemcpy_Crc32c_extendPortableRaw___redArg(initial_crc, BorrowAsByteArray(data), count);
}

uint32_t MemcpyCrc32c(void* dest, const void* src, size_t count, uint32_t initial_crc) noexcept {
  if (count == 0) return initial_crc;
  std::memcpy(dest, src, count);
  return ExtendCrc32c(initial_crc, src, count);
}

uint32_t MemcpyCrc32cPortable(void* dest, const void* src, size_t count,
                              uint32_t initial_crc) noexcept {
  if (count == 0) return initial_crc;
  std::memcpy(dest, src, count);
  return ExtendCrc32cPortable(initial_crc, src, count);
}

bool HardwareAvailable() noexcept {
  EnsureInitialized();
  return lp_leanmemcpy_Crc32c_hwAvailableRaw___redArg() != 0;
}

}  // namespace leanmemcpy
