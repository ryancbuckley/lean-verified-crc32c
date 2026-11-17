// C wrapper for the Reed–Solomon library (see leanrs.h). Not proven: it checks
// arguments, pads shards shorter than 64 bytes, and dispatches to
//  - `leanrs_apply` (cxx/leanrs_apply_arm64.S), whose machine code is proven
//    in ReedSolomon/Arm64/*.lean, on AArch64 CPUs with the SHA3 extension, or
//  - the portable Lean kernel `ReedSolomon.applyPortable` otherwise.
// Tables come from the proven Lean builder `ReedSolomon.tables`.
#include "leanrs.h"

#include <lean/lean.h>
#include <pthread.h>

#include <cstdlib>
#include <cstring>

#if defined(__APPLE__)
#include <sys/sysctl.h>
#elif defined(__linux__)
#include <sys/auxv.h>
#endif

extern "C" {
void lean_initialize_runtime_module();
void lean_io_mark_end_initialization();
lean_object* initialize_leancrc32c_ReedSolomon_Impl_Kernel(uint8_t builtin);
lean_object* leanrs_tables_lean(lean_object* xs, lean_object* ys);
lean_object* leanrs_apply_portable_lean(lean_object* coef, lean_object* data, size_t k, size_t r,
                                        size_t len);
#if defined(__aarch64__)
void leanrs_apply(const uint8_t* tab, const uint8_t* const* in, uint8_t* const* out, size_t k,
                  size_t r, size_t len) noexcept;
#endif
}

namespace {

pthread_once_t g_once = PTHREAD_ONCE_INIT;
bool g_verified = false;

bool CpuHasSha3() noexcept {
  if (std::getenv("LEANRS_DISABLE_HW") != nullptr) return false;
#if defined(__aarch64__) && defined(__APPLE__)
  int v = 0;
  size_t sz = sizeof v;
  return sysctlbyname("hw.optional.armv8_2_sha3", &v, &sz, nullptr, 0) == 0 && v != 0;
#elif defined(__aarch64__) && defined(__linux__)
  return (getauxval(AT_HWCAP) & (1ul << 17) /* HWCAP_SHA3 */) != 0;
#else
  return false;
#endif
}

void DoInitialize() noexcept {
  lean_initialize_runtime_module();
  lean_object* res = initialize_leancrc32c_ReedSolomon_Impl_Kernel(1);
  if (!lean_io_result_is_ok(res)) std::abort();
  lean_dec_ref(res);
  lean_io_mark_end_initialization();
  g_verified = CpuHasSha3();
}

void EnsureInitialized() noexcept { pthread_once(&g_once, &DoInitialize); }

lean_object* MakeBytes(const uint8_t* p, size_t n) {
  lean_object* a = lean_alloc_sarray(1, n, n);
  if (n != 0) std::memcpy(lean_sarray_cptr(a), p, n);
  return a;
}

// [a, a + an) and [b, b + bn) intersect (empty ranges never do).
bool Overlap(const void* a, size_t an, const void* b, size_t bn) noexcept {
  const uintptr_t x = reinterpret_cast<uintptr_t>(a), y = reinterpret_cast<uintptr_t>(b);
  return an != 0 && bn != 0 && x < y + bn && y < x + an;
}

bool ValidRun(const uint8_t* tab, size_t k, size_t r, size_t len, const uint8_t* const* in,
              uint8_t* const* out) noexcept {
  if (k == 0 || r == 0 || k > 256 || r > 256 || len == 0 || tab == nullptr || in == nullptr ||
      out == nullptr)
    return false;
  const uintptr_t lim = UINTPTR_MAX - len;
  for (size_t i = 0; i < k; i++)
    if (in[i] == nullptr || reinterpret_cast<uintptr_t>(in[i]) > lim) return false;
  for (size_t j = 0; j < r; j++) {
    if (out[j] == nullptr || reinterpret_cast<uintptr_t>(out[j]) > lim) return false;
    if (Overlap(out[j], len, tab, 32 * k * r) || Overlap(out[j], len, in, 8 * k) ||
        Overlap(out[j], len, out, 8 * r))
      return false;
    for (size_t i = 0; i < k; i++)
      if (Overlap(out[j], len, in[i], len)) return false;
    for (size_t j2 = 0; j2 < j; j2++)
      if (Overlap(out[j], len, out[j2], len)) return false;
  }
  return true;
}

int RunPortable(const uint8_t* tab, size_t k, size_t r, size_t len, const uint8_t* const* in,
                uint8_t* const* out) {
  lean_object* coef = lean_alloc_sarray(1, k * r, k * r);
  for (size_t n = 0; n < k * r; n++)
    lean_sarray_cptr(coef)[n] = tab[32 * n + 1];  // c * 1 = c
  lean_object* data = lean_alloc_sarray(1, k * len, k * len);
  for (size_t i = 0; i < k; i++) std::memcpy(lean_sarray_cptr(data) + i * len, in[i], len);
  lean_object* res = leanrs_apply_portable_lean(coef, data, k, r, len);
  if (lean_sarray_size(res) != r * len) std::abort();
  for (size_t j = 0; j < r; j++) std::memcpy(out[j], lean_sarray_cptr(res) + j * len, len);
  lean_dec_ref(res);
  return 0;
}

}  // namespace

extern "C" size_t leanrs_table_size(size_t k, size_t r) { return 32 * k * r; }

extern "C" int leanrs_prepare(const uint8_t* xs, size_t k, const uint8_t* ys, size_t r,
                              uint8_t* tab) {
  if (k == 0 || r == 0 || k > 256 || r > 256 || xs == nullptr || ys == nullptr || tab == nullptr)
    return -1;
  bool seen[256] = {};
  for (size_t i = 0; i < k; i++) {
    if (seen[xs[i]]) return -1;
    seen[xs[i]] = true;
  }
  EnsureInitialized();
  lean_object* t = leanrs_tables_lean(MakeBytes(xs, k), MakeBytes(ys, r));
  if (lean_sarray_size(t) != 32 * k * r) std::abort();
  std::memcpy(tab, lean_sarray_cptr(t), 32 * k * r);
  lean_dec_ref(t);
  return 0;
}

extern "C" int leanrs_run_portable(const uint8_t* tab, size_t k, size_t r, size_t len,
                                   const uint8_t* const* in, uint8_t* const* out) {
  if (!ValidRun(tab, k, r, len, in, out)) return -1;
  EnsureInitialized();
  return RunPortable(tab, k, r, len, in, out);
}

extern "C" int leanrs_run(const uint8_t* tab, size_t k, size_t r, size_t len,
                          const uint8_t* const* in, uint8_t* const* out) {
  if (!ValidRun(tab, k, r, len, in, out)) return -1;
  EnsureInitialized();
#if defined(__aarch64__)
  if (g_verified) {
    if (len >= 64) {
      leanrs_apply(tab, in, out, k, r, len);
      return 0;
    }
    // Short shards: the kernel works byte position by byte position, so run it
    // on zero-padded 64-byte copies and keep the first `len` bytes.
    alignas(16) uint8_t ibuf[256][64];
    alignas(16) uint8_t obuf[256][64];
    const uint8_t* ip[256];
    uint8_t* op[256];
    for (size_t i = 0; i < k; i++) {
      std::memset(ibuf[i], 0, 64);
      std::memcpy(ibuf[i], in[i], len);
      ip[i] = ibuf[i];
    }
    for (size_t j = 0; j < r; j++) op[j] = obuf[j];
    leanrs_apply(tab, ip, op, k, r, 64);
    for (size_t j = 0; j < r; j++) std::memcpy(out[j], obuf[j], len);
    return 0;
  }
#endif
  return RunPortable(tab, k, r, len, in, out);
}

extern "C" int leanrs_has_verified_kernel(void) {
  EnsureInitialized();
  return g_verified ? 1 : 0;
}
