// Full Phase 6 benchmarking harness implementing the brief's protocol:
//   - All 7 required copy+CRC / baseline contenders + CRC-only kernels,
//     measured in the same process on identical randomized buffers.
//   - Sizes: 16 B, 64 B, 256 B, 1 KiB, 4 KiB, 64 KiB, 1 MiB, 64 MiB.
//   - Thread pinning: QOS_CLASS_USER_INTERACTIVE on macOS (P-core cluster);
//     sched_setaffinity to one core on Linux.
//   - Alignment regimes:
//       1. aligned        (src+0, dst+0)
//       2. unaligned_same (src+k, dst+k cycling k in 1..7)
//       3. unaligned_skew (src+3, dst+7; cross-misaligned)
//   - Cache regimes:
//       * warm cache across all 8 sizes (15 interleaved rounds)
//       * cold cache (64 MiB eviction sweep before every single call) at
//         64 KiB, 1 MiB, and 64 MiB (15 interleaved rounds)
//   - Outputs:
//       * human-readable tables (median GB/s, IQR, ns/call, ratios to Abseil
//         and plain memcpy) on stdout
//       * raw per-trial CSV and summary CSV to paths given on argv.

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#if defined(__APPLE__)
#include <pthread.h>
#include <pthread/qos.h>
#include <sys/sysctl.h>
#elif defined(__linux__)
#include <pthread.h>
#include <sched.h>
#endif

#include "absl/crc/crc32c.h"
#include "absl/strings/string_view.h"
#include "leanmemcpy.h"

namespace {

// Portable C slicing-by-8 CRC32C baseline (pre-Chorba non-SIMD state of the art).
constexpr uint32_t kCastagnoliPoly = 0x82F63B78u;
uint32_t g_slice8_table[8][256];

void InitSlice8Tables() {
  for (uint32_t i = 0; i < 256; ++i) {
    uint32_t c = i;
    for (int k = 0; k < 8; ++k) {
      c = (c >> 1) ^ ((c & 1u) ? kCastagnoliPoly : 0u);
    }
    g_slice8_table[0][i] = c;
  }
  for (uint32_t i = 0; i < 256; ++i) {
    for (int t = 1; t < 8; ++t) {
      g_slice8_table[t][i] =
          (g_slice8_table[t - 1][i] >> 8) ^ g_slice8_table[0][g_slice8_table[t - 1][i] & 0xFFu];
    }
  }
}

inline uint32_t Crc32cSlice8Extend(uint32_t init_crc, const void* data, size_t n) {
  const uint8_t* p = static_cast<const uint8_t*>(data);
  uint32_t s = ~init_crc;
  while (n >= 8) {
    uint64_t w;
    std::memcpy(&w, p, 8);
    w ^= static_cast<uint64_t>(s);
    s = g_slice8_table[7][w & 0xFFu] ^
        g_slice8_table[6][(w >> 8) & 0xFFu] ^
        g_slice8_table[5][(w >> 16) & 0xFFu] ^
        g_slice8_table[4][(w >> 24) & 0xFFu] ^
        g_slice8_table[3][(w >> 32) & 0xFFu] ^
        g_slice8_table[2][(w >> 40) & 0xFFu] ^
        g_slice8_table[1][(w >> 48) & 0xFFu] ^
        g_slice8_table[0][(w >> 56) & 0xFFu];
    p += 8;
    n -= 8;
  }
  while (n > 0) {
    s = (s >> 8) ^ g_slice8_table[0][(s ^ *p++) & 0xFFu];
    --n;
  }
  return ~s;
}

inline uint32_t Crc32cSlice8Memcpy(void* dst, const void* src, size_t n, uint32_t init_crc) {
  if (n > 0) std::memcpy(dst, src, n);
  return Crc32cSlice8Extend(init_crc, src, n);
}

std::string PinCurrentThread() {
#if defined(__APPLE__)
  int rc = pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
  char brand[128] = {0};
  size_t len = sizeof(brand) - 1;
  sysctlbyname("machdep.cpu.brand_string", brand, &len, nullptr, 0);
  return std::string("macOS QOS_CLASS_USER_INTERACTIVE (rc=") + std::to_string(rc) +
         ", CPU=" + (brand[0] ? brand : "Apple Silicon") + ")";
#elif defined(__linux__)
  int cpu = 0;
  if (const char* env = std::getenv("BENCH_CPU")) cpu = std::atoi(env);
  cpu_set_t set;
  CPU_ZERO(&set);
  CPU_SET(cpu, &set);
  int rc = sched_setaffinity(0, sizeof(set), &set);
  return std::string("Linux sched_setaffinity(cpu=") + std::to_string(cpu) +
         ", rc=" + std::to_string(rc) + ")";
#else
  return "unpinned (unsupported OS)";
#endif
}

enum class ContenderId {
  kAbslMemcpy = 0,
  kMemcpyPlusAbslCompute,
  kPlainMemcpy,
  kCSlice8PlusMemcpy,
  kLeanMemcpyPortable,
  kLeanMemcpyDispatched,
  kAbslExtend,
  kCSlice8Extend,
  kLeanExtendPortable,
  kLeanExtendDispatched,
};

struct Contender {
  ContenderId id;
  const char* slug;
  const char* label;
  bool is_copy;
};

constexpr Contender kContenders[] = {
    {ContenderId::kAbslMemcpy, "absl_memcpy_crc32c", "absl::MemcpyCrc32c", true},
    {ContenderId::kMemcpyPlusAbslCompute, "memcpy_plus_absl_compute",
     "memcpy + absl::ComputeCrc32c", true},
    {ContenderId::kPlainMemcpy, "plain_memcpy", "Plain memcpy", true},
    {ContenderId::kCSlice8PlusMemcpy, "c_slice8_plus_memcpy",
     "C slicing-by-8 + memcpy", true},
    {ContenderId::kLeanMemcpyPortable, "lean_memcpy_portable",
     "Verified Lean portable (MemcpyCrc32cPortable)", true},
    {ContenderId::kLeanMemcpyDispatched, "lean_memcpy_dispatched",
     "Verified Lean dispatched (MemcpyCrc32c)", true},
    {ContenderId::kAbslExtend, "absl_extend_crc32c", "absl::ExtendCrc32c (CRC-only)", false},
    {ContenderId::kCSlice8Extend, "c_slice8_extend", "C slicing-by-8 (CRC-only)", false},
    {ContenderId::kLeanExtendPortable, "lean_extend_portable",
     "Verified Lean portable (ExtendCrc32cPortable)", false},
    {ContenderId::kLeanExtendDispatched, "lean_extend_dispatched",
     "Verified Lean dispatched (ExtendCrc32c)", false},
};

constexpr size_t kNumContenders = sizeof(kContenders) / sizeof(kContenders[0]);
constexpr size_t kSizes[] = {16, 64, 256, 1024, 4096, 65536, 1u << 20, 64u << 20};
constexpr int kTrials = 15;

inline uint32_t RunOne(ContenderId id, uint8_t* dst, const uint8_t* src, size_t n, uint32_t init) {
  asm volatile("" : "+r"(dst), "+r"(src) : : "memory");
  uint32_t out = init;
  switch (id) {
    case ContenderId::kAbslMemcpy:
      out = static_cast<uint32_t>(
          absl::MemcpyCrc32c(dst, src, n, absl::crc32c_t{init}));
      break;
    case ContenderId::kMemcpyPlusAbslCompute:
      std::memcpy(dst, src, n);
      asm volatile("" : : "r"(dst) : "memory");
      out = static_cast<uint32_t>(
          absl::ExtendCrc32c(absl::crc32c_t{init},
                             absl::string_view(reinterpret_cast<const char*>(src), n)));
      break;
    case ContenderId::kPlainMemcpy:
      std::memcpy(dst, src, n);
      out = init ^ dst[n >> 1];
      break;
    case ContenderId::kCSlice8PlusMemcpy:
      out = Crc32cSlice8Memcpy(dst, src, n, init);
      break;
    case ContenderId::kLeanMemcpyPortable:
      out = leanmemcpy::MemcpyCrc32cPortable(dst, src, n, init);
      break;
    case ContenderId::kLeanMemcpyDispatched:
      out = leanmemcpy::MemcpyCrc32c(dst, src, n, init);
      break;
    case ContenderId::kAbslExtend:
      out = static_cast<uint32_t>(
          absl::ExtendCrc32c(absl::crc32c_t{init},
                             absl::string_view(reinterpret_cast<const char*>(src), n)));
      break;
    case ContenderId::kCSlice8Extend:
      out = Crc32cSlice8Extend(init, src, n);
      break;
    case ContenderId::kLeanExtendPortable:
      out = leanmemcpy::ExtendCrc32cPortable(init, src, n);
      break;
    case ContenderId::kLeanExtendDispatched:
      out = leanmemcpy::ExtendCrc32c(init, src, n);
      break;
  }
  asm volatile("" : "+r"(out) : : "memory");
  return out;
}

struct Stats {
  double median_gbps;
  double p25_gbps;
  double p75_gbps;
  double iqr_gbps;
  double min_gbps;
  double max_gbps;
  double median_ns;
};

Stats ComputeStats(std::vector<double> sec_per_call, size_t n) {
  std::sort(sec_per_call.begin(), sec_per_call.end());
  const size_t m = sec_per_call.size();
  // Faster time = higher GB/s: median time is index m/2; P25 GB/s corresponds
  // to index 3*m/4 (slower quartile) and P75 GB/s to index m/4 (faster quartile).
  const double med_s = sec_per_call[m / 2];
  const double slow_q_s = sec_per_call[(3 * m) / 4];
  const double fast_q_s = sec_per_call[m / 4];
  const double min_s = sec_per_call.front();
  const double max_s = sec_per_call.back();
  Stats st{};
  st.median_gbps = static_cast<double>(n) / med_s / 1e9;
  st.p25_gbps = static_cast<double>(n) / slow_q_s / 1e9;
  st.p75_gbps = static_cast<double>(n) / fast_q_s / 1e9;
  st.iqr_gbps = st.p75_gbps - st.p25_gbps;
  st.min_gbps = static_cast<double>(n) / max_s / 1e9;
  st.max_gbps = static_cast<double>(n) / min_s / 1e9;
  st.median_ns = med_s * 1e9;
  return st;
}

void FlushCaches(uint8_t* evict, size_t evict_len, uint64_t salt) {
  uint64_t acc = salt;
  for (size_t i = 0; i < evict_len; i += 64) {
    evict[i] = static_cast<uint8_t>(evict[i] + 1u);
    acc ^= evict[i];
  }
  asm volatile("" : "+r"(acc) : : "memory");
}

size_t RepsForSize(size_t n, bool cold_cache) {
  if (cold_cache) return 1;
  if (n <= 64) return 100000;
  if (n <= 1024) return 40000;
  if (n <= 4096) return 15000;
  if (n <= 65536) return 1500;
  if (n <= (1u << 20)) return 96;
  return 2;  // 64 MiB: 2 reps * 15 trials = 30 calls (~1.9 GiB per contender)
}

const char* HumanSize(size_t n) {
  switch (n) {
    case 16: return "16 B";
    case 64: return "64 B";
    case 256: return "256 B";
    case 1024: return "1 KiB";
    case 4096: return "4 KiB";
    case 65536: return "64 KiB";
    case 1048576: return "1 MiB";
    case 67108864: return "64 MiB";
    default: return "?";
  }
}

}  // namespace

int main(int argc, char** argv) {
  const char* raw_csv_path = argc > 1 ? argv[1] : "reports/bench_apple_m4_raw.csv";
  const char* sum_csv_path = argc > 2 ? argv[2] : "reports/bench_apple_m4_summary.csv";

  InitSlice8Tables();
  const std::string pin_desc = PinCurrentThread();
  const bool hw_avail = leanmemcpy::HardwareAvailable();

  std::printf("# leanmemcpy Phase 6 Benchmark Suite\n");
  std::printf("# Thread pinning: %s\n", pin_desc.c_str());
  std::printf("# leanmemcpy::HardwareAvailable(): %s\n\n", hw_avail ? "true" : "false");

  constexpr size_t kMaxSize = 64u << 20;
  constexpr size_t kEvictSize = 64u << 20;
  void* raw_src = nullptr;
  void* raw_dst = nullptr;
  void* raw_evict = nullptr;
  if (posix_memalign(&raw_src, 64, kMaxSize + 64) != 0 ||
      posix_memalign(&raw_dst, 64, kMaxSize + 64) != 0 ||
      posix_memalign(&raw_evict, 64, kEvictSize) != 0) {
    std::fprintf(stderr, "posix_memalign failed\n");
    return 1;
  }
  uint8_t* sbase = static_cast<uint8_t*>(raw_src);
  uint8_t* dbase = static_cast<uint8_t*>(raw_dst);
  uint8_t* evict = static_cast<uint8_t*>(raw_evict);

  uint64_t rng = 0x2545F4914F6CDD1Dull;
  for (size_t i = 0; i < kMaxSize + 64; i += 8) {
    rng ^= rng << 13;
    rng ^= rng >> 7;
    rng ^= rng << 17;
    std::memcpy(sbase + i, &rng, 8);
    uint64_t z = ~rng;
    std::memcpy(dbase + i, &z, 8);
  }
  std::memset(evict, 0x5A, kEvictSize);

  // Self-check every CRC contender on all 8 sizes + unaligned offsets before timing.
  for (size_t n : kSizes) {
    for (size_t off = 0; off < 8; ++off) {
      const uint32_t ref = static_cast<uint32_t>(
          absl::ComputeCrc32c({reinterpret_cast<const char*>(sbase + off), n}));
      if (Crc32cSlice8Extend(0, sbase + off, n) != ref ||
          leanmemcpy::ExtendCrc32cPortable(0, sbase + off, n) != ref ||
          leanmemcpy::ExtendCrc32c(0, sbase + off, n) != ref ||
          leanmemcpy::MemcpyCrc32cPortable(dbase + off, sbase + off, n, 0) != ref ||
          leanmemcpy::MemcpyCrc32c(dbase + ((off + 3) & 7), sbase + off, n, 0) != ref) {
        std::fprintf(stderr, "CRC mismatch in pre-benchmark self-check at n=%zu off=%zu\n", n, off);
        return 1;
      }
    }
  }

  // ~80 ms P-core ramp-up before timed measurements.
  volatile uint32_t warm_sink = 0;
  for (int i = 0; i < 4000; ++i) {
    warm_sink ^= leanmemcpy::ExtendCrc32c(0, sbase, 65536);
  }

  FILE* raw_fp = std::fopen(raw_csv_path, "w");
  FILE* sum_fp = std::fopen(sum_csv_path, "w");
  if (!raw_fp || !sum_fp) {
    std::fprintf(stderr, "Failed to open CSV output files\n");
    return 1;
  }
  std::fprintf(raw_fp, "regime,size_bytes,contender,kind,trial,reps,sec_per_call,gbps\n");
  std::fprintf(sum_fp,
               "regime,size_bytes,contender,kind,median_gbps,iqr_gbps,p25_gbps,p75_gbps,"
               "min_gbps,max_gbps,median_ns,ratio_vs_absl,ratio_vs_memcpy\n");

  struct Regime {
    const char* name;
    bool cold_cache;
    int fixed_s_off;  // -1 means cycle k in 1..7 across reps/trials
    int fixed_d_off;
  };
  const Regime regimes[] = {
      {"warm_aligned", false, 0, 0},
      {"warm_unaligned_1_7", false, -1, -1},
      {"warm_unaligned_skew_3_7", false, 3, 7},
      {"cold_aligned", true, 0, 0},
  };

  for (const Regime& reg : regimes) {
    std::printf("## Regime: %s\n\n", reg.name);
    for (size_t n : kSizes) {
      if (reg.cold_cache && n < 65536) continue;
      const size_t reps = RepsForSize(n, reg.cold_cache);
      std::vector<std::vector<double>> samples(kNumContenders, std::vector<double>(kTrials));

      // Per-size untimed warmup across all contenders.
      for (size_t c = 0; c < kNumContenders; ++c) {
        uint32_t s = 0;
        const size_t warm_reps = std::max<size_t>(1, reps / 4);
        for (size_t q = 0; q < warm_reps; ++q) {
          s = RunOne(kContenders[c].id, dbase, sbase, n, s);
        }
        warm_sink ^= s;
      }

      // Interleaved trials (rotating contender order per round).
      for (int t = 0; t < kTrials; ++t) {
        for (size_t step = 0; step < kNumContenders; ++step) {
          const size_t c = (step + static_cast<size_t>(t)) % kNumContenders;
          const size_t base_s_off =
              reg.fixed_s_off >= 0 ? static_cast<size_t>(reg.fixed_s_off)
                                   : static_cast<size_t>((t % 7) + 1);
          const size_t base_d_off =
              reg.fixed_d_off >= 0 ? static_cast<size_t>(reg.fixed_d_off)
                                   : static_cast<size_t>((t % 7) + 1);

          if (reg.cold_cache) {
            FlushCaches(evict, kEvictSize, static_cast<uint64_t>(t * 31 + c));
          }

          uint32_t acc = 0;
          const auto t0 = std::chrono::steady_clock::now();
          if (reg.fixed_s_off >= 0) {
            uint8_t* dst = dbase + base_d_off;
            const uint8_t* src = sbase + base_s_off;
            for (size_t q = 0; q < reps; ++q) {
              acc = RunOne(kContenders[c].id, dst, src, n, acc);
            }
          } else {
            for (size_t q = 0; q < reps; ++q) {
              const size_t k = ((q + static_cast<size_t>(t)) % 7) + 1;
              acc = RunOne(kContenders[c].id, dbase + k, sbase + k, n, acc);
            }
          }
          const auto t1 = std::chrono::steady_clock::now();
          warm_sink ^= acc;

          const double sec =
              std::chrono::duration<double>(t1 - t0).count() / static_cast<double>(reps);
          samples[c][t] = sec;
          std::fprintf(raw_fp, "%s,%zu,%s,%s,%d,%zu,%.12e,%.6f\n", reg.name, n,
                       kContenders[c].slug, kContenders[c].is_copy ? "copy_crc" : "crc_only", t,
                       reps, sec, static_cast<double>(n) / sec / 1e9);
        }
      }

      std::vector<Stats> stats(kNumContenders);
      for (size_t c = 0; c < kNumContenders; ++c) {
        stats[c] = ComputeStats(samples[c], n);
      }
      const double absl_memcpy_gbps = stats[0].median_gbps;
      const double plain_memcpy_gbps = stats[2].median_gbps;
      const double absl_extend_gbps = stats[6].median_gbps;

      std::printf("### Size: %s (%zu B, %zu reps/trial x %d trials)\n", HumanSize(n), n, reps,
                  kTrials);
      for (size_t c = 0; c < kNumContenders; ++c) {
        const Stats& st = stats[c];
        const double ref_absl = kContenders[c].is_copy ? absl_memcpy_gbps : absl_extend_gbps;
        const double vs_absl = st.median_gbps / ref_absl;
        const double vs_memcpy = st.median_gbps / plain_memcpy_gbps;
        std::printf("  %-44s %7.2f GB/s (IQR %5.2f, [%6.2f..%6.2f])  %9.2f ns  vs_absl=%5.2fx  vs_memcpy=%5.2fx\n",
                    kContenders[c].label, st.median_gbps, st.iqr_gbps, st.min_gbps, st.max_gbps,
                    st.median_ns, vs_absl, vs_memcpy);
        std::fprintf(sum_fp, "%s,%zu,%s,%s,%.6f,%.6f,%.6f,%.6f,%.6f,%.6f,%.3f,%.4f,%.4f\n",
                     reg.name, n, kContenders[c].slug,
                     kContenders[c].is_copy ? "copy_crc" : "crc_only", st.median_gbps, st.iqr_gbps,
                     st.p25_gbps, st.p75_gbps, st.min_gbps, st.max_gbps, st.median_ns, vs_absl,
                     vs_memcpy);
      }
      std::printf("\n");
      std::fflush(stdout);
    }
  }

  std::fclose(raw_fp);
  std::fclose(sum_fp);
  std::free(raw_src);
  std::free(raw_dst);
  std::free(raw_evict);
  return 0;
}
