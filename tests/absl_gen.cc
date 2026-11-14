// Emits random test cases with abseil's answers, one per line, for the Lean
// differential checker (tests/Diff.lean). Deterministic for a given seed.
//   E <init> <hexbytes|-> <ExtendCrc32c>
//   Z <crc> <n> <ExtendCrc32cByZeroes>
//   C <crcA> <crcB> <lenB> <ConcatCrc32c>
//   P <crcA> <crcAB> <lenB> <RemoveCrc32cPrefix>
//   S <crcAB> <crcB> <lenB> <RemoveCrc32cSuffix>
//   M <init> <hexbytes|-> <MemcpyCrc32c>      (also checks the copy here)
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>
#include <string>

#include "absl/crc/crc32c.h"

static void hex(const std::string& s) {
  if (s.empty()) { std::printf("-"); return; }
  for (unsigned char c : s) std::printf("%02x", c);
}

int main(int argc, char** argv) {
  uint64_t seed = argc > 1 ? std::strtoull(argv[1], nullptr, 10) : 1;
  int count = argc > 2 ? std::atoi(argv[2]) : 2000;
  std::mt19937_64 rng(seed);
  auto u32 = [&] { return static_cast<uint32_t>(rng()); };
  auto bytes = [&](size_t n) {
    std::string s(n, '\0');
    for (auto& c : s) c = static_cast<char>(rng());
    return s;
  };
  auto len = [&]() -> size_t {
    switch (rng() % 4) {
      case 0: return rng() % 17;
      case 1: return rng() % 300;
      default: return rng() % 2000;
    }
  };
  auto biglen = [&]() -> uint64_t {
    uint64_t v = rng();
    return v >> (rng() % 64);
  };
  for (int i = 0; i < count; ++i) {
    {
      uint32_t init = (i % 3 == 0) ? 0 : u32();
      std::string s = bytes(len());
      std::printf("E %u ", init); hex(s);
      std::printf(" %u\n", static_cast<uint32_t>(absl::ExtendCrc32c(absl::crc32c_t{init}, s)));
      std::string dst(s.size(), '\x5a');
      uint32_t m = static_cast<uint32_t>(
          absl::MemcpyCrc32c(dst.data(), s.data(), s.size(), absl::crc32c_t{init}));
      if (dst != s) { std::fprintf(stderr, "abseil copy mismatch\n"); return 1; }
      std::printf("M %u ", init); hex(s); std::printf(" %u\n", m);
    }
    {
      uint32_t c = u32(); uint64_t n = biglen();
      std::printf("Z %u %llu %u\n", c, (unsigned long long)n,
                  static_cast<uint32_t>(absl::ExtendCrc32cByZeroes(absl::crc32c_t{c}, n)));
    }
    {
      // Arbitrary words, not only genuine CRCs: the functions are total.
      uint32_t a = u32(), b = u32(); uint64_t n = biglen();
      std::printf("C %u %u %llu %u\n", a, b, (unsigned long long)n,
                  static_cast<uint32_t>(absl::ConcatCrc32c(absl::crc32c_t{a}, absl::crc32c_t{b}, n)));
      std::printf("P %u %u %llu %u\n", a, b, (unsigned long long)n,
                  static_cast<uint32_t>(absl::RemoveCrc32cPrefix(absl::crc32c_t{a}, absl::crc32c_t{b}, n)));
      std::printf("S %u %u %llu %u\n", a, b, (unsigned long long)n,
                  static_cast<uint32_t>(absl::RemoveCrc32cSuffix(absl::crc32c_t{a}, absl::crc32c_t{b}, n)));
    }
  }
  return 0;
}
