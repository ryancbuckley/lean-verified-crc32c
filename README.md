# leanmemcpy

`leanmemcpy` is a formally verified implementation of CRC32C (`ExtendCrc32c`, `ComputeCrc32c`, and the CRC algebra operations `Concat`, `RemovePrefix`, `RemoveSuffix`, `ExtendByZeroes`) and fused memory-copy-with-CRC32C (`MemcpyCrc32c`) written in **Lean 4** (`v4.35.0`), with a zero-allocation **C11 / C++17** static library (`cxx/leanmemcpy.h`) drop-in compatible with Abseil's CRC32C API.

Every CRC path—from a pure-register portable fallback to a 6-stream hardware `CRC32C + CLMUL` kernel—is proven equal in Lean's kernel to a 44-line polynomial specification over $\mathbb{F}_2[X]$ in `MemcpyCrc32c/Spec.lean`, using only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and zero `sorry`, `admit`, `bv_decide`, or `native_decide`. On AArch64 (Apple M4), the compiled machine code of the hardware CRC32C call graph (`7` functions, `1,137` instructions) is additionally verified instruction-by-instruction against an operational A64 ISA model validated against Arm's machine-readable ASL.

---

## What Has Been Accomplished

### 1. Polynomial Specification & CRC Algebra (`MemcpyCrc32c/Spec.lean`, `Arith.lean`)
- **Reference specification.** CRC32C is specified directly as polynomial remainder modulo the Castagnoli generator $G(X)$ in Mathlib's `(ZMod 2)[X]`, matching Abseil's conditioning conventions (`0xFFFFFFFF` XOR on entry and exit of `ExtendCrc32c`).
- **Verified CRC combinators.** `extend_append`, `concat_spec`, `removePrefix_spec`, `removeSuffix_spec`, and `extendZeroes_spec` are proven for unboxed $O(\log n)$ square-and-multiply arithmetic in $\mathbb{F}_2[X]/(G)$, alongside kernel-evaluated test vectors (`"123456789" -> 0xE3069283` and all five RFC 3720 B.4 iSCSI vectors).

### 2. Verified Portable Register Kernel (`MemcpyCrc32c/Portable.lean`)
- **Zero-polynomial (Chorba) reduction for CRC32C.** Because $G(X)$ has 18 terms, $X + 1 \mid G(X)$ and every multiple of $G$ has even weight (`eval_one_G`), so 3-term and 5-term zero polynomials do not exist for CRC32C. Exhaustive search certified the lowest-degree 6-term multiple:
  $$Z_{209}(X) = X^{209} + X^{144} + X^{54} + X^{39} + X^{14} + 1$$
  which cancels each 64-bit word and re-injects five shifted XORs across a 4-word register window.
- **Three-tier register pipeline (zero scratch RAM, zero heap allocation):**
  - `< 40 B`: packed 8 KiB `ByteArray` slicing-by-8 (`sliceLoop`).
  - `40 B .. 2 KiB`: single-stream `fold209` reduction.
  - `≥ 2 KiB`: 4-stream interleaved `fold209_4x` holding all 16 pending `UInt64` words in GP registers, combined via an 8 KiB precomputed shift table (`x64ShiftBytes`) and unrolled modular multiplication.
- **Throughput.** On Apple M4, `extendPortable` beats C slicing-by-8 at every size (`1.07×` at 16 B to `5.1×` at 1–64 MiB), reaching **11.4–11.5 GB/s** CRC-only—~97% of single-stream hardware `CRC32CX` throughput using plain integer registers.

### 3. Validated SIMD/CRC Model Library & Hybrid Hardware Kernel (`lean-simd-models/`, `MemcpyCrc32c/HwKernel.lean`)
- **`lean-simd-models` package.** Standalone Lake package giving pure Lean models, `V128` (`BitVec 128`) views, and $\mathbb{F}_2[X]$ theorems for reflected `CRC32C` (`8/16/32/64`-bit) and `64×64 -> 128` carry-less multiplication (`PMULL` / `PCLMULQDQ`).
  - Validated on AArch64 against Arm's machine-readable ASL via **ASLp** (`100,720` vectors across `CRC32CB/H/W/X` and `PMULL`, zero mismatches) and `16,640,000` hardware differential evaluations on Apple M4.
  - Cross-checked for x86-64 via universal kernel proofs (`SimdModels/IntelSdm.lean`) against a transcription of Intel SDM Vol. 2A/2B `CRC32` and `PCLMULQDQ` pseudocode, plus `299.5 MB` of byte-identical cross-architecture differential output under Rosetta 2.
- **Three-regime hardware CRC32C kernel (`extendHw`):**
  - `< 96 B`: frameless loop-free `CRC32CX/W/H/B` tree (`hwShort` / `hwTail16`).
  - `96 .. 767 B`: 3-way parallel `CRC32CX` (`48 B/iter`) combined via `PMULL + CRC32CX` (`combine3`).
  - `≥ 768 B`: 6-way hybrid **`3 × CRC32CX + 3 × PMULL` 64-byte dot-product** fold (`384 B/iter`, `hwFold6`), hiding loop-carried scalar accumulator latency behind 24 `CRC32CX` ops while feeding `pmull` + `eor3` directly from 128-bit loads.

### 4. Dispatched Copy-and-CRC, C11/C++17 ABI & Fuzzing (`cxx/`, `MemcpyCrc32c/CApi.lean`)
- **Headline Lean theorem (`memcpyCrc32c_spec`).** Regardless of what the `opaque` CPU capability probe returns at runtime, `memcpyCrc32c` returns `(src.copySlice sOff dst dOff n, Spec.extend init (src.extract sOff (sOff + n)))`.
- **C11 & C++17 static library (`libleanmemcpy.a`).** Built with `-fno-exceptions -fno-rtti` (links cleanly into pure `-std=c11` binaries without `-lc++`), synchronizing one-time Lean runtime startup behind a single acquire byte load on subsequent calls.
- **Memory-safety & sanitizer hardening:**
  - Static C-IR call-graph audit (`scripts/check_capi.sh`) verifying all 22 reachable generated C functions perform zero allocations, zero reference-count operations, and zero Lean object-header reads (`m_tag` / `m_size`).
  - `9,051` `PROT_NONE` guard-page boundary tests at alignments `0..7` (both with and without `-DNDEBUG`).
  - **106,000,000 `libFuzzer` + ASan + UBSan executions per path** (`cxx/fuzz.cc`, with Lean runtime assertions enabled, exact heap redzones, trailing sentinels, and threshold neighborhood sniping) against `absl::ExtendCrc32c` with **zero** mismatches or sanitizer findings.

### 5. Performance on Apple M4 (`bench/full_bench.cc`, `reports/bench_apple_m4_summary.csv`)
Measured against upstream `abseil-cpp` (`CMake Release`, `-O3 -DNDEBUG`) linked into the same process, 15 interleaved rounds rotating contender order, GB/s median:

| Size | `absl::MemcpyCrc32c` | **Lean `MemcpyCrc32c`** | Ratio vs Abseil | Lean `MemcpyCrc32cPortable` | C `slice8` + `memcpy` | Plain `memcpy` |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **16 B** (warm) | 3.70 (4.3 ns) | **4.50 (3.6 ns)** | **1.21×** (unaligned: **1.43×**) | 2.13 | 2.07 | 5.72 |
| **64 B** (warm) | 8.79 (7.3 ns) | **8.99 (7.1 ns)** | **1.02×** | 2.98 | 2.20 | 27.98 |
| **256 B** (warm) | 13.42 | **13.42** | **1.00×** | 5.80 | 2.21 | 46.67 |
| **1 KiB** (warm) | 18.61 | **22.81** | **1.23×** (unaligned: **1.43×**) | 6.73 | 2.21 | 94.87 |
| **4 KiB** (warm) | 19.93 | **30.77** | **1.54×** (unaligned: **1.63×**) | 8.87 | 2.13 | 102.67 |
| **64 KiB** (warm) | 19.83 | **32.10** | **1.62×** | 9.12 | 2.08 | 65.29 |
| **1 MiB** (warm) | 20.71 | **31.53** | **1.52×** | 9.87 | 2.15 | 79.79 |
| **64 MiB** (warm) | 20.94 | **23.94** | **1.14×** | 8.81 | 2.13 | 43.59 |
| **64 MiB** (cold) | 20.78 | **21.64** | **1.04×** | 8.81 | 2.09 | 39.27 |

For CRC-only (`ExtendCrc32c`), the out-of-line verified Lean function runs at **6.30 GB/s (`2.54 ns`)** at 16 B (`0.90×` Abseil's header-inlined fast path—within ~1 clock cycle across a C ABI call) and **56.1 GB/s** at 1 MiB (`0.90×` `absl::ExtendCrc32c`).

### 6. AArch64 Binary Machine-Code Verification (`MemcpyCrc32c/Arm64/`)
For the Apple M4 build, all **7 functions (`1,137` 32-bit instruction words)** reachable from `_lp_leanmemcpy_Crc32c_extendHwRaw___redArg` (`combine3`, `combine6`, `hwLoop`, `hwFold6Loop`, `hwFold6`, `rawExtendHwMulti`, `extendHwRaw`) are verified at the binary instruction level against `SimdModels/Arm64.lean`:
- **End-to-end theorem (`extendHwRaw_mc_spec`).** From any machine state entering `extendHwRaw___redArg` with code and constants loaded, read-only payload `a` at `objPtr + 0x18`, and `0x160` writable stack bytes below `SP`, execution terminates at `X30` with `W0 = Crc32c.Spec.extend c (a.extract 0 len)`, AAPCS64 callee-saved registers (`SP`, `X19..X30`, `D8..D15`) preserved, and all memory outside `[SP - 0x160, SP)`—including unmapped guard pages and the 24-byte region `[objPtr, objPtr + 0x18)` before a borrowed pointer—untouched. For `len < 96` (`extendHwRaw_short_mc_spec`), `0` stack bytes are required and memory is completely unchanged.
- **Binary & ISA validation.** `SimdModels/Arm64.lean` is checked against ASLp across `3,017` full-state vectors covering `996` distinct instruction words (including all `873` distinct words in the 7 functions), and `scripts/check_aarch64_mc.sh` checks byte-for-byte agreement between `Arm64/Code.lean` and the `.o` objects, `libleanmemcpy.a`, and linked Mach-O binary (including 7 branch relocations and 20 GOT pairs with Apple `ld` `adrp+ldr -> adrp+add` relaxation).

---

## Trusted Computing Base

`scripts/check_trusted.sh` scans every `.lean` file (after stripping comments and string literals) and rejects any `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp`, `native_decide`, `bv_decide`, or `@[extern]` outside `SimdModels/Trusted.lean`.

- **Source-level theorems (`MemcpyCrc32c/Axioms.lean`, 60 theorems):**
  1. Lean 4.35.0's kernel and Mathlib's polynomial definitions (`[propext, Classical.choice, Quot.sound]`).
  2. For native execution: Lean's C codegen, Clang, and the 9 `@[extern]` bindings in `SimdModels/Trusted.lean` (`crc32c_u8/16/32/64`, `clmulLo/Hi`, `loadU8`, `loadU64LE`, `cpuHasCrcClmul`), plus the ~295-line C++ wrapper `cxx/leanmemcpy.cc`.
- **AArch64 machine-code theorems (`MemcpyCrc32c/Arm64.lean`, hardware CRC call graph on this binary):**
  - **Removed from TCB:** Lean's compiler (`leanc`), `clang -O2`, and all C-shim instruction/load bindings (`crc32c_*`, `clmul*`, `loadU8`, `loadU64LE`).
  - **Remaining in TCB:** Lean's kernel, the A64 operational model (`SimdModels/Arm64.lean`), the Mach-O byte-audit script (`scripts/check_aarch64_mc.py`), the loader/module-init assumption (`CodeLoaded` / `GlobalsLoaded`), and the outer C++ wrapper (`cxx/leanmemcpy.cc`: dispatch, copy, and entry register contract).

---

## Methodological Insights

1. **Split executable `Impl/` modules from Mathlib proof modules.**
   Keeping executable code in `MemcpyCrc32c/Impl/` (importing only `Init`) while placing `GF(2)[X]` specs and equivalence proofs in `MemcpyCrc32c/*.lean` gives full access to Mathlib's `AdjoinRoot` quotient-ring machinery during verification without ever linking Mathlib into native C/C++ builds.

2. **Scalar-typed `@[extern]` bindings + proof-only `V128` views avoid heap boxing.**
   Lean has no unboxed 128-bit scalar type; an `@[extern]` over `BitVec 128` allocates on every intrinsic. Typing executable bindings over unboxed `UInt32` / `UInt64` halves (`clmulLo`, `clmulHi`, `loadU64LE`) while reconstructing `V128` (`BitVec 128`) only in proof terms lets Clang fuse adjacent operations into native 128-bit NEON / XMM instructions (`ldp q`, `pmull`, `eor3`) with zero allocations.

3. **Proof-erased bounds witnesses unlock unaligned word loads—and `lean_sarray_object*` has a hidden alignment/header trap.**
   - *Throughput:* Lean's `lean_sarray_object` declares `uint8_t m_data[0]`, preventing LLVM from merging 8 safe `ByteArray.uget` byte loads across `[0 x i8]` bounds (`14.5 GB/s` vs `58.6 GB/s` at 1 MiB). Passing erased proof witnesses `a.size < USize.size` and `off + 8 ≤ a.size` to an inline `__builtin_memcpy` `uint64_t` load (`loadU64LE`) restores full hardware bandwidth with zero runtime checks.
   - *Safety:* Wrapping a raw C caller pointer `p` via `p - offsetof(lean_sarray_object, m_data)` looks benign until `lean_byte_array_uget` -> `lean_sarray_cptr` casts that synthetic address to `lean_sarray_object*`: for unaligned `p` (`1..7`), forming the struct pointer is immediate C/UBSan alignment UB, and without `-DNDEBUG` it asserts `lean_is_sarray` by reading `m_tag` 24 bytes before `p` (faulting on a guard page). Computing `(const uint8_t *)((uintptr_t)a + offsetof(...))` in unsigned integer arithmetic (`SIMDMODELS_SARRAY_BYTES`) and auditing the transitive C-IR call graph (`scripts/check_capi.sh`) eliminates both bugs.

4. **Make runtime CPU feature probes `opaque`.**
   Declaring `cpuHasCrcClmul : Unit -> Bool` as `opaque` (rather than giving it a Lean `true`/`false` model) prevents any proof from assuming which branch executes, forcing every dispatched kernel to satisfy the exact same spec and reducing CPU-detection risk purely to "does not `SIGILL`".

5. **Pure kernel proofs scale without `bv_decide`.**
   In Lean 4.35, `bv_decide` introduces compiler-trusted `_native.bv_decide` axioms. Bitwise word-assembly lemmas (`BitVec.eq_of_getLsbD_eq`), `GF(2)[X]` polynomial identities in `AdjoinRoot G`, `decide +kernel` on finite tables/decode certificates, and integer bounds on compiler-emitted magic-number divisions (`÷ 48` via `0xAAAB` / `0xAAAAAAAAAAAAAAAB`, `÷ 384`) proved fast enough to keep every theorem—including `1,137` A64 machine instructions—strictly axiom-clean.

6. **Decoupled `memcpy` + wide CRC beat interleaved loops on Apple M4—once microarchitectural hazards at 16 B were cleared.**
   Interleaving copy with CRC (and 512 KiB cache-blocked fusion) underperformed calling platform `memcpy` followed by the 6-stream CRC+PMULL fold on M4 (`31.5 GB/s` vs Abseil's `20.7 GB/s` at 1 MiB), while avoiding any trusted mutable store primitive. At 16 B, disassembly and profiling uncovered two subtle stalls: an unconditional 144-byte stack frame triggered by an inlined 22-argument cold call, and an Apple M4 4 KiB store-to-load virtual-offset aliasing penalty whenever `(dest & 0xFFF) == (src & 0xFFF)` if `dest` was written immediately before `src` was checksummed. Outlining the cold path, making `< 96 B` frameless, and checksumming `src` before inline `CopyUpTo64` cut 16 B latency from `8.68 ns` to `3.56 ns`.

7. **Combine hand-structured loop invariants with untrusted path generation for binary verification.**
   In compiled machine code, steady-state loops (`hwLoop`, `hwFold6Loop`, `rawExtendHwMulti`) have clean inductive invariants suited to hand-written symbolic execution, whereas Clang's jump-threaded `< 96 B` decision DAG (`420` instructions with merged tails and shifting base pointers) fights symbolic `len`. Using an untrusted Python tracer (`scripts/gen_aarch64_short_paths.py`) to emit one straight-line Lean lemma per concrete byte length (`0..95`) keeps the generator completely outside the TCB—any wrong step fails Lean kernel typechecking—while covering all 420 instructions cleanly.

8. **Binary machine-code proofs belong at the *end* of tuning, not the middle.**
   Lean-level proofs (`HwKernel.lean`, `Portable.lean`) survive kernel retuning and compiler upgrades; binary proofs (`Arm64/*.lean`) are tied to one exact compiler, flag set, target ISA, and instruction stream. Any retuning changes the emitted words and breaks `check_aarch64_mc.sh` until re-verified. Stabilize per-platform kernel shapes first, and apply binary verification only after a target's binary has settled.

---

## What Remains & Roadmap for x86-64 and Server ARM

Everything above has been tuned and hardware-tested on **Apple M4 (macOS / AArch64)**. Although x86-64 codegen (`-msse4.2 -mpclmul`) already compiles cleanly with all `CRC32` and `PCLMULQDQ` intrinsics inlined and passes Rosetta 2 differential checks, real x86-64 and server-ARM deployment remains open:

1. **Measure first on real target silicon (Linux port of benchmarks & harnesses).**
   Rosetta 2 validates functional lowering, not silicon or microarchitecture. The immediate next step is making `bench/run_bench.sh` and the Abseil comparison run natively on Linux across rented cloud instances: a modern Intel server core, a modern AMD Zen part, an older x86-64 core without wide carry-less multiply, and two or three AWS Graviton generations.

2. **Expect optimal kernel shapes to differ across microarchitectures.**
   Stream counts, fold strides, and size thresholds depend on `CRC32` vs `CLMUL` port throughput and latency, vector width (`128`/`256`/`512`-bit on x86-64), and L1/L2/LLC geometry—which is why Abseil itself selects stream counts per CPU model. Parameters tuned for Apple M4's unusually wide core (`3 × CRC32CX + 3 × PMULL` at `384 B/iter`) are unlikely to be optimal on Intel/AMD or narrower Neoverse cores.

3. **Parameterize the hardware kernel *before* retuning.**
   Refactor stream counts, block sizes, and regime thresholds into explicit parameters of a single verified Lean kernel and prove correctness once for all valid parameter choices. Per-CPU tuning then reduces to picking constants without writing new proofs.

4. **Dispatch across a small, disciplined family of ISA kernels.**
   Each additional hardware instruction requires a model and vendor validation in `lean-simd-models`, so the kernel family should stay compact:
   - **x86-64:** baseline `SSE4.2 + PCLMULQDQ` (128-bit), wider `AVX2 + VPCLMULQDQ` (256-bit), and `AVX-512 + VPCLMULQDQ` (512-bit), alongside mechanically checking `SimdModels/IntelSdm.lean` against Intel's machine-readable Intrinsics Guide XML.
   - **AArch64:** baseline `CRC32 + PMULL` versus `CRC32 + PMULL + EOR3` (`FEAT_SHA3`).

5. **Audit and gate the `EOR3` (`FEAT_SHA3`) dependency on ARM.**
   On Apple M4, Clang compiles the 3-way XOR in `hwFold6` into `eor3.16b` (`FEAT_SHA3`). Currently, `simdmodels_cpu_has_crc_clmul()` in `lean-simd-models/c/simd_shim.h` checks only `HWCAP_CRC32` and `HWCAP_PMULL` on Linux—not `HWCAP_SHA3`. Older ARMv8.0/8.1 server cores (such as Graviton 2 / Neoverse N1) implement `CRC32 + PMULL` without `FEAT_SHA3`, so ARM builds must either compile the baseline hardware kernel without `+sha3` or split dispatch so `+sha3` code is gated on `HWCAP_SHA3`.

6. **Re-evaluate copy fusion and non-temporal stores on x86-64.**
   Sequential `memcpy`-then-CRC showed no penalty on M4's large system-level cache, but on x86-64 servers with buffers exceeding LLC, two passes evict data before checksumming, and temporal stores pollute cache via RFO traffic. Interleaved copy-and-CRC or non-temporal streaming stores (`MOVNTDQ`, as Abseil uses for large buffers) should be benchmarked on real x86-64 memory hierarchies.

7. **Pin or audit compilers per target.**
   Small-buffer latency (`16–95 B`) depends heavily on how the C compiler lowers Lean's generated C (tail calls, shrink-wrapping, paired loads, vectorization). Different Clang versions or GCC on Linux may emit spills or unwanted vectorization from the same Lean source (note `cxx/build.sh` already passes `-fno-vectorize -fno-slp-vectorize` to `HwCombine.c` on x86-64); either pin the compiler per release target or inspect emitted assembly on each platform.

8. **Optional portable throughput gap (`~10 GB/s` vs `~15 GB/s`).**
   Closing the remaining large-buffer gap on hardware-less targets would use Chorba's word-aligned $Z(X^{64})$ scratch-buffer reduction (`~15 GB/s` in `bench/proto.c`), which requires adding a verified mutable 64-bit word-buffer primitive.

---

## Repository Layout

```text
MemcpyCrc32c/
  Poly.lean, Spec.lean        # GF(2)[X] Castagnoli polynomial & frozen CRC32C spec
  Bitwise.lean, Vectors.lean  # Bit-at-a-time reference & RFC 3720 / standard test vectors
  Arith.lean                  # Proofs for append, concat, removePrefix/Suffix, extendZeroes
  ZeroPoly.lean, Word64.lean  # Certified CRC32C zero polynomials & 64-bit word lemmas
  Portable.lean               # Equivalence proof for 3-tier Chorba portable kernel
  Hw.lean, HwKernel.lean      # Equivalence proof for 3-regime CRC32C + CLMUL kernel
  Memcpy.lean, Dispatch.lean  # Copy-and-CRC & opaque runtime CPU-dispatch proofs
  CApi.lean, Axioms.lean      # C-ABI entry-point theorems & #print axioms audit (60 theorems)
  Impl/                       # Mathlib-free executable Lean implementations
  Arm64.lean, Arm64/          # AArch64 binary machine-code proofs (7 functions, 1,137 insns)
lean-simd-models/
  SimdModels/                 # V128 & scalar CRC/CLMUL models, GF(2)[X] specs, Intel SDM & A64 ISA
  c/simd_shim.h               # Target-guarded C intrinsics & alignment-safe byte/word loads
  tests/, validation/         # ASLp vectors, hardware differential tests & Rosetta cross-check
cxx/                          # C11/C++17 static library (leanmemcpy.h/.cc), tests & libFuzzer
bench/                        # Full CMake-Abseil benchmark suite & C prototypes
scripts/                      # TCB scanner, C-IR call-graph audit, Mach-O binary byte checker
reports/                      # Detailed development notes & raw Apple M4 benchmark CSVs
```

---

## Building & Verifying

```bash
# 1. Kernel-check all Lean specs, portable & hardware kernels, dispatch, C-API & axiom audit
lake build

# 2. Verify zero unauthorized externs, axioms, sorry, or bv_decide across all .lean files
./scripts/check_trusted.sh

# 3. Build C11/C++17 static library (build/cxx/libleanmemcpy.a) and run C-IR & guard-page audits
./cxx/build.sh
./scripts/check_capi.sh

# 4. Run instruction-model hardware differential & Arm ASL regression checks
(cd lean-simd-models && lake exe hw_diff 100000 1)
(cd lean-simd-models && lake exe asl_check < validation/asl_vectors_arm.txt)

# 5. Kernel-check AArch64 binary machine-code proofs (takes ~4 minutes) & audit Mach-O bytes
lake build MemcpyCrc32c.Arm64
./scripts/check_aarch64_mc.sh
(cd lean-simd-models && lake exe asl_arm64_check < validation/asl_vectors_arm64.txt)
```

---

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

