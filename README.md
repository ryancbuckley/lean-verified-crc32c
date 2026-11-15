# lean-verified-crc32c

`lean-verified-crc32c` is a formally verified implementation of CRC32C (`ExtendCrc32c`, `ComputeCrc32c`, and the CRC algebra operations `Concat`, `RemovePrefix`, `RemoveSuffix`, `ExtendByZeroes`) and fused memory-copy-with-CRC32C (`MemcpyCrc32c`) written in **Lean 4** (`v4.35.0`), with a zero-allocation **C11 / C++17** static library (`cxx/leancrc32c.h`) that mirrors Abseil's CRC32C API. The library still links against Lean's runtime shared libraries (`libleanshared`, `libInit_shared`; see `build/cxx/LINK_FLAGS`) for one-time module initialization.

**Naming.** In code, the project is called `leancrc32c`: the Lake package, `cxx/leancrc32c.h` / `.cc`, `libleancrc32c.a`, the C functions (`leancrc32c_extend_crc32c`, …), the C++ namespace (`leancrc32c::`), and the compiled Lean symbols (`_lp_leancrc32c_...`). The Lean library and its source directory keep the name `MemcpyCrc32c`, and Lean declarations live in the `Crc32c` namespace.

**Platform status.** Everything here was built, tuned, tested and benchmarked on one machine: an Apple M4 running macOS. x86-64 has only been exercised under Rosetta 2, and no other AArch64 core or operating system has been tried. Read every performance number below as an M4 number.

*New to CRCs, polynomial folding, or formal verification in Lean? Start with [background.md](background.md).*

Every CRC path—from a pure-register portable fallback to a 6-stream hardware `CRC32C + CLMUL` kernel—is proven equal in Lean's kernel to a 44-line polynomial specification over $\mathbb{F}_2[X]$ in `MemcpyCrc32c/Spec.lean`, using only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and zero `sorry`, `admit`, `bv_decide`, or `native_decide`. On AArch64 (Apple M4), the compiled machine code of the hardware CRC32C call graph (`7` functions, `1,137` instructions) is additionally verified instruction-by-instruction against an operational A64 ISA model validated against Arm's machine-readable ASL.

---

## What Has Been Accomplished

### 1. Polynomial Specification, Generator Algebra & Error Detection (`MemcpyCrc32c/Spec.lean`, `Arith.lean`, `PolyAlgebra.lean`, `ErrorDetection.lean`)
- **Reference specification.** CRC32C is specified directly as polynomial remainder modulo the Castagnoli generator $G(X)$ in Mathlib's `(ZMod 2)[X]`, matching Abseil's conditioning conventions (`0xFFFFFFFF` XOR on entry and exit of `ExtendCrc32c`).
- **Verified CRC combinators.** `extend_append`, `concat_spec`, `removePrefix_spec`, `removeSuffix_spec`, and `extendZeroes_spec` are proven for unboxed $O(\log n)$ square-and-multiply arithmetic in $\mathbb{F}_2[X]/(G)$, alongside kernel-evaluated test vectors (`"123456789" -> 0xE3069283` and all five RFC 3720 B.4 iSCSI vectors).
- **Castagnoli generator structure (`PolyAlgebra.lean`).** $G(X)$ factors into irreducible factors $(X + 1) \cdot P_{31}(X)$ (`G_eq_mul_P31`, `irreducible_X_add_one`, `irreducible_P31`, `squarefree_G`). Using Mathlib's Lucas–Lehmer test for $M_{31} = 2^{31} - 1$, $P_{31}(X)$ is proven primitive (`orderOf_root_P31`) and $\pi(X) \in \mathbb{F}_2[X]/(G)$ has exact multiplicative order $2^{31} - 1$ (`orderOf_π_X`), alongside characteristic-2 Frobenius invariance (`dvd_expand_two_pow_iff`: $G(X) \mid p(X^{2^k}) \iff G(X) \mid p(X)$).
- **End-to-end error detection & Hamming-distance bounds (`ErrorDetection.lean`).** Two same-length messages + CRCs collide iff $G(X)$ divides their codeword error polynomial (`dvd_codewordError_iff`). Combining this with the generator and minimal zero-polynomial theorems yields kernel-checked Castagnoli/Koopman guarantees for `Spec.extend`, `computeCrc32c`, and `memcpyCrc32c`:
  - **All odd-weight bit errors** (`Spec.extend_detects_odd_errors`) and **all $\le 32$-bit / 4-byte burst errors** (`Spec.extend_detects_burst32`, `Spec.extend_ne_of_burst4Bytes`) at arbitrary message lengths.
  - **Hamming-distance guarantees for whole-byte buffers:** **HD = 4** up to `268,435,451` B (`~256 MiB`, `Spec.extend_hd4`), **HD = 6** up to `655` B (Koopman's bit-level limit is `5,243` payload bits) covering **512 B storage sectors** (`Spec.extend_hd6`, `memcpyCrc32c_sector_hd6`), **HD = 8** up to `22` B (`Spec.extend_hd8`), and **HD = 10** up to `5` B codeword / `9` B uncorrupted-CRC payload (`Spec.extend_hd10`, `Spec.extend_payload_hd10`). The theorems prove detection. The limits match Koopman's published bit lengths and cannot be raised, because the zero polynomials in section 2 fit in the next byte; that converse is not stated as a Lean theorem.

### 2. Certified Zero Polynomials & Verified Portable Register Kernel (`MemcpyCrc32c/ZeroPoly.lean`, `ZeroPolyMinimal.lean`, `Portable.lean`)
- **Zero-polynomial (Chorba) reduction for CRC32C.** Because $G(X)$ has 18 terms, $X + 1 \mid G(X)$ and every nonzero multiple of $G$ has positive even weight (`even_card_support_of_dvd_G`), ruling out odd weights (`3, 5, 7, 9`). Across every sparse-multiple regime, both **degree minimality** and **uniqueness** are proven in the Lean kernel:
  - **Weight $< 8$ (`≤ 6` terms, `zero6_209_minimal` / `zero6_209_unique`):** every nonzero multiple of $G$ with fewer than 8 terms has degree $\ge 209$, and the unique degree-209 multiple is
    $$Z_{209}(X) = X^{209} + X^{144} + X^{54} + X^{39} + X^{14} + 1$$
    which cancels each 64-bit word and re-injects five shifted XORs across a 4-word register window. By Frobenius invariance, $Z_{209}(X^{64})$ (`13,376` bits) is likewise the unique minimal 64-bit word-aligned multiple with $< 8$ terms (`zero6_word64_minimal`, `zero6_word64_unique`).
  - **Other Chorba & Koopman regimes:** unique minimal `< 4`-term (`2`-term) multiple $X^{2^{31}-1} + 1$ (`zero2_minimal` / `zero2_unique`); unique minimal `< 6`-term (`4`-term) multiple $X^{5275} + X^{4508} + X^{2751} + 1$ (`zero4_5275_minimal` / `zero4_5275_unique`); unique minimal `< 8`-term multiple with leading gap $\ge 128$ (128-bit folding) $X^{290} + X^{136} + X^{113} + X^{107} + X^{32} + 1$ (`zero6_290_minimal` / `zero6_290_unique`); and unique minimal `< 10`-term (`8`-term) multiple $X^{79} + X^{75} + X^{71} + X^{58} + X^{18} + X^{12} + X + 1$ (`zero8_79_minimal` / `zero8_79_unique`).
- **Three-tier register pipeline (zero scratch RAM, zero heap allocation):**
  - `< 40 B`: packed 8 KiB `ByteArray` slicing-by-8 (`sliceLoop`).
  - `40 B .. 2 KiB`: single-stream `fold209` reduction.
  - `≥ 2 KiB`: 4-stream interleaved `fold209_4x` holding all 16 pending `UInt64` words in GP registers, combined via an 8 KiB precomputed shift table (`x64ShiftBytes`) and unrolled modular multiplication.
- **Throughput.** On Apple M4, `extendPortable` beats C slicing-by-8 at every size (`1.07×` at 16 B to `5.1×` at 1–64 MiB), reaching **11.4–11.5 GB/s** CRC-only—~97% of single-stream hardware `CRC32CX` throughput using plain integer registers. This is still `0.42–0.48×` `absl::MemcpyCrc32c` in the copy benchmark below, short of the project's goal of staying within `1.5×` of Abseil on the portable path. The 4-stream kernel leans on the M4's wide core; expect a smaller gain over slicing-by-8 on narrower cores.

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
- **C11 & C++17 static library (`libleancrc32c.a`).** Built with `-fno-exceptions -fno-rtti` (links cleanly into pure `-std=c11` binaries without `-lc++`), synchronizing one-time Lean runtime startup behind a single acquire byte load on subsequent calls.
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

How to read this table:

- **The copy win comes from strategy, not from a faster CRC.** On the M4, `absl::MemcpyCrc32c` runs at about 20 GB/s while `absl::ExtendCrc32c` alone runs at about 62 GB/s, so Abseil's fused routine is the slow one here. Plain `memcpy` followed by `absl::ComputeCrc32c` (the `memcpy_plus_absl_compute` rows in the CSV) reaches 32–34 GB/s at 4 KiB–1 MiB, level with or slightly ahead of the Lean routine. Abseil's fused path was tuned for x86-64 servers; do not expect the `1.5×` to carry over there.
- **The CRC kernel itself is 10–15% behind Abseil's at 64 KiB and above** (see the CRC-only figures below). That gap is the honest measure of the kernel and is still open.
- **Cold-cache and unaligned results are weaker in places.** Cold at 1 MiB the Lean routine is `0.96×` Abseil and at 64 KiB `1.06×`; warm unaligned at 256 B it is `0.91×`. The full set is in `reports/bench_apple_m4_summary.csv`.

For CRC-only (`ExtendCrc32c`), the out-of-line verified Lean function runs at **6.30 GB/s (`2.54 ns`)** at 16 B (`0.90×` Abseil's header-inlined fast path—within ~1 clock cycle across a C ABI call) and **56.1 GB/s** at 1 MiB (`0.90×` `absl::ExtendCrc32c`).

### 6. AArch64 Binary Machine-Code Verification (`MemcpyCrc32c/Arm64/`)
For the Apple M4 build, all **7 functions (`1,137` 32-bit instruction words)** reachable from `_lp_leancrc32c_Crc32c_extendHwRaw___redArg` (`combine3`, `combine6`, `hwLoop`, `hwFold6Loop`, `hwFold6`, `rawExtendHwMulti`, `extendHwRaw`) are verified at the binary instruction level against `SimdModels/Arm64.lean`:
- **End-to-end theorem (`extendHwRaw_mc_spec`).** From any machine state entering `extendHwRaw___redArg` with code and constants loaded, read-only payload `a` at `objPtr + 0x18`, and `0x160` writable stack bytes below `SP`, execution terminates at `X30` with `W0 = Crc32c.Spec.extend c (a.extract 0 len)`, AAPCS64 callee-saved registers (`SP`, `X19..X30`, `D8..D15`) preserved, and all memory outside `[SP - 0x160, SP)` unchanged. The theorem assumes only the payload, the constants and the stack are mapped, and the model faults on any access to an unmapped byte, so the code provably never reads the 24 bytes `[objPtr, objPtr + 0x18)` in front of a borrowed pointer or anything past the payload. For `len < 96` (`extendHwRaw_short_mc_spec`), `0` stack bytes are required and memory is completely unchanged.
- **Which binary.** The proofs are about the objects produced by `cxx/build.sh` (system `clang -O2` on the Lean-generated C), not the executables `lake` links with Lean's bundled clang. They cover the hardware CRC path only: not the portable path, the dispatch, the copy, or the C++ wrapper.
- **Binary & ISA validation.** `SimdModels/Arm64.lean` is checked against ASLp across `3,017` full-state vectors covering `996` distinct instruction words (including all `873` distinct words in the 7 functions), and `scripts/check_aarch64_mc.sh` checks byte-for-byte agreement between `Arm64/Code.lean` and the `.o` objects, `libleancrc32c.a`, and linked Mach-O binary (including 7 branch relocations and 20 GOT pairs with Apple `ld` `adrp+ldr -> adrp+add` relaxation).

---

## Trusted Computing Base

`scripts/check_trusted.sh` scans every `.lean` file (after stripping comments and string literals) and rejects any `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp`, `native_decide`, or `@[extern]` outside `SimdModels/Trusted.lean`. `bv_decide` is permitted only inside a directory named `BvDecide/` (the agreed quarantine policy); no such directory exists, so none is used.

- **Source-level theorems (`MemcpyCrc32c/Axioms.lean`, 102 theorems, enforced via `#guard_msgs`):**
  1. Lean 4.35.0's kernel and Mathlib's polynomial definitions (`[propext, Classical.choice, Quot.sound]`).
  2. For native execution: Lean's C codegen, Clang, and the 9 `@[extern]` bindings in `SimdModels/Trusted.lean` (`crc32c_u8/16/32/64`, `clmulLo/Hi`, `loadU8`, `loadU64LE`, `cpuHasCrcClmul`), plus the ~295-line C++ wrapper `cxx/leancrc32c.cc`.
- **AArch64 machine-code theorems (`MemcpyCrc32c/Arm64.lean`, hardware CRC call graph on this binary):**
  - **Removed from TCB:** Lean's compiler (`leanc`), `clang -O2`, and all C-shim instruction/load bindings (`crc32c_*`, `clmul*`, `loadU8`, `loadU64LE`).
  - **Remaining in TCB:** Lean's kernel, the A64 operational model (`SimdModels/Arm64.lean`, validated by testing against Arm's ASL, not proven: two random states per compiled instruction word plus edge-case families), the Mach-O byte-audit script (`scripts/check_aarch64_mc.py`), the loader/module-init assumption (`CodeLoaded` / `GlobalsLoaded`: the constants are written at run time by Lean's unverified module initializer, and no Lean term shows the assumptions are satisfiable for a concrete memory image), and the outer C++ wrapper (`cxx/leancrc32c.cc`: dispatch, copy, and entry register contract).

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
   In Lean 4.35, `bv_decide` introduces compiler-trusted `_native.bv_decide` axioms. Bitwise word-assembly lemmas (`BitVec.eq_of_getLsbD_eq`), `GF(2)[X]` polynomial identities in `AdjoinRoot G`, `decide +kernel` on finite tables, `rfl` decode certificates, and integer bounds on compiler-emitted magic-number divisions (`÷ 48` via `0xAAAB` / `0xAAAAAAAAAAAAAAAB`, `÷ 384`) proved fast enough to keep every theorem—including `1,137` A64 machine instructions—strictly axiom-clean.

6. **Decoupled `memcpy` + wide CRC beat interleaved loops on Apple M4—once microarchitectural hazards at 16 B were cleared.**
   Interleaving copy with CRC (and 512 KiB cache-blocked fusion) did not beat calling platform `memcpy` followed by the 6-stream CRC+PMULL fold on M4 (a fair alternating A/B at 64 MiB gave 22–23 GB/s blocked against 24.5 GB/s unblocked; an earlier quick experiment suggesting a 25% gain from blocking was a first-touch artefact). The simple form also avoids any trusted mutable store primitive. This is an M4 result: the same comparison must be rerun on each target before the copy strategy is fixed there. At 16 B, disassembly and profiling uncovered two subtle stalls: an unconditional 144-byte stack frame triggered by an inlined 22-argument cold call, and an Apple M4 4 KiB store-to-load virtual-offset aliasing penalty whenever `(dest & 0xFFF) == (src & 0xFFF)` if `dest` was written immediately before `src` was checksummed. Outlining the cold path, making `< 96 B` frameless, and checksumming `src` before inline `CopyUpTo64` cut 16 B latency from `8.68 ns` to `3.56 ns`.

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

5. **Decide how `EOR3` (`FEAT_SHA3`) is handled on ARM.**
   The source never asks for `EOR3`: the shim requests only `crc,aes`, and the runtime probe checks only CRC32 and PMULL. The M4 binary contains `eor3` because Apple's default arm64 target includes `FEAT_SHA3`, so Clang fuses the fold's two XORs. Consequences for other ARM targets:
   - A Linux build with a generic `-march` will not emit `eor3`. It is safe on older cores (Graviton 2 / Neoverse N1 have no `FEAT_SHA3`) but the fold has one more instruction per 128-bit lane than the code that was tuned and proven here, so both its speed and its instruction words differ.
   - A build with `-mcpu=native` or `+sha3` will emit `eor3` and will fault on cores without it, because nothing gates on `HWCAP_SHA3`. If such builds are wanted, add a separately compiled `+sha3` variant behind its own probe.

6. **Re-evaluate copy fusion and non-temporal stores on x86-64.**
   Sequential `memcpy`-then-CRC showed no penalty on M4's large system-level cache, but on x86-64 servers with buffers exceeding LLC, two passes evict data before checksumming, and temporal stores pollute cache via RFO traffic. Interleaved copy-and-CRC or non-temporal streaming stores (`MOVNTDQ`, as Abseil uses for large buffers) should be benchmarked on real x86-64 memory hierarchies.

7. **Pin or audit compilers per target.**
   Small-buffer latency (`16–95 B`) depends heavily on how the C compiler lowers Lean's generated C (tail calls, shrink-wrapping, paired loads, vectorization). Different Clang versions or GCC on Linux may emit spills or unwanted vectorization from the same Lean source (note `cxx/build.sh` already passes `-fno-vectorize -fno-slp-vectorize` to `HwCombine.c` on x86-64); either pin the compiler per release target or inspect emitted assembly on each platform.

8. **Things to check on the first real x86-64 run.**
   - `clmulLo` and `clmulHi` are separate bindings that each perform a full carry-less multiply. The design relies on the compiler merging each lo/hi pair into one multiply; confirm in the x86-64 disassembly that each pair becomes a single `pclmulqdq` and not two.
   - Rosetta 2 does not provide AVX-512, so wider `VPCLMULQDQ` kernels cannot be tested on this machine even functionally.
   - Only the 128-bit instructions have models. Every wider instruction needs a model, a vendor cross-check and a hardware differential run in `lean-simd-models` before a kernel may use it.
   - The shim uses GCC/Clang builtins and target attributes; MSVC is unsupported.

9. **Close the CRC-kernel gap to Abseil on large buffers.**
   CRC-only throughput is `0.85–0.90×` `absl::ExtendCrc32c` from 64 KiB up on the M4. This gap exists independently of the copy and is the first thing to investigate when retuning stream counts.

10. **Portable throughput gap (`~10 GB/s` vs `~15 GB/s`); the `1.5×` goal is not met.**
   Closing the remaining large-buffer gap on hardware-less targets would use Chorba's word-aligned $Z(X^{64})$ scratch-buffer reduction (`~15 GB/s` in `bench/proto.c`), which requires adding a verified mutable 64-bit word-buffer primitive.

---

## Repository Layout

```text
MemcpyCrc32c/
  Poly.lean, Spec.lean        # GF(2)[X] Castagnoli polynomial & frozen CRC32C spec
  PolyAlgebra.lean            # (X+1)*P31 factorization, Lucas-Lehmer order 2^31-1 & Frobenius invariance
  Bitwise.lean, Vectors.lean  # Bit-at-a-time reference & RFC 3720 / standard test vectors
  Arith.lean                  # Proofs for append, concat, removePrefix/Suffix, extendZeroes
  ZeroPoly.lean, Word64.lean  # Certified CRC32C zero polynomials & 64-bit word lemmas
  ZeroPolyMinimal.lean, ZeroMin/ # Minimality & uniqueness for weights <4, <6, <8 (deg 209, 290, word64), <10
  ErrorDetection.lean         # Odd-error, 32-bit burst & Castagnoli/Koopman HD=4,6,8,10 theorems
  Portable.lean               # Equivalence proof for 3-tier Chorba portable kernel
  Hw.lean, HwKernel.lean      # Equivalence proof for 3-regime CRC32C + CLMUL kernel
  Memcpy.lean, Dispatch.lean  # Copy-and-CRC & opaque runtime CPU-dispatch proofs
  CApi.lean, Axioms.lean      # C-ABI entry-point theorems & #guard_msgs axiom audit (102 theorems)
  Impl/                       # Mathlib-free executable Lean implementations
  Arm64.lean, Arm64/          # AArch64 binary machine-code proofs (7 functions, 1,137 insns)
lean-simd-models/
  SimdModels/                 # V128 & scalar CRC/CLMUL models, GF(2)[X] specs, Intel SDM & A64 ISA
  c/simd_shim.h               # Target-guarded C intrinsics & alignment-safe byte/word loads
  tests/, validation/         # ASLp vectors, hardware differential tests & Rosetta cross-check
cxx/                          # C11/C++17 static library (leancrc32c.h/.cc), tests & libFuzzer
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

# 3. Build C11/C++17 static library (build/cxx/libleancrc32c.a) and run C-IR & guard-page audits
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

### Requirements and caveats

- Tested only on macOS / Apple Silicon with Lean 4.35.0 (via `elan`) and Apple clang 17. `cxx/build.sh` is plain shell and should port; `cxx/build_fuzz.sh`, `scripts/check_aarch64_mc.sh` and `scripts/gen_aarch64_short_paths.py` use `xcrun` and Mach-O and will need work on Linux.
- Differential tests, the fuzzer and the benchmarks need an `abseil-cpp` checkout: pass its path to `tests/build_absl.sh`, or set `ABSEIL` for `bench/run_bench.sh` (both default to `~/programming/temp/abseil-cpp`).
- ASLp is needed only to regenerate the vector files in `lean-simd-models/validation/`; the checked-in vectors replay without it.
- The repository uses `jj`.

### Ground rules for changes

- `MemcpyCrc32c/Spec.lean` is frozen (SHA-1 `bfe6e5a8c35be5b36198a9f385401da248d7c61e`). Do not edit it without sign-off.
- Never weaken a theorem to make a change fit; no `sorry`, `admit` or new axioms. Run `scripts/check_trusted.sh`.
- One optimization per commit, with measurements. Measure on an idle machine and alternate contenders; two wrong conclusions in this project came from skipping that.
- After any change to the hardware kernel, compiler or flags, `scripts/check_aarch64_mc.sh` will fail. To restore the machine-code proofs: update `Arm64/Code.lean` from the new objects, rerun `scripts/gen_aarch64_short_paths.py` to regenerate the 96 short-length lemmas, and repair the six hand-structured proofs by hand. Do this once per settled binary, not per tuning step.
- `reports/phase1.md` … `phase7.md` record what was tried, including what failed.

---

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

