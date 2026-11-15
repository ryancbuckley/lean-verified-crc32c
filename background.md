# Background: Fast CRCs and How We Prove Them Correct

This document explains the core ideas behind `lean-verified-crc32c` in plain terms—no background in coding theory, SIMD assembly, or theorem provers assumed. Once you have the mental models below, [README.md](README.md) and the source files should be straightforward to follow.

---

## 1. What CRC32C and `MemcpyCrc32c` Are

When storage engines, filesystems, databases, or RPC frameworks move data, they want a fast way to catch accidental bit flips from disks, network links, or memory buses. A **CRC** (*Cyclic Redundancy Check*) is a deterministic 32-bit digest of a byte buffer designed specifically for error detection (not cryptographic security against an attacker).

**CRC32C** (the *Castagnoli* CRC, standardized in iSCSI, ext4, Btrfs, RocksDB, Ceph, and Google's Abseil) is the dominant CRC in modern infrastructure because Intel, AMD, and Arm CPUs build dedicated instructions for it directly into hardware.

In practice, programs often need to **copy a buffer** and **compute its CRC32C** back-to-back, plus manipulate checksums without re-reading the original bytes:

- `ExtendCrc32c` / `ComputeCrc32c`: checksum a buffer (or extend an existing checksum with more bytes).
- `MemcpyCrc32c`: copy `count` bytes from `src` to `dest` and return their CRC32C.
- **CRC algebra** (`Concat`, `RemovePrefix`, `RemoveSuffix`, `ExtendByZeroes`): given the checksums and byte lengths of two buffers, compute the checksum of their concatenation—or strip off a known prefix or suffix—in microseconds using math on the 32-bit checksums alone.

---

## 2. Why a Checksum Is Secretly Polynomial Division

The cleanest way to understand every CRC trick in this repository is to view a sequence of bits as a polynomial whose coefficients are only `0` or `1` (written $\mathbb{F}_2[X]$ in math notation):

$$\texttt{1011}_2 \;\longleftrightarrow\; 1\cdot X^3 + 0\cdot X^2 + 1\cdot X^1 + 1$$

Arithmetic on these polynomials follows ordinary high-school algebra with one twist—**coefficients wrap around modulo 2, so there are never any carries**:

- **Addition and subtraction are both bitwise XOR (`^`).** Adding `1 + 1` gives `0` with no carry into the next bit, so `+` and `-` are identical.
- **Multiplying by $X^k$ is shifting left by $k$ bits.**
- **Multiplying two polynomials is "carry-less multiplication"** (`CLMUL` / `PMULL` on ARM, `PCLMULQDQ` on x86): the same shift-and-add pattern as integer multiplication, except the partial products are **XORed** instead of added.

With that dictionary, **computing a 32-bit CRC is just polynomial long division** of your message polynomial $M(X)$ (shifted up by $X^{32}$) by a fixed degree-32 **generator polynomial** $G(X)$, keeping the 32-bit **remainder**. (Standard CRC32C also reverses the bit order within each byte—a "reflected" CRC—and flips all 32 bits with `0xFFFFFFFF` on entry and exit so that adding leading or trailing zero bytes changes the checksum.)

### Why this matters
Polynomial remainder modulo $G(X)$ is **linear over XOR**:

$$(A(X) \oplus B(X)) \bmod G(X) \;=\; (A(X) \bmod G(X)) \;\oplus\; (B(X) \bmod G(X))$$

Every single optimization in fast CRC code comes from this one equation: you can break a message into pieces, shift or fold pieces independently, XOR the partial results back together, and get the **exact same 32-bit remainder** as if you had divided the whole buffer one bit at a time.

---

## 3. How Fast CRC Algorithms Avoid Bit-by-Bit Division

The textbook CRC loop shifts a 32-bit register by one bit, checks the outgoing bit, and conditionally XORs in $G(X)$. It is tiny and obviously faithful to the definition, but horribly slow: every bit must wait for the previous bit's result.

`lean-verified-crc32c` uses three progressively wider techniques—all proven to compute the exact same remainder modulo $G(X)$:

### Lookup Tables (*Slicing-by-8*)
Instead of stepping 1 bit at a time, precompute a small table (`8 × 256` entries = 8 KiB) storing the 32-bit remainders of every possible byte value at 8 consecutive byte positions. Processing an 8-byte word becomes 8 table lookups XORed together. This has zero startup math, making it ideal for very short buffers on CPUs without CRC instructions.

### Zero-Polynomial (*Chorba*) Reduction (Portable Register Path)
Suppose you find a polynomial $Z(X)$ that is an **exact multiple** of $G(X)$—so $Z(X) \bmod G(X) = 0$ (a *zero polynomial*)—and also happens to have **very few `1` bits** (say, only 6 terms out of 210 bits).

Because $Z(X)$ has remainder `0`, XORing any multiple $W(X) \cdot X^k \cdot Z(X)$ into your message **leaves the final CRC completely unchanged**. You can use the top term of $Z(X)$ to cancel an entire 64-bit message word at once, paying only 5 shifted XORs into a sliding window of four 64-bit integer registers ahead of you—no special CPU instructions and no lookup-table memory reads required!

*(A neat quirk of CRC32C: its generator $G(X)$ has 18 nonzero terms, an even number, which means $X + 1$ divides $G(X)$ and **every** multiple of $G(X)$ must also have an even number of terms. That is why the smallest sparse multiple for CRC32C has 6 terms, whereas standard gzip CRC32 has 3-term and 5-term multiples.)*

Running 4 independent streams of this reduction side-by-side in general-purpose registers lets the CPU overlap the shift-and-XOR steps, then recombines the 4 stream checksums at the end.

### Hardware `CRC32C` + Carry-Less Multiply Folding
Even when a CPU has a dedicated 64-bit `CRC32C` instruction, a single instruction takes ~3 clock cycles to finish, so feeding one buffer sequentially leaves most of the CPU idle waiting on that dependency chain. Fast hardware kernels break that limit in two ways:

1. **Multi-stream `CRC32C`:** Split the buffer into 3 (or more) contiguous stripes, run independent `CRC32C` accumulators on all stripes simultaneously so the CPU pipelines them in parallel, and algebraically combine the stripe checksums at the end using multiplication modulo $G(X)$.
2. **Carry-less multiply (`CLMUL`) folding:** Instead of reducing down to 32 bits on every word, multiply 128-bit chunks by precomputed constants $X^k \bmod G(X)$ using SIMD carry-less multiply instructions (`PMULL` / `PCLMULQDQ`) and XOR them into wide vector accumulators. On modern cores, integer `CRC32C` instructions and vector `CLMUL` instructions run on **different execution units**, so a hybrid loop running both streams at once keeps both pipelines busy.

---

## 4. What Formal Verification in Lean 4 Means

In ordinary software engineering, you write a slow 20-line reference CRC, write a fast 500-line parallel kernel, and run millions of random tests hoping no edge case (say, buffer length `95`, or a carry-over across stream boundaries) was missed.

**Lean 4** is both a compiled programming language and an interactive **proof assistant**. In Lean:

1. **You write a short, readable specification (`MemcpyCrc32c/Spec.lean`, 44 lines)** defining CRC32C directly as polynomial remainder modulo $G(X)$, and check it against official standard test vectors.
2. **You write the fast executable code (`MemcpyCrc32c/Impl/`),** using lookup tables, zero polynomials, multi-stream loops, and inline hardware instructions.
3. **You write mathematical proofs (`MemcpyCrc32c/*.lean`)** showing that for **all** `c : UInt32` and **all** `a : ByteArray`—not just tested samples, but every mathematically possible input—the fast code returns the exact same `UInt32` as `Spec.extend c a`. Lean's small proof-checking core (*the kernel*) checks every logical step and rejects the build if any case is left unproven (`sorry`).

Three design patterns make this practical for low-level systems code:

- **Compile-time bounds proofs (*proof erasure*).** Safe array reads normally compile to runtime bounds checks (`if i < size`), which prevent loading 8 bytes in a single instruction. In Lean, a load helper can require a *proof argument* (`h : off + 8 ≤ a.size`). Lean verifies at compile time that every caller proves its offset is in bounds, then **erases the proof completely** before generating C—producing raw, check-free machine loads that are mathematically guaranteed to stay inside the array.
- **No external SAT-solver axioms.** Some proof tools outsource bit-twiddling goals to external SAT solvers (`bv_decide`), adding solver/compiler certificates to what you must trust. Every bit-vector and polynomial proof in this repository is checked directly inside Lean's kernel using only Lean's three standard mathematical axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **`opaque` CPU feature probes.** At runtime, the library asks the CPU whether hardware CRC/CLMUL instructions exist. Declaring that check `opaque` in Lean prevents any proof from assuming whether it returns `true` or `false`, forcing both the hardware path and the portable path to satisfy the exact same theorem.

---

## 5. Source-Level Proofs vs. Machine-Code Proofs (and What You Still Trust)

Every verification project has a **Trusted Computing Base (TCB)**: the small set of things that are *assumed* rather than *proven*, where a bug could still break the guarantee. Understanding the two proof layers in this repo comes down to seeing what each layer removes from the TCB:

### Layer A: Source-Level Verification (`MemcpyCrc32c/*.lean`)
Proves that the Lean programs equal `Spec.lean`.
- **No longer trusted:** All CRC math—lookup tables, zero-polynomial bit shifts, multi-stream splitting/recombining, magic constants, and short-buffer edge cases.
- **Still trusted when running from C/C++:**
  1. **Lean's kernel** and the 44-line `Spec.lean` definition.
  2. **Compilers:** Lean's C code generator and the C compiler (`clang`) that compile the Lean code.
  3. **Hardware instruction bindings (`lean-simd-models/`):** Lean cannot see inside silicon, so hardware instructions (`CRC32C`, `CLMUL`) and raw unaligned loads are modeled as pure Lean bit-vector functions wired to tiny inline C intrinsics. To make sure those models match reality, we cross-check them against **Arm's official machine-readable Architecture Specification Language (ASL)** (executed via the **ASLp** interpreter), against Intel's manual pseudocode, and across millions of randomized runs on real hardware.
  4. **The thin C/C++ wrapper (`cxx/leancrc32c.cc`):** Borrows raw C caller pointers without copying or allocating, copies `src` to `dest`, and calls into Lean. Because C pointer rules around alignment and object headers are subtle, this boundary is checked with static C call-graph audits, hardware `PROT_NONE` guard pages, and `100M+` sanitizer-instrumented fuzz runs.

### Layer B: Binary Machine-Code Verification (`MemcpyCrc32c/Arm64/`)
Even with source-level proofs, a bug in Lean's compiler, `clang -O2`, or our inline C intrinsics could emit buggy assembly.

For the compiled AArch64 hardware CRC32C call graph (`7` functions, `1,137` 32-bit ARM instructions), we go one step further: we extract the **exact 32-bit instruction words** from the compiled `.o` / `.a` binary, decode and step them inside a Lean model of the ARM64 CPU (`SimdModels/Arm64.lean`, covering registers, condition flags, stack pointer, and byte-by-byte read/write memory permissions), and prove that running those machine instructions from entry to `ret` returns `Spec.extend`, preserves ABI callee-saved registers, and faults on—hence provably never performs—any out-of-bounds or header memory access.

- **Removed from the TCB:** Lean's compiler, `clang -O2`, and the C intrinsic/load shims for those functions.
- **The trade-off:** Source-level proofs survive performance retuning and compiler upgrades; machine-code proofs are tied to **one exact compiled binary** and must be redone whenever a kernel change or compiler flag alters the emitted instructions. And even at the binary level, you still trust Lean's kernel, `Spec.lean`, the ARM64 instruction model (validated against Arm's ASL), the script that checks the binary bytes on disk match the numbers in the proof, Lean's startup initialization of constant tables, and the outer C++ wrapper.
