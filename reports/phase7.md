# Phase 7 report: AArch64 machine-code verification (stretch)

Status: done for the hardware CRC32C call graph on AArch64 (Apple M4 build).
All seven functions reachable from `extendHwRaw`, 1,137 instructions, are
proven against the frozen Phase 1 specification at the level of the compiled
instruction words. Nothing has been done for x86-64, for the portable path,
or for the C++ wrapper and dispatch.

## What is proven

Headline, `MemcpyCrc32c/Arm64/ExtendHwRaw.lean`:

`extendHwRaw_mc_spec`. Take any machine state whose program counter is at the
entry of `_lp_leancrc32c_Crc32c_extendHwRaw___redArg`, with the seven
functions and their constants loaded, a read-only payload `a` at
`objPtr + 0x18`, 0x160 bytes of writable stack below `SP`, `W0 = c`,
`X1 = objPtr`, `X2 = len` and `len ≤ a.size`. Then the model runs to the
return address in `X30` and:

- `W0 = Crc32c.Spec.extend c (a.extract 0 len)`, the Phase 1 polynomial spec;
- memory outside `[SP - 0x160, SP)` is unchanged, and every read-only and
  every unmapped byte is preserved;
- `SP`, `X19..X30` and `D8..D15` are preserved (AAPCS64).

The model's step function fails on a read of an unmapped byte or a write to a
byte that is not writable, so the theorem also shows the code reads nothing
but the payload, its constants and its own stack. `extendHwRaw_short_mc_spec`
strengthens this for `len < 96`: no stack is required and no memory is
written. `extendHwRaw_mc_eq_lean` states the same result against the Lean
function `Crc32c.extendHwRaw`.

| Function | Instructions | Theorem | File |
| --- | ---: | --- | --- |
| `combine3` | 44 | `combine3_mc_spec` | `Arm64/Combine.lean` |
| `combine6` | 65 | `combine6_mc_spec` | `Arm64/Combine.lean` |
| `hwLoop` | 99 | `hwLoop_mc_spec` | `Arm64/HwLoop.lean` |
| `hwFold6Loop` | 197 | `hwFold6Loop_mc_spec` | `Arm64/HwFold6.lean` |
| `hwFold6` | 186 | `hwFold6_mc_spec` | `Arm64/HwFold6.lean` |
| `rawExtendHwMulti` | 119 | `rawExtendHwMulti_mc_spec` | `Arm64/RawExtendHwMulti.lean` |
| `extendHwRaw` | 427 | `extendHwRaw_mc_spec` | `Arm64/ExtendHwRaw.lean`, `Arm64/ExtendHwRawShort.lean` |

`MemcpyCrc32c/Arm64.lean` runs `#print axioms` under `#guard_msgs` on all of
these: each depends only on `propext`, `Classical.choice`, `Quot.sound`. No
`sorry`, `bv_decide` or `native_decide`. `Spec.lean` is unchanged. Build with
`lake build MemcpyCrc32c.Arm64`; the default target does not include these
modules. The generated module alone takes about four minutes to check.

## How the last function was done

The first six functions were proven by hand-structured symbolic execution
(Gemini's work, reviewed and rebuilt here). `extendHwRaw` is different: for
`len < 96` the compiler emitted a loop-free decision tree of 420 instructions
with heavily merged tails, in which the same instruction serves different
lengths with different base pointers. A symbolic proof over `len` would have
to rediscover that merging.

Instead, each length gets its own lemma. For a fixed length the path is fixed,
so `scripts/gen_aarch64_short_paths.py` traces the path for each of the 96
lengths (3,337 steps in total) and emits `Arm64/ExtendHwRawShort.lean`: one
lemma per length that steps the model along the path and rewrites the result
into `rawExtend`. `short_all` combines them. The generator is not trusted: it
only chooses which instruction index to step next and which facts to give
`simp`, and a wrong trace fails to compile. The 96 paths together execute all
420 instructions of the tree.

For `96 ≤ len` the function pushes a 0x10-byte frame and calls
`rawExtendHwMulti`; that case composes `rawExtendHwMulti_mc_spec` with the
frame's save and restore.

## What this removes from the trusted base, and what remains

For the hardware path on this binary, the theorem no longer relies on Lean's
code generator, on clang, or on the C shim's instruction bindings (`crc32c_*`,
`clmul*`, `loadU8`, `loadU64LE`): the proof is about the instructions that
were emitted.

Still trusted:

1. **The A64 model** (`lean-simd-models/SimdModels/Arm64.lean`): decoder and
   step function for the instructions used. Checked against Arm's ASL through
   ASLp on 3,017 full-state vectors covering all 873 distinct instruction
   words of the seven functions; see `lean-simd-models/validation/README.md`
   for the limits of that check.
2. **That the proven words are the binary.**
   `scripts/check_aarch64_mc.sh` compares `Arm64/Code.lean` byte for byte
   with the object files, the static archive and a linked test binary,
   including 7 branch relocations and 20 GOT-load pairs. The script is
   trusted; it passes on the current build.
3. **The loading hypotheses.** `CodeLoaded` and `GlobalsLoaded` are assumed,
   not derived from a model of the loader. In particular the eleven constants
   and the shift table are assumed to hold the values of the Lean
   definitions; at run time they are written by Lean's module initializer,
   which is not verified here. No Lean term instantiates these hypotheses for
   a concrete memory image, so their joint satisfiability rests on the
   script in item 2 and on inspection.
4. **The calling contract.** The wrapper must enter with the registers as
   stated and 0x160 bytes of stack. The C++ wrapper, the CPU-feature
   dispatch, `extendRaw`, and the copy are compiled code outside this proof.
5. Lean's kernel.

The model has no notion of interrupts, other threads, or self-modifying
code (`code` is separate from data memory).

## Corrections to the handed-over summary

- The summary named a C++ harness `lean-simd-models/c/asl_check.cpp`. No such
  file exists; the check is `tests/AslArm64Check.lean` with
  `validation/aslp_arm64_vectors.py`.
- "192,000+ checks" is not a figure I could reproduce. The check runs 3,017
  full-state vectors.
- There is no top-level `README.md` to update.

## Fragility

These proofs are about one binary. Any change to the kernel, to compiler
flags, or to the compiler version changes the instruction words, and
`check_aarch64_mc.sh` will then fail until `Code.lean` and the affected
proofs are redone. `ExtendHwRawShort.lean` can be regenerated; the other six
proofs are hand-structured and would need manual repair. Retuning for other
AArch64 cores or adding x86-64 kernels should therefore come before any
further machine-code work.
