#!/usr/bin/env python3
"""Generates MemcpyCrc32c/Arm64/ExtendHwRawShort.lean.

`_lp_leanmemcpy_Crc32c_extendHwRaw___redArg` handles lengths 0..95 with a
loop-free, heavily tail-merged decision tree (420 of its 427 instructions).
For a fixed length the path through that tree is fixed, so this script traces
the path for each of the 96 lengths and emits one Lean lemma per length that
steps the Arm64 model along it.

Nothing here is trusted. The script only chooses which instruction index to
step next and which rewriting facts to hand to `simp`; every step is checked by
Lean against the decoded instruction words in `Code.lean`, and a wrong trace
simply fails to compile.

Input: the disassembly of the linked test binary (`build/cxx/test_c_abi`,
built by `scripts/check_aarch64_mc.sh`), read through `llvm-objdump`.

Usage: python3 scripts/gen_aarch64_short_paths.py
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / "build" / "cxx" / "test_c_abi"
SYMBOL = "_lp_leanmemcpy_Crc32c_extendHwRaw___redArg"
OUT = ROOT / "MemcpyCrc32c" / "Arm64" / "ExtendHwRawShort.lean"


def disassemble():
    text = subprocess.run(
        ["xcrun", "llvm-objdump", "-d", "--no-show-raw-insn", str(BINARY)],
        check=True, capture_output=True, text=True).stdout
    ins, on = [], False
    for line in text.splitlines():
        if line.startswith("0") and line.rstrip().endswith(f"<{SYMBOL}>:"):
            on = True
            continue
        if on:
            m = re.match(r"^\s*[0-9a-f]+:\s+(.*)$", line)
            if not m:
                break
            ins.append(m.group(1).split(";")[0].strip())
    if len(ins) != 427:
        sys.exit(f"expected 427 instructions for {SYMBOL}, found {len(ins)}")
    return ins


def target(t):
    return int(re.search(r"\+0x([0-9a-f]+)>", t).group(1), 16) // 4


def imm(s):
    return int(s.strip().lstrip("#"), 0)


def trace(ins, n):
    """Returns (indices stepped, facts for simp, loads, absorbed chunks)."""
    x = {"x2": n, "x3": None, "x9": None}
    x1off = -0x18          # data offset of the address held in x1
    pc, flags = 0, None
    steps, facts, loads, absorbed = [], [], {}, []
    pend = {}              # register -> (width, data offset) of the value it holds

    def fact(stmt):
        if stmt not in facts:
            facts.append(stmt)

    while True:
        t = ins[pc]
        op, _, rest = t.partition("\t")
        a = [s.strip() for s in rest.split(",")]
        nxt = pc + 1
        steps.append(pc)
        if op == "ret":
            return steps, facts, loads, absorbed
        if op == "mov" and a[0] == "x3":
            x["x3"] = x["x2"]
        elif op == "mov" and a[0] == "w9":
            v = imm(a[1])
            x["x9"] = v
            fact(f"(({v} : UInt16).toUInt32 <<< (0 : Nat).toUInt32).toUInt64 = {v}")
        elif op in ("mvn", "mov"):
            pass
        elif op == "cmp":
            flags = (x[a[0]], imm(a[1]))
        elif op in ("sub", "subs"):
            if op == "subs":
                flags = (x[a[1]], imm(a[2]))
            x[a[0]] = (x[a[1]] - imm(a[2])) % 2**64
        elif op == "and":
            m = imm(a[2]) if a[2].startswith("#") else x[a[2]]
            r = x[a[1]] & m
            fact(f"({x[a[1]]} : UInt64) &&& {m} = {r}")
            x[a[0]] = r
        elif op.startswith("b."):
            p, q = flags
            c = op[2:]
            taken = {"hi": p > q, "ls": p <= q, "eq": p == q, "ne": p != q}[c]
            if c == "eq":
                fact(f"(({p} : UInt64) == {q}) = {str(p == q).lower()}")
            elif c == "ne":
                fact(f"(({p} : UInt64) != {q}) = {str(p != q).lower()}")
            if taken:
                nxt = target(t)
        elif op == "cbz":
            z = x[a[0]] == 0
            fact(f"((({x[a[0]]} : UInt64) == 0) != false) = {str(z).lower()}")
            if z:
                nxt = target(t)
        elif op == "b":
            nxt = target(t)
        elif op in ("ldrb", "ldrh", "ldr", "ldp"):
            m = re.search(r"\[x1, #0x([0-9a-f]+)\](!?)", rest)
            d = int(m.group(1), 16)
            off = x1off + d
            if op == "ldp":
                for k, r in enumerate(a[:2]):
                    pend[r] = (8, off + 8 * k)
                    loads[(8, off + 8 * k)] = True
                    if r == "x9":
                        x["x9"] = None
                if m.group(2):
                    x1off += d
            else:
                w = {"ldrb": 1, "ldrh": 2, "ldr": 8 if a[0].startswith("x") else 4}[op]
                pend["x" + a[0][1:]] = (w, off)
                loads[(w, off)] = True
                if a[0][1:] == "9":
                    x["x9"] = None
        elif op == "orr":
            lo, hi = pend["x" + a[1][1:]], pend["x" + a[2][1:]]
            assert lo[0] == 1 and hi == (1, lo[1] + 1), (n, pc)
            pend["x9"] = (2, lo[1])
        elif op.startswith("crc32c"):
            w = {"b": 1, "h": 2, "w": 4, "x": 8}[op[-1]]
            src = pend["x" + a[2][1:]]
            assert src[0] == w, (n, pc)
            absorbed.append(src)
        else:
            sys.exit(f"unhandled instruction at {pc}: {t}")
        pc = nxt


HEADER = '''/-
GENERATED by scripts/gen_aarch64_short_paths.py. Do not edit by hand.

Machine-code verification of the loop-free `0..95`-byte paths of
`_lp_leanmemcpy_Crc32c_extendHwRaw___redArg` (420 of its 427 instructions):
one lemma per length, each stepping the Arm64 model along the fixed path the
compiled decision tree takes for that length. Every path is frameless: it
writes no memory, reads only payload bytes `[0, n)`, and returns to `X30` with
all registers other than `X0`, `X1`, `X3`, `X8`, `X9`, `X10` and the flags
unchanged.

The generator is not trusted: it only picks the instruction indices and the
rewriting facts, and Lean checks each step against `Code.lean`.
-/
import MemcpyCrc32c.Arm64.RawExtendHwMulti

set_option linter.unusedSimpArgs false

namespace Crc32c.Arm64MC
open SimdModels

/-- What the machine code must do when entered with length `n` in `X2`. -/
def ShortSpec (n : Nat) : Prop :=
  ∀ {code : UInt64 → Option UInt32} {L : CodeLayout} {s : Arm64.ArmState} {objPtr : UInt64}
    {data : ByteArray} (_hs : data.size < USize.size) {c : UInt32},
    CodeLoaded code s.mem L → s.mem.hasROBytes (objPtr + 0x18) data →
    s.pc = L.extendHwRawBase → s.getW r0 = c → s.regs.x1 = objPtr →
    s.regs.x2 = n.toUInt64 → n ≤ data.size →
    ∃ k s', Arm64.run code k s = some s' ∧ s'.pc = s.regs.x30 ∧
      s'.getW r0 = Crc32c.rawExtend (c ^^^ 0xFFFFFFFF) (Crc32c.bytes data 0 n) ^^^ 0xFFFFFFFF ∧
      s'.mem = s.mem ∧ CalleeSaved s s'

private theorem ro_addr (p d : UInt64) (k : Nat) (h : d = 0x18 + k.toUInt64) :
    p + d = (p + 0x18) + k.toUInt64 := by rw [h, UInt64.add_assoc]

private theorem xor_ones_cancel (c : UInt32) : (c ^^^ 0xFFFFFFFF) ^^^ 0xFFFFFFFF = c := by
  rw [UInt32.xor_assoc]; simp

local macro "ms" hc:ident idx:num "[" extras:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| mc_step_ex_with step_extendHwRaw $hc $idx extendHwRawInsn
     [UInt64.reduceLT, UInt64.reduceLE, UInt64.reduceAdd, UInt64.reduceSub, $extras,*])
'''

READ = {1: "ro_readU8 ({a}) hro {k} (by omega)",
        2: "ro_readU16 ({a}) hro {k} (by omega)",
        4: "ro_readU32 ({a}) hro {k} (by omega)",
        8: "ro_readU64 ({a}) hro hs {k} (by omega)"}
ABSORB = {1: "rawExtend_u8_fin data {k} {n} (by omega) hn",
          2: "rawExtend_u16_fin data hs {k} {n} (by omega) hn",
          4: "rawExtend_u32_fin data hs {k} {n} (by omega) hn",
          8: "rawExtend_u64_fin data hs {k} {n} (by omega) hn"}


def lemma(ins, n):
    steps, facts, loads, absorbed = trace(ins, n)
    pos = 0
    for w, off in absorbed:
        assert off == pos, (n, absorbed)
        pos += w
    assert pos == n, (n, absorbed)
    o = []
    o.append("set_option maxRecDepth 8192 in")
    o.append(f"theorem short_{n} : ShortSpec {n} := by")
    o.append("  intro code L s objPtr data hs c hc hro hpc hw0 hx1 hx2 hn")
    o.append("  rcases s with ⟨regs, sp, simd, nzcv, pc, mem⟩")
    o.append("  dsimp only at hc hro hpc hx1 hx2")
    o.append("  dsimp only [getW_mk_r0] at hw0")
    o.append("  subst hpc")
    o.append(f"  have hx2 : regs.x2 = {n} := hx2")
    names = ["hx2"]
    for i, f in enumerate(facts):
        o.append(f"  have hf{i} : {f} := rfl")
        names.append(f"hf{i}")
    for (w, k) in loads:
        addr = f"regs.x1 + {0x18 + k}"
        o.append(f"  have hl{w}_{k} := " + READ[w].format(a=addr, k=k)
                 + " (by rw [hx1]; exact ro_addr _ _ _ rfl)")
        names.append(f"hl{w}_{k}")
    extras = ", ".join(names)
    for idx in steps:
        o.append(f"  ms hc {idx} [{extras}]")
    o.append("  refine ⟨0, _, Arm64.run_zero _ _, rfl, ?_, rfl,")
    o.append("    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,")
    o.append("     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩")
    rws = [ABSORB[w].format(k=k, n=n) for (w, k) in absorbed]
    rws.append("Crc32c.bytes_of_le data (Nat.le_refl _)")
    o.append("  rw [" + ",\n    ".join(rws) + "]")
    if n == 0:
        o.append("  simp only [Arm64.ArmState.getW, Arm64.RegFile.get]")
        o.append("  rw [hw0]")
        o.append("  exact (xor_ones_cancel c).symm")
    else:
        o.append("  simp only [Arm64.ArmState.getW, Arm64.RegFile.get, toUInt32_toUInt64,")
        o.append("    nat_toUInt32_8, toUInt16_reassemble2, toUInt16_reassemble2_comm]")
        o.append("  rw [hw0]")
        o.append("  rfl")
    return "\n".join(o) + "\n"


def main():
    ins = disassemble()
    only = [int(v) for v in sys.argv[1:]] or range(96)
    parts = [HEADER]
    for n in only:
        parts.append(lemma(ins, n))
    if not sys.argv[1:]:
        parts.append("/-- Every length below 96 is covered. -/\n"
                     "theorem short_all (n : Nat) (hn : n < 96) : ShortSpec n := by\n"
                     "  interval_cases n\n  exacts ["
                     + ",\n    ".join(", ".join(f"short_{n}" for n in range(r, r + 8))
                                      for r in range(0, 96, 8))
                     + "]\n")
    parts.append("end Crc32c.Arm64MC\n")
    OUT.write_text("\n".join(parts))
    print(f"wrote {OUT.relative_to(ROOT)} ({len(only)} lengths)")


if __name__ == "__main__":
    main()
