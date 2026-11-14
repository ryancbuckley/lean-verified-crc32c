#!/usr/bin/env python3
"""Authoritative Arm cross-check, step 1: produce test vectors from Arm's
machine-readable ASL by executing the real A64 opcodes in ASLp (UQ-PAC/aslp).

Untrusted glue: it only drives ASLp and reformats its output. The vectors are
checked against the Lean models by tests/AslCheck.lean.

Usage: aslp_vectors.py <path-to-aslp-checkout> <random-cases-per-opcode> > vectors.txt
Output lines:  <name> <x> <y> <result>      (decimal; for pmull, result = lo hi)
"""
import subprocess, sys, random

OPCODES = {  # assembled with clang: op w0, w1, w2 / pmull v0.1q, v1.1d, v2.1d
    "crc32c_u8": 0x1AC25020,   # crc32cb w0, w1, w2
    "crc32c_u16": 0x1AC25420,  # crc32ch w0, w1, w2
    "crc32c_u32": 0x1AC25820,  # crc32cw w0, w1, w2
    "crc32c_u64": 0x9AC25C20,  # crc32cx w0, w1, x2
    "pmull": 0x0EE2E020,       # pmull v0.1q, v1.1d, v2.1d
}
M64 = (1 << 64) - 1

def cases(n, rng):
    edge = [0, M64, 0xAAAAAAAAAAAAAAAA, 0x5555555555555555, 0x00000000FFFFFFFF,
            0xFFFFFFFF00000000, 0x0123456789ABCDEF, 0x8000000000000001, 1, 1 << 63, 1 << 31, 1 << 32]
    out = [(x, y) for x in edge for y in edge]
    out += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(n)]
    return out

def main():
    aslp, n = sys.argv[1], int(sys.argv[2])
    rng = random.Random(20261114)
    plan, script = [], [":init globals", ":init regs",
                        # the 64x64->128 PMULL form is an optional feature; our targets have it
                        ':set impdef "Has 128-bit form of PMULL instructions" = TRUE']
    for name, op in OPCODES.items():
        for x, y in cases(n, rng):
            if name == "pmull":
                # upper halves are random junk: PMULL (not PMULL2) must ignore them
                jx, jy = rng.getrandbits(64), rng.getrandbits(64)
                script += [f"_Z[1] = 0x{(jx << 64) | x:032x}[127:0];", f"_Z[2] = 0x{(jy << 64) | y:032x}[127:0];",
                           f":opcode A64 0x{op:08x}", "_Z[0]"]
            else:
                # upper 32 bits of the accumulator register are junk the instruction must ignore
                jx = rng.getrandbits(32)
                script += [f"_R[1] = 0x{(jx << 32) | (x & 0xFFFFFFFF):016x}[63:0];", f"_R[2] = 0x{y:016x}[63:0];",
                           f":opcode A64 0x{op:08x}", "_R[0]"]
            plan.append((name, x, y))
    script.append(":quit")
    res = subprocess.run(["dune", "exec", "asli"], cwd=aslp, input="\n".join(script) + "\n",
                         capture_output=True, text=True)
    if "Error" in res.stdout or "Error" in res.stderr:
        bad = [l for l in (res.stdout + res.stderr).splitlines() if "Error" in l]
        sys.exit("ASLp reported errors:\n" + "\n".join(bad[:5]))
    vals = [int(l.split("'")[1], 2) for l in res.stdout.splitlines()
            if l.startswith("64'") or l.startswith("128'")]
    if len(vals) != len(plan):
        sys.exit(f"expected {len(plan)} results from ASLp, got {len(vals)}\n{res.stderr[-2000:]}")
    width = {"crc32c_u8": 8, "crc32c_u16": 16, "crc32c_u32": 32, "crc32c_u64": 64}
    for (name, x, y), v in zip(plan, vals):
        if name == "pmull":
            print(name, x, y, v & M64, v >> 64)
        else:
            print(name, x & 0xFFFFFFFF, y & ((1 << width[name]) - 1), v)

main()
