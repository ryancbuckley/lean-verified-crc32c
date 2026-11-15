#!/usr/bin/env python3
"""Authoritative Arm ASL cross-check for SimdModels.Arm64 (Phase 7).

Executes real 32-bit A64 instruction words in ASLp (UQ-PAC/aslp) against Arm's
machine-readable Architecture Specification Language (ASL), capturing full
architectural state transitions (PC, SP, PSTATE.{N,Z,C,V}, X0..X30, V0..V31, and
a 384-byte RAM window [0x20000, 0x20180)) for:
  1. All unique compiled A64 instruction words across the 7 verified functions
     in Hw.c.o, HwCombine.c.o, and linked test_c_abi (including both taken and
     untaken states for every conditional branch), and
  2. Systematic architectural edge-case vectors across all 19 opcode families
     modeled in SimdModels/Arm64.lean (all 256 CSEL cond x NZCV combinations,
     signed/unsigned AddWithCarry boundaries, DecodeBitMasks element sizes,
     W-register and D/8B-register upper-half zeroing, INS lane preservation,
     SP vs XZR/WZR, V31, pre/post/signed-offset LDP/STP, LDR/STR, CRC32C,
     PMULL, EOR3, EXT, ZIP2).

Checked against SimdModels.Arm64.step by lean-simd-models/tests/AslArm64Check.lean.

Usage:
  python3 aslp_arm64_vectors.py <asli.exe-or-aslp-dir> [objdump-file ...] > vectors.txt
"""
import os
import random
import re
import subprocess
import sys

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
M128 = (1 << 128) - 1
MEM_BASE = 0x20000
MEM_WORDS = 48  # 384 bytes: [0x20000, 0x20180), pointer base = 0x20080
PTR_BASE = 0x20080
INIT_PC = 0x10004124


def canary_x(i):
    return (0xA5A5000000000100 + i) & M64


def canary_v(i):
    lo = (0x5A5A000000000200 + i) & M64
    hi = (0xC3C3000000000300 + i) & M64
    return lo | (hi << 64)


def canary_mem_word(k):
    return (0xD00D000000000000 + k * 0x0102030405060708) & M64


def classify_mem(w):
    """Return ('none' | 'load' | 'store' | 'load_reg', rn) for memory setup."""
    rn = (w >> 5) & 0x1F
    if (w & 0x3A000000) == 0x28000000:
        is_load = (w >> 22) & 1
        return ("load" if is_load else "store", rn)
    if (w & 0x3B000000) == 0x39000000:
        simd = (w >> 26) & 1
        opc = (w >> 22) & 3
        if not simd and opc == 0:
            return ("store", rn)
        return ("load", rn)
    if (w & 0x3FE0FC00) == 0x38606800:
        return ("load_reg", rn)
    return ("none", rn)


def is_cond_branch(w):
    return (w & 0xFF000010) == 0x54000000 or (w & 0x7E000000) == 0x34000000


def enc_str_x_uimm(rt, rn, word_idx):
    # STR Xt, [Xn, #(word_idx * 8)] : 11 111 0 01 00 imm12 Rn Rt
    return 0xF9000000 | ((word_idx & 0xFFF) << 10) | ((rn & 31) << 5) | (rt & 31)


def enc_ldr_x_uimm(rt, rn, word_idx):
    # LDR Xt, [Xn, #(word_idx * 8)] : 11 111 0 01 01 imm12 Rn Rt
    return 0xF9400000 | ((word_idx & 0xFFF) << 10) | ((rn & 31) << 5) | (rt & 31)


EDGE64 = [
    0, 1, 2, 7, 15, 16, 31, 32, 63, 64,
    0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x100000000,
    0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF,
    0x0123456789ABCDEF, 0xFEDCBA9876543210,
    0xAAAAAAAAAAAAAAAA, 0x5555555555555555,
]


def rand_val64(rng):
    if rng.random() < 0.45:
        return rng.choice(EDGE64)
    return rng.getrandbits(64)


def make_cases_for_opcode(w, rng, n_rand=2):
    """Build pre-state override dicts for opcode w."""
    rd = w & 0x1F
    rn = (w >> 5) & 0x1F
    ra = (w >> 10) & 0x1F
    rm = (w >> 16) & 0x1F
    mem_kind, mem_rn = classify_mem(w)

    cases = []
    if (w & 0xFF000010) == 0x54000000:
        # B.cond: test across several NZCV values to hit both taken & untaken
        for nzcv in [0b0000, 0b0100, 0b0010, 0b1001, 0b1000, 0b0110]:
            cases.append({"nzcv": nzcv, "pc": INIT_PC + rng.choice([0, 4, 0x120])})
        return cases
    if (w & 0x7E000000) == 0x34000000:
        # CBZ / CBNZ: test zero, zero-in-low-32-only, and non-zero
        for val in [0, 0x1234567800000000, 1, 0x8000000000000005]:
            ov = {"pc": INIT_PC}
            if rd < 31:
                ov[f"x{rd}"] = val
            cases.append(ov)
        return cases

    for _ in range(n_rand):
        ov = {"nzcv": rng.randrange(16), "pc": INIT_PC + rng.choice([0, 0x40, 0xFF8])}
        for r in {rd, rn, ra, rm}:
            if r < 31:
                ov[f"x{r}"] = rand_val64(rng)
            ov[f"v{r}"] = rng.getrandbits(128)
        if mem_kind != "none":
            aligned_off = rng.choice([-16, 0, 16, 32])
            base = PTR_BASE + aligned_off
            if mem_rn == 31:
                ov["sp"] = base
            else:
                ov[f"x{mem_rn}"] = base
            if mem_kind == "load_reg":
                if rm < 31:
                    if rm == mem_rn:
                        ov[f"x{rm}"] = PTR_BASE
                    else:
                        # ASLp's built-in RAM stub aligns multi-byte PhysMemRead
                        sz_bits = (w >> 30) & 3
                        step = 1 << sz_bits
                        ov[f"x{rm}"] = rng.randrange(0, 48 // step) * step
        cases.append(ov)
    return cases


def build_synthetic_suite(rng):
    """Construct systematic edge-case tests across all 19 opcode families."""
    tests = []  # list of (opcode_u32, override_dict)

    # 1. CSEL: all 16 cond x all 16 NZCV states (both W and X)
    for cond in range(16):
        w_x = 0x9A820020 | (cond << 12)  # csel x0, x1, x2, cond
        w_w = 0x1A820020 | (cond << 12)  # csel w0, w1, w2, cond
        for nzcv in range(16):
            ov = {
                "nzcv": nzcv,
                "x0": 0xDEADBEEFCAFEBABE,
                "x1": 0x1111222233334444,
                "x2": 0x9999AAAABBBBCCCC,
            }
            tests.append((w_x, ov))
            if (cond + nzcv) % 2 == 0:
                tests.append((w_w, ov))

    # 2. AddWithCarry / SUBS / ADDS / CMP / ADD / SUB (imm & shifted reg, SP & XZR)
    alu_ops = [
        0xEB020020,  # subs x0, x1, x2
        0x6B020020,  # subs w0, w1, w2
        0xAB020020,  # adds x0, x1, x2
        0x2B020020,  # adds w0, w1, w2
        0xEB02003F,  # cmp x1, x2 (rd = xzr)
        0x6B02003F,  # cmp w1, w2 (rd = wzr)
        0x8B822020,  # add x0, x1, x2, asr #8
        0x4B421820,  # sub w0, w1, w2, lsr #6
        0x910043FF,  # add sp, sp, #16
        0xD101C3FF,  # sub sp, sp, #0x70
        0x91401020,  # add x0, x1, #4, lsl #12
        0xF100043F,  # cmp x1, #1
        0x7100043F,  # cmp w1, #1
    ]
    boundary_pairs = [
        (0, 0), (0, 1), (1, 0), (1, 1),
        (0x7FFFFFFF, 1), (0x80000000, 1), (0xFFFFFFFF, 1), (0xFFFFFFFF, 0xFFFFFFFF),
        (0x7FFFFFFFFFFFFFFF, 1), (0x8000000000000000, 1),
        (0xFFFFFFFFFFFFFFFF, 1), (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF),
        (0xF000000080000000, 0xF000000080000000),
    ]
    for w in alu_ops:
        for x, y in boundary_pairs[:8]:
            tests.append((w, {"x0": 0xFFFFFFFF12345678, "x1": x, "x2": y, "sp": PTR_BASE}))

    # 3. Logical immediate (DecodeBitMasks across esize=2,4,8,16,32,64) & Logical reg
    logic_ops = [
        0x92400020,  # and x0, x1, #1
        0x92403C20,  # and x0, x1, #0xffff
        0xB2000020,  # orr x0, x1, #0x5555555555555555 (esize=2)
        0xD2010420,  # eor x0, x1, mask
        0xF240003F,  # tst x1, #1
        0x7200003F,  # tst w1, #1
        0x12001C20,  # and w0, w1, #0xff
        0xAA2203E0,  # mvn x0, x2 (orn x0, xzr, x2)
        0x2A2203E0,  # mvn w0, w2
        0xAA024020,  # orr x0, x1, x2, lsl #16
        0xCA823020,  # eor x0, x1, x2, asr #12
        0x8AC22C20,  # and x0, x1, x2, ror #11
        0x0AC22C20,  # and w0, w1, w2, ror #11
        0xEA020020,  # ands x0, x1, x2
        0x6A020020,  # ands w0, w1, w2
    ]
    for w in logic_ops:
        for _ in range(4):
            tests.append((w, {"x0": rand_val64(rng), "x1": rand_val64(rng), "x2": rand_val64(rng)}))

    # 4. MOVZ / MOVN / MOVK & UBFM & MADD / UMULH & Branches / ADRP
    misc_ops = [
        0xD2855560,  # movz x0, #0x2aab
        0x52855560,  # movz w0, #0x2aab (zeros upper 32!)
        0x92800020,  # movn x0, #1
        0x12800020,  # movn w0, #1 (zeros upper 32!)
        0xF2BACCA0,  # movk x0, #0xd665, lsl #16
        0x72BACCA0,  # movk w0, #0xd665, lsl #16 (zeros upper 32!)
        0xD355FC20,  # lsr x0, x1, #21 (ubfm imms >= immr)
        0xD37DF020,  # lsl x0, x1, #3  (ubfm imms < immr)
        0x53057C20,  # lsr w0, w1, #5
        0x531B6820,  # lsl w0, w1, #5
        0x9B027C20,  # mul x0, x1, x2 (madd ra=xzr)
        0x9B020C20,  # madd x0, x1, x2, x3
        0x1B020C20,  # madd w0, w1, w2, w3
        0x9BC27C20,  # umulh x0, x1, x2
        0x14000015,  # b +0x54
        0x17FFFFEC,  # b -0x50
        0x94000020,  # bl +0x80
        0xD65F03C0,  # ret x30
        0x90000008,  # adrp x8, 0
        0xF0FFFFE8,  # adrp x8, -0x1000
    ]
    for w in misc_ops:
        for _ in range(4):
            tests.append((w, {
                "x0": rand_val64(rng), "x1": rand_val64(rng),
                "x2": rand_val64(rng), "x3": rand_val64(rng),
                "x30": 0x10008888, "pc": INIT_PC + rng.choice([0, 0x7FC]),
            }))

    # 5. CRC32C & SIMD / Crypto / Transfers (including WZR and V31!)
    simd_ops = [
        0x1AC25020,  # crc32cb w0, w1, w2
        0x1AC25420,  # crc32ch w0, w1, w2
        0x1AC25820,  # crc32cw w0, w1, w2
        0x9AC25C20,  # crc32cx w0, w1, x2
        0x9AC25FE0,  # crc32cx w0, wzr, x2 (WZR accumulator!)
        0x0EE2E020,  # pmull v0.1q, v1.1d, v2.1d
        0x0EFFE3FF,  # pmull v31.1q, v31.1d, v31.1d (V31 is real, not zero!)
        0x2E221C20,  # eor v0.8b, v1.8b, v2.8b (must zero upper 64!)
        0x6E221C20,  # eor v0.16b, v1.16b, v2.16b
        0xCE020C20,  # eor3 v0.16b, v1.16b, v2.16b, v3.16b
        0x6E020020,  # ext v0.16b, v1.16b, v2.16b, #0
        0x6E020820,  # ext v0.16b, v1.16b, v2.16b, #1
        0x6E024020,  # ext v0.16b, v1.16b, v2.16b, #8
        0x6E027820,  # ext v0.16b, v1.16b, v2.16b, #15
        0x4EC27820,  # zip2 v0.2d, v1.2d, v2.2d
        0x9E660020,  # fmov x0, d1
        0x9E670020,  # fmov d0, x1 (must zero upper 64 of v0!)
        0x4E083C20,  # umov x0, v1.d[0]
        0x4E183C20,  # umov x0, v1.d[1]
        0x4E081C20,  # ins v0.d[0], x1 (must preserve v0.d[1]!)
        0x4E181C20,  # ins v0.d[1], x1 (must preserve v0.d[0]!)
        0x6E080420,  # ins v0.d[0], v1.d[0]
        0x6E084420,  # ins v0.d[0], v1.d[1]
        0x6E180420,  # ins v0.d[1], v1.d[0]
        0x6E184420,  # ins v0.d[1], v1.d[1]
        0x6E180400,  # ins v0.d[1], v0.d[0] (in-place lane copy!)
    ]
    for w in simd_ops:
        for _ in range(5):
            tests.append((w, {
                "x0": rand_val64(rng), "x1": rand_val64(rng), "x2": rand_val64(rng),
                "v0": rng.getrandbits(128), "v1": rng.getrandbits(128),
                "v2": rng.getrandbits(128), "v3": rng.getrandbits(128),
                "v31": rng.getrandbits(128),
            }))

    # 6. Memory loads & stores (GP & SIMD, pre-index, post-index, signed-offset, reg)
    mem_ops = [
        0xA9BF0BE1,  # stp x1, x2, [sp, #-16]!
        0xA8C10BE1,  # ldp x1, x2, [sp], #16
        0xA9010BE1,  # stp x1, x2, [sp, #16]
        0xA9410BE1,  # ldp x1, x2, [sp, #16]
        0x29020BE1,  # stp w1, w2, [sp, #16]
        0x29420BE1,  # ldp w1, w2, [sp, #16] (zeros upper 32 of x1, x2!)
        0x6DBF0BE1,  # stp d1, d2, [sp, #-16]!
        0x6CC10BE1,  # ldp d1, d2, [sp], #16 (zeros upper 64 of v1, v2!)
        0x6D410BE1,  # ldp d1, d2, [sp, #16]
        0x390013E1,  # strb w1, [sp, #4]
        0x394013E1,  # ldrb w1, [sp, #4]
        0x790013E1,  # strh w1, [sp, #8]
        0x794013E1,  # ldrh w1, [sp, #8]
        0xB90013E1,  # str w1, [sp, #16]
        0xB94013E1,  # ldr w1, [sp, #16]
        0xF9000BE1,  # str x1, [sp, #16]
        0xF9400BE1,  # ldr x1, [sp, #16]
        0xFD400BE1,  # ldr d1, [sp, #16]
        0x3DC00BE1,  # ldr q1, [sp, #32]
        0x38626820,  # ldrb w0, [x1, x2]
        0x78626820,  # ldrh w0, [x1, x2]
    ]
    for w in mem_ops:
        for k in range(3):
            is_ldrh_reg = w == 0x78626820
            tests.append((w, {
                "sp": PTR_BASE + k * 16,
                "x0": rand_val64(rng), "x1": PTR_BASE if (w & 0x3FE0FC00) == 0x38606800 else rand_val64(rng),
                "x2": (rng.randrange(0, 16) * (2 if is_ldrh_reg else 1)) if (w & 0x3FE0FC00) == 0x38606800 else rand_val64(rng),
                "v1": rng.getrandbits(128), "v2": rng.getrandbits(128),
            }))

    return tests


def extract_objdump_opcodes(paths):
    opcodes = set()
    for p in paths:
        with open(p) as f:
            for line in f:
                m = re.match(r"^\s*[0-9a-f]+:\s+([0-9a-f]{8})\s+", line)
                if m:
                    opcodes.add(int(m.group(1), 16))
    return sorted(opcodes)


def main():
    if len(sys.argv) < 2:
        sys.exit("Usage: aslp_arm64_vectors.py <asli.exe-or-aslp-dir> [disasm.txt ...]")
    aslp_arg = sys.argv[1]
    disasm_files = sys.argv[2:]
    rng = random.Random(20261115)

    all_tests = []
    obj_opcodes = extract_objdump_opcodes(disasm_files)
    for w in obj_opcodes:
        for ov in make_cases_for_opcode(w, rng, n_rand=2):
            all_tests.append((w, ov))
    all_tests.extend(build_synthetic_suite(rng))

    # Build a single batch script for ASLp
    script = [
        ":init globals",
        ":init regs",
        ':set impdef "Has 128-bit form of PMULL instructions" = TRUE',
        ':set impdef "Has SHA1 Crypto instructions" = TRUE',
        ':set impdef "Has SHA256 Crypto instructions" = TRUE',
        ':set impdef "Has SHA3 Crypto instructions" = TRUE',
        f"_R[29] = 0x{MEM_BASE:016x}[63:0];",
    ]
    # Initialize all 48 memory words [0x20000, 0x20180) using STR X30, [X29, #k*8]
    for k in range(MEM_WORDS):
        script.append(f"_R[30] = 0x{canary_mem_word(k):016x}[63:0];")
        script.append(f":opcode A64 0x{enc_str_x_uimm(30, 29, k):08x}")
    # Initialize canary GP & SIMD registers
    for i in range(31):
        script.append(f"_R[{i}] = 0x{canary_x(i):016x}[63:0];")
    for i in range(32):
        script.append(f"_Z[{i}] = 0x{canary_v(i):032x}[127:0];")

    plans = []
    for w, ov in all_tests:
        rd = w & 0x1F
        rn = (w >> 5) & 0x1F
        ra = (w >> 10) & 0x1F
        rm = (w >> 16) & 0x1F
        mem_kind, mem_rn = classify_mem(w)

        pc_in = ov.get("pc", INIT_PC)
        sp_in = ov.get("sp", PTR_BASE)
        nzcv_in = ov.get("nzcv", 0)
        n_b = (nzcv_in >> 3) & 1
        z_b = (nzcv_in >> 2) & 1
        c_b = (nzcv_in >> 1) & 1
        v_b = nzcv_in & 1

        script.append(f"_PC = 0x{pc_in:016x}[63:0];")
        script.append(f"SP_EL0 = 0x{sp_in:016x}[63:0];")
        script.append(f"PSTATE.N = 0x{n_b}[0:0];")
        script.append(f"PSTATE.Z = 0x{z_b}[0:0];")
        script.append(f"PSTATE.C = 0x{c_b}[0:0];")
        script.append(f"PSTATE.V = 0x{v_b}[0:0];")
        script.append("__BranchTaken = FALSE;")

        touched_x = set()
        touched_v = set()
        for k, val in ov.items():
            if k.startswith("x"):
                idx = int(k[1:])
                touched_x.add(idx)
                script.append(f"_R[{idx}] = 0x{val:016x}[63:0];")
            elif k.startswith("v"):
                idx = int(k[1:])
                touched_v.add(idx)
                script.append(f"_Z[{idx}] = 0x{val:032x}[127:0];")

        # Execute the real A64 opcode!
        script.append(f":opcode A64 0x{w:08x}")

        # Query post-state from ASLp
        query_gp = sorted({r for r in [rd, rn, ra, rm, 30] if r < 31})
        query_simd = sorted({r for r in [rd, rn, ra, rm, 31]})
        script.extend(["__BranchTaken", "_PC", "SP_EL0", "PSTATE.N", "PSTATE.Z", "PSTATE.C", "PSTATE.V"])
        for r in query_gp:
            script.append(f"_R[{r}]")
        for r in query_simd:
            script.append(f"_Z[{r}]")

        # If this instruction stored to memory, read back the affected 8-byte words
        mem_check_words = []
        if mem_kind == "store":
            # Conservatively inspect [0x20000, 0x20180) around PTR_BASE: words 0..47?
            # We know base is around PTR_BASE (word 16), offsets in [-16..+32] words -> check words 0..47?
            # Checking 6 words around the base is plenty! Compute exact base_val:
            base_val = sp_in if mem_rn == 31 else ov.get(f"x{mem_rn}", canary_x(mem_rn))
            # Offsets in our binary/tests are within [-112, +200] bytes
            w_lo = max(0, ((base_val - 128) - MEM_BASE) // 8)
            w_hi = min(MEM_WORDS - 1, ((base_val + 208) - MEM_BASE) // 8)
            # Even tighter: compute exact address range from instruction!
            if (w & 0x3A000000) == 0x28000000:
                imm7 = (w >> 15) & 0x7F
                if imm7 & 0x40:
                    imm7 -= 0x80
                opc = (w >> 30) & 3
                simd_p = (w >> 26) & 1
                scale = 3 if (simd_p or opc == 2) else 2
                mode = (w >> 23) & 7
                addr = base_val if mode == 1 else (base_val + (imm7 << scale))
                w_lo = (addr - MEM_BASE) // 8
                w_hi = min(MEM_WORDS - 1, w_lo + 2)
            elif (w & 0x3B000000) == 0x39000000:
                sz = (w >> 30) & 3
                imm12 = (w >> 10) & 0xFFF
                addr = base_val + (imm12 << sz)
                w_lo = (addr - MEM_BASE) // 8
                w_hi = min(MEM_WORDS - 1, w_lo + 1)
            mem_check_words = list(range(max(0, w_lo), min(MEM_WORDS, w_hi + 1)))
            script.append(f"_R[29] = 0x{MEM_BASE:016x}[63:0];")
            for mw in mem_check_words:
                script.append(f":opcode A64 0x{enc_ldr_x_uimm(30, 29, mw):08x}")
                script.append("_R[30]")
            # Restore modified memory words to canary values
            for mw in mem_check_words:
                script.append(f"_R[30] = 0x{canary_mem_word(mw):016x}[63:0];")
                script.append(f":opcode A64 0x{enc_str_x_uimm(30, 29, mw):08x}")
            touched_x.update([29, 30])

        # Restore any potentially modified registers back to canary state
        for r in touched_x | set(query_gp):
            script.append(f"_R[{r}] = 0x{canary_x(r):016x}[63:0];")
        for r in touched_v | set(query_simd):
            script.append(f"_Z[{r}] = 0x{canary_v(r):032x}[127:0];")

        plans.append((w, ov, pc_in, sp_in, nzcv_in, query_gp, query_simd, mem_check_words))

    script.append(":quit")

    if os.path.isdir(aslp_arg):
        cmd = ["dune", "exec", "asli"]
        cwd = aslp_arg
    else:
        cmd = [aslp_arg]
        cwd = None

    res = subprocess.run(cmd, cwd=cwd, input="\n".join(script) + "\n", capture_output=True, text=True)
    if "Error" in res.stdout or "Error" in res.stderr or "Parser error" in res.stdout:
        bad = [l for l in (res.stdout + res.stderr).splitlines() if "Error" in l or "Parser error" in l]
        sys.exit("ASLp reported errors:\n" + "\n".join(bad[:10]))

    tokens = []
    for l in res.stdout.splitlines():
        s = l.strip()
        if s in ("TRUE", "FALSE") or s.startswith("1'") or s.startswith("64'") or s.startswith("128'"):
            tokens.append(s)

    idx = 0

    def next_bool():
        nonlocal idx
        t = tokens[idx]
        idx += 1
        if t in ("TRUE", "1'1'"):
            return True
        if t in ("FALSE", "1'0'"):
            return False
        raise ValueError(f"bad bool token: {t}")

    def next_bits():
        nonlocal idx
        t = tokens[idx]
        idx += 1
        return int(t.split("'")[1], 2)

    for w, ov, pc_in, sp_in, nzcv_in, query_gp, query_simd, mem_check_words in plans:
        br_taken = next_bool()
        raw_pc = next_bits()
        post_pc = raw_pc if br_taken else ((pc_in + 4) & M64)
        post_sp = next_bits()
        pn = 1 if next_bool() else 0
        pz = 1 if next_bool() else 0
        pc_f = 1 if next_bool() else 0
        pv = 1 if next_bool() else 0
        post_nzcv = (pn << 3) | (pz << 2) | (pc_f << 1) | pv

        gp_vals = {r: next_bits() for r in query_gp}
        simd_vals = {r: next_bits() for r in query_simd}
        mem_vals = {mw: next_bits() for mw in mem_check_words}

        # Format pre overrides
        pre_items = [f"pc={pc_in}", f"sp={sp_in}", f"nzcv={nzcv_in}"]
        for k in sorted(ov.keys()):
            if k in ("pc", "sp", "nzcv"):
                continue
            val = ov[k]
            if k.startswith("v"):
                pre_items.append(f"{k}={val & M64}:{val >> 64}")
            else:
                pre_items.append(f"{k}={val}")

        # Format post overrides (relative to pre-state!)
        post_items = [f"pc={post_pc}", f"sp={post_sp}", f"nzcv={post_nzcv}"]
        for r, val in gp_vals.items():
            pre_v = ov.get(f"x{r}", canary_x(r))
            if val != pre_v:
                post_items.append(f"x{r}={val}")
        for r, val in simd_vals.items():
            pre_v = ov.get(f"v{r}", canary_v(r))
            if val != pre_v:
                post_items.append(f"v{r}={val & M64}:{val >> 64}")
        for mw, val in mem_vals.items():
            if val != canary_mem_word(mw):
                post_items.append(f"m{mw}={val}")

        print(f"{w} | {' '.join(pre_items)} | {' '.join(post_items)}")

    if idx != len(tokens):
        sys.exit(f"token count mismatch: consumed {idx} of {len(tokens)}")


if __name__ == "__main__":
    main()
