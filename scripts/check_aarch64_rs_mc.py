#!/usr/bin/env python3
"""Checks that the instruction words proven in ReedSolomon/Arm64/Apply.lean
(`applyWords`) are exactly the bytes of `leanrs_apply` in the assembled object
build/cxx/leanrs_apply_arm64.o, that nothing else is in its text section
except alignment padding, and that the object has no relocations (the routine
is position-independent and calls nothing)."""
import re
import subprocess
import sys

OBJ = "build/cxx/leanrs_apply_arm64.o"
LEAN = "ReedSolomon/Arm64/Apply.lean"
SYM = "leanrs_apply"
NOP = 0xD503201F


def run(*cmd):
    return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout


m = re.search(r"def applyWords : Array UInt32 := #\[(.*?)\]", open(LEAN).read(), re.S)
if not m:
    sys.exit(f"FAIL: applyWords not found in {LEAN}")
want = [int(w, 16) for w in re.findall(r"0x[0-9a-fA-F]{8}", m.group(1))]

dis = run("objdump", "-d", OBJ)
words = {int(a, 16): int(w, 16)
         for a, w in re.findall(r"^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s", dis, re.M)}
syms = {name.lstrip("_"): int(addr, 16)
        for addr, name in re.findall(r"^([0-9a-f]+) T (\S+)$", run("nm", OBJ), re.M)}
if SYM not in syms:
    sys.exit(f"FAIL: {SYM} is not a defined text symbol in {OBJ}")
covered = set()
for i, w in enumerate(want):
    addr = syms[SYM] + 4 * i
    if words.get(addr) != w:
        sys.exit(f"FAIL: {SYM}+{4 * i:#x}: object has {words.get(addr)}, proven word is {w:#010x}")
    covered.add(addr)
extra = [a for a, w in words.items() if a not in covered and w != NOP]
if extra:
    sys.exit(f"FAIL: {OBJ} has unproven non-padding words at {[hex(a) for a in extra]}")
if re.search(r"ARM64_RELOC|R_AARCH64", run("objdump", "-r", OBJ)):
    sys.exit(f"FAIL: {OBJ} has relocations")
print(f"OK: {len(want)} proven instruction words of {SYM} match {OBJ}, no relocations")
