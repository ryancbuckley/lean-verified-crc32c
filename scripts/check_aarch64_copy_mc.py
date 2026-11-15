#!/usr/bin/env python3
"""Checks that the instruction words proven in MemcpyCrc32c/Arm64/Copy.lean
(`copyWords`) and CopySmall.lean (`copySmallWords`) are exactly the bytes of
`leancrc32c_copy_large` and `leancrc32c_copy_small` in the assembled object
build/cxx/leancrc32c_copy_arm64.o, that nothing else is in its text section
except alignment padding, and that the object has no relocations (both
routines are position-independent and call nothing)."""
import re
import subprocess
import sys

OBJ = "build/cxx/leancrc32c_copy_arm64.o"
NOP = 0xD503201F


def proven(path, name):
    lean = open(path).read()
    m = re.search(r"def %s : Array UInt32 := #\[(.*?)\]" % name, lean, re.S)
    if not m:
        sys.exit(f"FAIL: {name} not found in {path}")
    return [int(w, 16) for w in re.findall(r"0x[0-9a-fA-F]{8}", m.group(1))]


def run(*cmd):
    return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout


dis = run("objdump", "-d", OBJ)
words = {int(a, 16): int(w, 16)
         for a, w in re.findall(r"^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s", dis, re.M)}
syms = {name.lstrip("_"): int(addr, 16)
        for addr, name in re.findall(r"^([0-9a-f]+) T (\S+)$", run("nm", OBJ), re.M)}

covered = set()
total = 0
for sym, path, name in [
    ("leancrc32c_copy_large", "MemcpyCrc32c/Arm64/Copy.lean", "copyWords"),
    ("leancrc32c_copy_small", "MemcpyCrc32c/Arm64/CopySmall.lean", "copySmallWords"),
]:
    if sym not in syms:
        sys.exit(f"FAIL: {sym} is not a defined text symbol in {OBJ}")
    want = proven(path, name)
    for i, w in enumerate(want):
        addr = syms[sym] + 4 * i
        if words.get(addr) != w:
            sys.exit(f"FAIL: {sym}+{4 * i:#x}: object has {words.get(addr)}, proven word is {w:#010x}")
        covered.add(addr)
    total += len(want)

extra = [a for a, w in words.items() if a not in covered and w != NOP]
if extra:
    sys.exit(f"FAIL: {OBJ} has unproven non-padding words at {[hex(a) for a in extra]}")
if re.search(r"ARM64_RELOC|R_AARCH64", run("objdump", "-r", OBJ)):
    sys.exit(f"FAIL: {OBJ} has relocations")
print(f"OK: {total} proven instruction words (2 routines) match {OBJ}, no relocations")
