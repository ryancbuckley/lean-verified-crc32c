#!/usr/bin/env python3
"""Checks that the instruction words proven in MemcpyCrc32c/Arm64/Copy.lean
(`copyWords`) are exactly the bytes of `leancrc32c_copy_large` in the assembled
object build/cxx/leancrc32c_copy_arm64.o, and that the object has no
relocations (the routine is position-independent and calls nothing)."""
import re
import subprocess
import sys

OBJ = "build/cxx/leancrc32c_copy_arm64.o"
lean = open("MemcpyCrc32c/Arm64/Copy.lean").read()
m = re.search(r"def copyWords : Array UInt32 := #\[(.*?)\]", lean, re.S)
if not m:
    sys.exit("FAIL: copyWords not found in Copy.lean")
proven = [int(w, 16) for w in re.findall(r"0x[0-9a-fA-F]{8}", m.group(1))]

dis = subprocess.run(["objdump", "-d", OBJ], check=True, capture_output=True, text=True).stdout
actual = [int(x, 16) for x in re.findall(r"^\s*[0-9a-f]+:\s+([0-9a-f]{8})\s", dis, re.M)]
# the assembler may pad the section to its alignment with trailing nops
while len(actual) > len(proven) and actual[-1] == 0xD503201F:
    actual.pop()
if actual != proven:
    sys.exit(f"FAIL: {OBJ} has {len(actual)} words that differ from the {len(proven)} proven words")

rel = subprocess.run(["objdump", "-r", OBJ], check=True, capture_output=True, text=True).stdout
if re.search(r"ARM64_RELOC|R_AARCH64", rel):
    sys.exit(f"FAIL: {OBJ} has relocations")

syms = subprocess.run(["nm", OBJ], check=True, capture_output=True, text=True).stdout
if not re.search(r"\bT _?leancrc32c_copy_large$", syms, re.M):
    sys.exit("FAIL: leancrc32c_copy_large is not a defined text symbol")
print(f"OK: {len(proven)} proven instruction words match {OBJ}, no relocations")
