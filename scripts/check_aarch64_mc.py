#!/usr/bin/env python3
"""
Mach-O 64-bit AArch64 binary audit for Phase 7 (`MemcpyCrc32c/Arm64/Code.lean`).

Verifies byte-for-byte and relocation-for-relocation equality between the
machine-code specification in `MemcpyCrc32c/Arm64/Code.lean` and:
  1. Compiled Mach-O object files (`HwCombine.c.o`, `Hw.c.o`),
  2. Static library archive members (`build/cxx/libleancrc32c.a`), and
  3. Linked Mach-O executable (`build/cxx/test_c_abi`), checking that every
     unrelocated 32-bit word is identical, every `ARM64_RELOC_BRANCH26` (`bl`/`b`)
     targets the exact linked callee virtual address, and every
     `ARM64_RELOC_GOT_LOAD_PAGE21`/`PAGEOFF12` pair resolves (via GOT slot or
     Apple `ld` `adrp + add` relaxation) to the exact linked global address.

Can also dump raw `.o` words and relocations via `--dump-json` for generating
`MemcpyCrc32c/Arm64/Code.lean`.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import struct
import sys
from typing import Dict, List, Tuple

MH_MAGIC_64 = 0xFEEDFACF
CPU_TYPE_ARM64 = 0x0100000C
LC_SEGMENT_64 = 0x19
LC_SYMTAB = 0x02

ARM64_RELOC_BRANCH26 = 2
ARM64_RELOC_GOT_LOAD_PAGE21 = 5
ARM64_RELOC_GOT_LOAD_PAGEOFF12 = 6

MASK64 = (1 << 64) - 1

FUNCTIONS = [
    ("combine3", "HwCombine.c.o", "_lp_leancrc32c_Crc32c_combine3"),
    ("combine6", "HwCombine.c.o", "_lp_leancrc32c_Crc32c_combine6"),
    ("hwLoop", "Hw.c.o", "_lp_leancrc32c_Crc32c_hwLoop___redArg"),
    ("hwFold6Loop", "Hw.c.o", "_lp_leancrc32c_Crc32c_hwFold6Loop___redArg"),
    ("hwFold6", "Hw.c.o", "_lp_leancrc32c_Crc32c_hwFold6___redArg"),
    ("rawExtendHwMulti", "Hw.c.o", "_lp_leancrc32c_Crc32c_rawExtendHwMulti___redArg"),
    ("extendHwRaw", "Hw.c.o", "_lp_leancrc32c_Crc32c_extendHwRaw___redArg"),
]

SYM_TO_ID = {
    "_lp_leancrc32c_Crc32c_combine3": "fnCombine3",
    "_lp_leancrc32c_Crc32c_combine6": "fnCombine6",
    "_lp_leancrc32c_Crc32c_hwLoop___redArg": "fnHwLoop",
    "_lp_leancrc32c_Crc32c_hwFold6Loop___redArg": "fnHwFold6Loop",
    "_lp_leancrc32c_Crc32c_hwFold6___redArg": "fnHwFold6",
    "_lp_leancrc32c_Crc32c_rawExtendHwMulti___redArg": "fnRawExtendHwMulti",
    "_lp_leancrc32c_Crc32c_extendHwRaw___redArg": "fnExtendHwRaw",
    "_lp_leancrc32c_Crc32c_hwOne": "gHwOne",
    "_lp_leancrc32c_Crc32c_hwX64": "gHwX64",
    "_lp_leancrc32c_Crc32c_hwShiftSmallBytes": "gHwShiftSmallBytes",
    "_lp_leancrc32c_Crc32c_kFold128__1": "gKFold128_1",
    "_lp_leancrc32c_Crc32c_kFold128__2": "gKFold128_2",
    "_lp_leancrc32c_Crc32c_kFold256__1": "gKFold256_1",
    "_lp_leancrc32c_Crc32c_kFold256__2": "gKFold256_2",
    "_lp_leancrc32c_Crc32c_kFold384__1": "gKFold384_1",
    "_lp_leancrc32c_Crc32c_kFold384__2": "gKFold384_2",
    "_lp_leancrc32c_Crc32c_kFold512__1": "gKFold512_1",
    "_lp_leancrc32c_Crc32c_kFold512__2": "gKFold512_2",
}
ID_TO_SYM = {v: k for k, v in SYM_TO_ID.items()}


def sign_extend(val: int, bits: int) -> int:
    sign_bit = 1 << (bits - 1)
    mask = (1 << bits) - 1
    v = val & mask
    return (v | (~mask & MASK64)) if (v & sign_bit) else v


class MachO64:
    def __init__(self, data: bytes, label: str):
        self.data = data
        self.label = label
        if len(data) < 32:
            raise ValueError(f"{label}: truncated Mach-O header")
        magic, cputype, _, self.filetype, ncmds, _, _, _ = struct.unpack_from(
            "<IIIIIIII", data, 0
        )
        if magic != MH_MAGIC_64 or cputype != CPU_TYPE_ARM64:
            raise ValueError(
                f"{label}: expected ARM64 Mach-O 64, got magic={hex(magic)} cpu={hex(cputype)}"
            )
        self.segments: List[Tuple[str, int, int, int, int]] = []
        self.sections: List[dict] = []
        symoff = nsyms = stroff = 0
        off = 32
        sect_idx = 0
        for _ in range(ncmds):
            cmd, cmdsize = struct.unpack_from("<II", data, off)
            if cmd == LC_SEGMENT_64:
                segname = data[off + 8 : off + 24].split(b"\x00", 1)[0].decode()
                vmaddr, vmsize, fileoff, filesize, _, _, nsects, _ = struct.unpack_from(
                    "<QQQQIIII", data, off + 24
                )
                self.segments.append((segname, vmaddr, vmsize, fileoff, filesize))
                soff = off + 72
                for _ in range(nsects):
                    sect_idx += 1
                    sectname = data[soff : soff + 16].split(b"\x00", 1)[0].decode()
                    sseg = data[soff + 16 : soff + 32].split(b"\x00", 1)[0].decode()
                    (
                        saddr,
                        ssize,
                        sfileoff,
                        _,
                        srelocoff,
                        snreloc,
                        _,
                        _,
                        _,
                        _,
                    ) = struct.unpack_from("<QQIIIIIIII", data, soff + 32)
                    self.sections.append(
                        {
                            "index": sect_idx,
                            "seg": sseg,
                            "sect": sectname,
                            "addr": saddr,
                            "size": ssize,
                            "fileoff": sfileoff,
                            "relocoff": srelocoff,
                            "nreloc": snreloc,
                        }
                    )
                    soff += 80
            elif cmd == LC_SYMTAB:
                symoff, nsyms, stroff, _ = struct.unpack_from("<IIII", data, off + 8)
            off += cmdsize

        self.syms: List[Tuple[str, int, int, int]] = []
        self.def_syms: Dict[str, Tuple[int, int]] = {}
        for i in range(nsyms):
            n_strx, n_type, n_sect, _, n_value = struct.unpack_from(
                "<IBBHQ", data, symoff + i * 16
            )
            end = data.index(b"\x00", stroff + n_strx)
            name = data[stroff + n_strx : end].decode()
            self.syms.append((name, n_type, n_sect, n_value))
            if (n_type & 0x0E) == 0x0E:
                self.def_syms[name] = (n_sect, n_value)

    def get_text_section(self) -> dict:
        for s in self.sections:
            if s["seg"] == "__TEXT" and s["sect"] == "__text":
                return s
        raise ValueError(f"{self.label}: missing __TEXT,__text section")

    def extract_function(self, sym_name: str) -> dict:
        text = self.get_text_section()
        if sym_name not in self.def_syms:
            raise ValueError(f"{self.label}: missing symbol {sym_name}")
        sect, start = self.def_syms[sym_name]
        if sect != text["index"]:
            raise ValueError(f"{self.label}: {sym_name} not in __TEXT,__text")
        boundaries = sorted(
            {
                val
                for nm, tp, sc, val in self.syms
                if (tp & 0x0E) == 0x0E
                and sc == text["index"]
                and not nm.startswith("ltmp")
            }
            | {text["addr"] + text["size"]}
        )
        end = next(b for b in boundaries if b > start)
        if (end - start) % 4 != 0:
            raise ValueError(f"{self.label}: {sym_name} size not multiple of 4")
        foff_start = text["fileoff"] + (start - text["addr"])
        nwords = (end - start) // 4
        words = list(struct.unpack_from(f"<{nwords}I", self.data, foff_start))

        # Parse relocations inside [start, end)
        raw_relocs = []
        for r in range(text["nreloc"]):
            r_address, r_info = struct.unpack_from(
                "<iI", self.data, text["relocoff"] + r * 8
            )
            abs_addr = text["addr"] + r_address
            if start <= abs_addr < end:
                if (abs_addr - start) % 4 != 0:
                    raise ValueError(
                        f"{self.label}: unaligned relocation in {sym_name} at {hex(abs_addr)}"
                    )
                r_sym = r_info & 0xFFFFFF
                r_pcrel = (r_info >> 24) & 1
                r_len = (r_info >> 25) & 3
                r_ext = (r_info >> 27) & 1
                r_type = (r_info >> 28) & 0xF
                if r_ext != 1 or r_len != 2:
                    raise ValueError(
                        f"{self.label}: unexpected reloc flags ext={r_ext} len={r_len} in {sym_name}"
                    )
                target = self.syms[r_sym][0]
                raw_relocs.append(((abs_addr - start) // 4, r_type, r_pcrel, target))

        raw_relocs.sort(key=lambda x: x[0])
        branches = []
        gots = []
        i = 0
        while i < len(raw_relocs):
            idx, r_type, r_pcrel, target = raw_relocs[i]
            if target not in SYM_TO_ID:
                raise ValueError(
                    f"{self.label}: unexpected relocation target {target} in {sym_name}"
                )
            sym_id = SYM_TO_ID[target]
            if r_type == ARM64_RELOC_BRANCH26:
                if r_pcrel != 1:
                    raise ValueError(f"{self.label}: non-pcrel BRANCH26 in {sym_name}")
                w = words[idx]
                if w == 0x94000000:
                    is_call = True
                elif w == 0x14000000:
                    is_call = False
                else:
                    raise ValueError(
                        f"{self.label}: unexpected BRANCH26 template {hex(w)} in {sym_name}"
                    )
                branches.append({"idx": idx, "isCall": is_call, "target": sym_id})
                i += 1
            elif r_type == ARM64_RELOC_GOT_LOAD_PAGE21:
                if i + 1 >= len(raw_relocs):
                    raise ValueError(f"{self.label}: unpaired GOT_LOAD_PAGE21 in {sym_name}")
                idx2, r_type2, r_pcrel2, target2 = raw_relocs[i + 1]
                if (
                    idx2 != idx + 1
                    or r_type2 != ARM64_RELOC_GOT_LOAD_PAGEOFF12
                    or r_pcrel != 1
                    or r_pcrel2 != 0
                    or target2 != target
                ):
                    raise ValueError(
                        f"{self.label}: malformed GOT_LOAD pair at idx {idx} in {sym_name}"
                    )
                w0, w1 = words[idx], words[idx + 1]
                rd = w0 & 0x1F
                if (
                    (w0 & 0x9F000000) != 0x90000000
                    or (w1 & 0xFFC00000) != 0xF9400000
                    or (w1 & 0x1F) != rd
                    or ((w1 >> 5) & 0x1F) != rd
                    or rd == 31
                ):
                    raise ValueError(
                        f"{self.label}: unexpected GOT_LOAD words {hex(w0)}, {hex(w1)} in {sym_name}"
                    )
                gots.append({"idx": idx, "rd": rd, "target": sym_id})
                i += 2
            else:
                raise ValueError(
                    f"{self.label}: unsupported relocation type {r_type} at idx {idx} in {sym_name}"
                )

        return {
            "start": start,
            "end": end,
            "words": words,
            "branches": branches,
            "gots": gots,
        }

    def read_vaddr_u64(self, va: int) -> int:
        for _, vmaddr, _, fileoff, filesize in self.segments:
            if vmaddr <= va <= vmaddr + filesize - 8:
                return struct.unpack_from("<Q", self.data, fileoff + (va - vmaddr))[0]
        raise ValueError(f"{self.label}: unmapped file-backed u64 at {hex(va)}")


def extract_ar_members(ar_path: pathlib.Path) -> Dict[str, bytes]:
    data = ar_path.read_bytes()
    if data[:8] != b"!<arch>\n":
        raise ValueError(f"{ar_path}: not a BSD/Unix ar archive")
    members: Dict[str, bytes] = {}
    pos = 8
    while pos < len(data):
        hdr = data[pos : pos + 60]
        name = hdr[:16].decode("ascii", errors="replace").strip()
        size = int(hdr[48:58].decode("ascii").strip())
        body = data[pos + 60 : pos + 60 + size]
        if name.startswith("#1/"):
            nlen = int(name[3:])
            real_name = body[:nlen].rstrip(b"\x00").decode("utf-8")
            payload = body[nlen:]
        else:
            real_name = name.rstrip("/")
            payload = body
        members[real_name] = payload
        pos += 60 + size + (size & 1)
    return members


def parse_code_lean(lean_path: pathlib.Path) -> Dict[str, dict]:
    text = lean_path.read_text()
    spec: Dict[str, dict] = {}
    for short, _, _ in FUNCTIONS:
        m_words = re.search(
            rf"def\s+{short}Words\s*:\s*Array\s+UInt32\s*:=\s*#\[(.*?)\]",
            text,
            re.S,
        )
        if not m_words:
            raise ValueError(f"{lean_path}: missing `def {short}Words`")
        body_no_comments = re.sub(r"--[^\n]*", "", m_words.group(1))
        words = [int(tok, 16) for tok in re.findall(r"0x[0-9a-fA-F]+", body_no_comments)]

        m_br = re.search(
            rf"def\s+{short}Branches\s*:\s*List\s+BranchReloc\s*:=\s*\[(.*?)\]",
            text,
            re.S,
        )
        if not m_br:
            raise ValueError(f"{lean_path}: missing `def {short}Branches`")
        branches = []
        for idx_s, call_s, sym_s in re.findall(
            r"\{\s*idx\s*:=\s*(\d+)\s*,\s*isCall\s*:=\s*(true|false)\s*,\s*target\s*:=\s*\.([A-Za-z0-9_]+)\s*\}",
            m_br.group(1),
        ):
            branches.append(
                {"idx": int(idx_s), "isCall": call_s == "true", "target": sym_s}
            )

        m_got = re.search(
            rf"def\s+{short}Gots\s*:\s*List\s+GotReloc\s*:=\s*\[(.*?)\]",
            text,
            re.S,
        )
        if not m_got:
            raise ValueError(f"{lean_path}: missing `def {short}Gots`")
        gots = []
        for idx_s, rd_s, sym_s in re.findall(
            r"\{\s*idx\s*:=\s*(\d+)\s*,\s*rd\s*:=\s*(?:⟨)?(\d+)(?:,\s*by\s+decide⟩)?\s*,\s*target\s*:=\s*\.([A-Za-z0-9_]+)\s*\}",
            m_got.group(1),
        ):
            gots.append({"idx": int(idx_s), "rd": int(rd_s), "target": sym_s})

        spec[short] = {"words": words, "branches": branches, "gots": gots}
    return spec


def verify_linked_exe(exe: MachO64, spec: Dict[str, dict]) -> Tuple[int, int]:
    for sym_name in SYM_TO_ID:
        if sym_name not in exe.def_syms:
            raise ValueError(f"{exe.label}: missing symbol {sym_name}")

    branch_checked = 0
    got_checked = 0
    for short, _, sym_name in FUNCTIONS:
        fn = exe.extract_function(sym_name)
        exp = spec[short]
        if len(fn["words"]) != len(exp["words"]):
            raise ValueError(
                f"{exe.label}: {short} word count {len(fn['words'])} != {len(exp['words'])}"
            )
        reloc_idxs = {b["idx"] for b in exp["branches"]}
        for g in exp["gots"]:
            reloc_idxs.add(g["idx"])
            reloc_idxs.add(g["idx"] + 1)

        for idx, (got_w, exp_w) in enumerate(zip(fn["words"], exp["words"])):
            if idx not in reloc_idxs and got_w != exp_w:
                raise ValueError(
                    f"{exe.label}: {short}[{idx}] word mismatch {hex(got_w)} != {hex(exp_w)}"
                )

        base_va = fn["start"]
        for b in exp["branches"]:
            idx = b["idx"]
            pc = base_va + 4 * idx
            w = fn["words"][idx]
            opc_expect = 0x94000000 if b["isCall"] else 0x14000000
            if (w & 0xFC000000) != opc_expect:
                raise ValueError(
                    f"{exe.label}: {short}[{idx}] expected {'BL' if b['isCall'] else 'B'}, got {hex(w)}"
                )
            off = sign_extend((w & 0x03FFFFFF) << 2, 28)
            dest = (pc + off) & MASK64
            target_va = exe.def_syms[ID_TO_SYM[b["target"]]][1]
            if dest != target_va:
                raise ValueError(
                    f"{exe.label}: {short}[{idx}] branch target {hex(dest)} != {hex(target_va)}"
                )
            branch_checked += 1

        for g in exp["gots"]:
            idx = g["idx"]
            rd = g["rd"]
            pc = base_va + 4 * idx
            w0 = fn["words"][idx]
            w1 = fn["words"][idx + 1]
            if (w0 & 0x9F000000) != 0x90000000 or (w0 & 0x1F) != rd:
                raise ValueError(
                    f"{exe.label}: {short}[{idx}] expected ADRP X{rd}, got {hex(w0)}"
                )
            immlo = (w0 >> 29) & 0x3
            immhi = (w0 >> 5) & 0x7FFFF
            page_off = (sign_extend((immhi << 2) | immlo, 21) << 12) & MASK64
            page = ((pc & ~0xFFF) + page_off) & MASK64
            target_va = exe.def_syms[ID_TO_SYM[g["target"]]][1]

            if (w1 & 0xFF800000) == 0x91000000:
                # Apple ld GOT relaxation: ADD Xd, Xd, #imm12
                rd1 = w1 & 0x1F
                rn1 = (w1 >> 5) & 0x1F
                sh = (w1 >> 22) & 0x1
                imm12 = (w1 >> 10) & 0xFFF
                off = imm12 << (12 if sh else 0)
                resolved = (page + off) & MASK64
                if rd1 != rd or rn1 != rd or resolved != target_va:
                    raise ValueError(
                        f"{exe.label}: {short}[{idx}] relaxed GOT ADD {hex(resolved)} != {hex(target_va)}"
                    )
            elif (w1 & 0xFFC00000) == 0xF9400000:
                # Unrelaxed GOT load: LDR Xd, [Xd, #off]
                rd1 = w1 & 0x1F
                rn1 = (w1 >> 5) & 0x1F
                off = ((w1 >> 10) & 0xFFF) << 3
                slot_va = (page + off) & MASK64
                slot_val = exe.read_vaddr_u64(slot_va)
                if rd1 != rd or rn1 != rd or slot_val != target_va:
                    raise ValueError(
                        f"{exe.label}: {short}[{idx}] GOT slot {hex(slot_val)} != {hex(target_va)}"
                    )
            else:
                raise ValueError(
                    f"{exe.label}: {short}[{idx}+1] unexpected GOT second insn {hex(w1)}"
                )
            got_checked += 1

    return branch_checked, got_checked


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--build-dir", default="build/cxx")
    ap.add_argument("--code-lean", default="MemcpyCrc32c/Arm64/Code.lean")
    ap.add_argument("--dump-json", action="store_true")
    args = ap.parse_args()

    build_dir = pathlib.Path(args.build_dir)
    objs = {
        "HwCombine.c.o": MachO64(
            (build_dir / ".lake_build_ir_MemcpyCrc32c_Impl_HwCombine.c.o").read_bytes(),
            "HwCombine.c.o",
        ),
        "Hw.c.o": MachO64(
            (build_dir / ".lake_build_ir_MemcpyCrc32c_Impl_Hw.c.o").read_bytes(),
            "Hw.c.o",
        ),
    }

    extracted = {}
    for short, obj_key, sym_name in FUNCTIONS:
        extracted[short] = objs[obj_key].extract_function(sym_name)

    if args.dump_json:
        exe_path = build_dir / "test_c_abi"
        linked_syms = {}
        if exe_path.exists():
            exe = MachO64(exe_path.read_bytes(), "test_c_abi")
            linked_syms = {
                sym_id: exe.def_syms[sym][1]
                for sym, sym_id in SYM_TO_ID.items()
                if sym in exe.def_syms
            }
        print(json.dumps({"functions": extracted, "linked_syms": linked_syms}, indent=2))
        return 0

    code_lean = pathlib.Path(args.code_lean)
    spec = parse_code_lean(code_lean)

    # 1. Verify against standalone .o files
    total_words = 0
    for short, obj_key, _ in FUNCTIONS:
        got = extracted[short]
        exp = spec[short]
        if got["words"] != exp["words"]:
            raise ValueError(f"{obj_key}: {short} words differ from {code_lean}")
        if got["branches"] != exp["branches"]:
            raise ValueError(
                f"{obj_key}: {short} BRANCH26 relocs {got['branches']} != {exp['branches']}"
            )
        if got["gots"] != exp["gots"]:
            raise ValueError(
                f"{obj_key}: {short} GOT_LOAD relocs {got['gots']} != {exp['gots']}"
            )
        total_words += len(exp["words"])

    # 2. Verify against libleancrc32c.a archive members
    ar_members = extract_ar_members(build_dir / "libleancrc32c.a")
    ar_map = {
        "HwCombine.c.o": ".lake_build_ir_MemcpyCrc32c_Impl_HwCombine.c.o",
        "Hw.c.o": ".lake_build_ir_MemcpyCrc32c_Impl_Hw.c.o",
    }
    for obj_key, member_name in ar_map.items():
        if member_name not in ar_members:
            raise ValueError(f"libleancrc32c.a: missing member {member_name}")
        if ar_members[member_name] != objs[obj_key].data:
            raise ValueError(f"libleancrc32c.a: {member_name} differs from {obj_key}")

    # 3. Verify against linked test_c_abi executable
    exe = MachO64((build_dir / "test_c_abi").read_bytes(), "test_c_abi")
    n_br, n_got = verify_linked_exe(exe, spec)

    print(
        f"OK: AArch64 Mach-O machine-code audit ({len(FUNCTIONS)} functions, "
        f"{total_words} instructions, {n_br} BRANCH26 relocations, {n_got} GOT_LOAD pairs "
        f"verified across .o, libleancrc32c.a, and test_c_abi)"
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
