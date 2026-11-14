/- Feasibility spike, not product code: can a Lean loop over an inline
   hardware-CRC intrinsic compile to tight machine code? -/
import MemcpyCrc32c.Impl.Portable
open Crc32c

@[extern c inline "__builtin_arm_crc32cd(#1, #2)"]
def crc32cd (c : UInt32) (w : UInt64) : UInt32 := stepWord c w

def hwLoop (a : @& ByteArray) (hs : a.size < USize.size) (i fin : USize)
    (hi : i.toNat ≤ fin.toNat) (hfin : fin.toNat ≤ a.size) (s : UInt32) : UInt32 :=
  if h : 8 ≤ fin - i then
    have hsub : (fin - i).toNat = fin.toNat - i.toNat :=
      USize.toNat_sub_of_le fin i (USize.le_iff_toNat_le.mpr hi)
    have h' : 8 ≤ fin.toNat - i.toNat := by
      have := USize.le_iff_toNat_le.mp h
      have e8 : (8 : USize).toNat = 8 := by simp
      rw [hsub, e8] at this; exact this
    have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat i 8 (by omega)
    hwLoop a hs (i + 8) fin (by omega) hfin (crc32cd s (load64 a i hs (by omega)))
  else bytesLoop a i fin hfin s
termination_by fin.toNat - i.toNat
decreasing_by omega

def hwExtend (c : UInt32) (a : @& ByteArray) : UInt32 :=
  if hs : a.size < USize.size then
    hwLoop a hs 0 a.size.toUSize (by simp) (by rw [USize.toNat_ofNat_of_lt' hs]; omega) (c ^^^ 0xFFFFFFFF) ^^^ 0xFFFFFFFF
  else 0

def mkBuf (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut x : UInt64 := 88172645463325252
  for _ in [0:n] do
    x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 7); x := x ^^^ (x <<< 17)
    b := b.push x.toUInt8
  return b

def main : IO Unit := do
  let a := mkBuf 1048576
  IO.println s!"agree: {hwExtend 5 a == extendPortable 5 a}"
  let mut sink : UInt32 := 0
  let mut best := 0.0
  for _ in [0:9] do
    let t0 ← IO.monoNanosNow
    for _ in [0:64] do sink := hwExtend sink a
    let t1 ← IO.monoNanosNow
    best := max best (1048576.0 * 64.0 / (t1 - t0).toFloat)
  IO.println s!"single-stream hardware CRC from Lean, 1 MiB: {best} GB/s [{sink}]"
