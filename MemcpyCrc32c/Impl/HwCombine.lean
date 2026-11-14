/-
Precomputed shift constants, 2 KiB small-stream shift table, and hardware
stream-combining helpers (`hwMul`, `hwPowGo`, `hwShiftWords`, `combine3`,
`combine6`) for `MemcpyCrc32c.Impl.Hw`.

Kept in its own translation unit so the C compiler cannot inline `combine3` /
`combine6` (and `hwPowGo`) bottom-up into the inner stream loops (`hwFold3`,
`hwFold6Loop`). Core-only executable code.
-/
import MemcpyCrc32c.Impl.Portable
import SimdModels.Trusted

namespace Crc32c
open SimdModels (crc32c_u64 clmulLo)

/-! ### Portable precomputed constants and shift tables -/

/-- `X^1`, reflected (`bit 30` of a 32-bit reflected word). Named `hwX1` to avoid
colliding with `ZeroPoly.x1` in proof modules. -/
@[inline] def hwX1 : UInt32 := 0x40000000

/-- Identity element `X^(-33) mod G` for shifted hardware multiplication `hwMul`:
computed as `(X^(-8))^5 * X^7 = X^(-33) mod G`. -/
def hwOne : UInt32 := mulMod (powMod xInv8 5) 0x01000000

/-- Base `X^(64 - 33) = X^31 mod G` for `hwPowGo` (one 64-bit word per step). -/
def hwX64 : UInt32 := powMod hwX1 31

/-- 128-bit fold constants (`X * polyR kFold{d}_{1,2} = X^{d+64, d} mod G`) for
64-byte multi-block dot-product folding across distances `d ∈ {128, 256, 384, 512}` bits. -/
def kFold128_1 : UInt64 := (powMod hwX1 159).toUInt64
def kFold128_2 : UInt64 := (powMod hwX1 95).toUInt64
def kFold256_1 : UInt64 := (powMod hwX1 287).toUInt64
def kFold256_2 : UInt64 := (powMod hwX1 223).toUInt64
def kFold384_1 : UInt64 := (powMod hwX1 415).toUInt64
def kFold384_2 : UInt64 := (powMod hwX1 351).toUInt64
def kFold512_1 : UInt64 := (powMod hwX1 543).toUInt64
def kFold512_2 : UInt64 := (powMod hwX1 479).toUInt64

/-- Byte `m` of the packed 2 KiB small-stream shift table (`512` `UInt32` entries):
entry `ws` (`1 ≤ ws < 512`) stores `X^(64 * ws - 33) mod G` in little-endian bytes. -/
def hwShiftSmallEntry (m : Fin 2048) : UInt8 :=
  let ws := m.val / 4
  let shift := ((m.val % 4) * 8).toUInt32
  let entry := if ws = 0 then 0 else powMod hwX1 (64 * ws - 33)
  (entry >>> shift).toUInt8

/-- Packed 2 KiB shift table covering stream lengths up to `511 * 8 = 4088` bytes
(`24 KiB` across 6 streams) in a single 32-bit load. -/
def hwShiftSmallBytes : ByteArray :=
  ByteArray.mk (Array.ofFn hwShiftSmallEntry)

theorem hwShiftSmallBytes_size : hwShiftSmallBytes.size = 2048 := by
  simp [hwShiftSmallBytes, ByteArray.size]

theorem hwShiftSmallBytes_uget (j : USize) (h : j.toNat < hwShiftSmallBytes.size) :
    hwShiftSmallBytes.uget j h =
      hwShiftSmallEntry ⟨j.toNat, by simpa [hwShiftSmallBytes_size] using h⟩ := by
  have key : ∀ {n : Nat} (f : Fin n → UInt8) (h' : j.toNat < (ByteArray.mk (Array.ofFn f)).size),
      (ByteArray.mk (Array.ofFn f)).uget j h' = f ⟨j.toNat, by simpa [ByteArray.size] using h'⟩ := by
    intro n f h'; simp [ByteArray.uget]
  exact key hwShiftSmallEntry h

/-- Single-load shift lookup for `ws < 512` 64-bit words. -/
@[inline] def hwShiftSmall (ws : USize) (hws : ws.toNat < 512) : UInt32 :=
  have hs : 2048 < USize.size := by have := usize_size_gt; omega
  have hpow : 2 ^ System.Platform.numBits = USize.size := rfl
  have h4 : (4 : USize).toNat = 4 := by simp
  have hbase : (ws * 4).toNat = ws.toNat * 4 := by
    rw [USize.toNat_mul, h4]; exact Nat.mod_eq_of_lt (by omega)
  load32 hwShiftSmallBytes (ws * 4) (by rw [hwShiftSmallBytes_size]; exact hs)
    (by rw [hwShiftSmallBytes_size]; omega)

/-! ### Hardware GF(2) multiplication and stream combination -/

/-- Shifted product modulo `G` via 64-bit carry-less multiply + `CRC32CX`:
computes `P(a) * P(b) * X^33 mod G` in two instructions. -/
@[inline] def hwMul (a b : UInt32) : UInt32 :=
  crc32c_u64 0 (clmulLo a.toUInt64 b.toUInt64)

/-- Square-and-multiply under `hwMul` for arbitrary 64-bit word counts. -/
def hwPowGo (base acc : UInt32) (n : UInt64) : UInt32 :=
  if _h : n = 0 then acc
  else hwPowGo (hwMul base base) (if n &&& 1 = 1 then hwMul acc base else acc) (n >>> 1)
termination_by n.toNat
decreasing_by
  have hn : n.toNat ≠ 0 := fun h0 => _h (by rw [← n.ofNat_toNat, h0]; rfl)
  have hs : (n >>> 1).toNat = n.toNat / 2 := by rw [UInt64.toNat_shiftRight]; rfl
  omega

/-- Shifted factor `X^(64 * ws - 33) mod G` for `1 ≤ ws`: O(1) table load for
`ws < 512`, hardware `hwPowGo` for larger streams. -/
@[inline] def hwShiftWords (ws : USize) : UInt32 :=
  if h : ws < 512 then
    have e512 : (512 : USize).toNat = 512 := by simp
    hwShiftSmall ws (by have := USize.lt_iff_toNat_lt.mp h; omega)
  else
    hwPowGo hwX64 hwOne ws.toUInt64

/-- Combine three equal-length stream CRCs (`L = ws * 8` bytes per stream). -/
@[noinline] def combine3 (ws : USize) (s0 s1 s2 : UInt32) : UInt32 :=
  let f := hwShiftWords ws
  hwMul (hwMul s0 f ^^^ s1) f ^^^ s2

/-- Tree-combine six equal-length stream CRCs (`L = ws * 8` bytes per stream). -/
@[noinline] def combine6 (ws : USize) (s0 s1 s2 s3 s4 s5 : UInt32) : UInt32 :=
  let f := hwShiftWords ws
  let f2 := hwMul f f
  let p01 := hwMul s0 f ^^^ s1
  let p23 := hwMul s2 f ^^^ s3
  let p45 := hwMul s4 f ^^^ s5
  hwMul (hwMul p01 f2 ^^^ p23) f2 ^^^ p45

end Crc32c
