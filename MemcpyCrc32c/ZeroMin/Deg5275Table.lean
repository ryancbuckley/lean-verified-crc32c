/-
Shared residue list, lookup table (`0` and `X^1, …, X^5274 mod G`), and fast
single-pass certificates for `zero4_5275_minimal` and `zero4_5275_unique`.
-/
import MemcpyCrc32c.ZeroMin.Common

namespace Crc32c

namespace ZeroMin.Deg5275
open ZeroMin

def tableKeys : List Nat := 0 :: resNat 5274 (stepBit 0x80000000)

open Lean Elab Term in
elab "deg5275_residues%" : term =>
  return toExpr (resNat 5274 (stepBit 0x80000000))

open Lean Elab Term in
elab "deg5275_trie%" : term =>
  return (Trie.build 32 tableKeys).toExpr

open Lean Elab Term in
elab "deg5275_bits_lo%" : term =>
  return mkRawNatLit (bitset (· % 65536) tableKeys)

open Lean Elab Term in
elab "deg5275_bits_hi%" : term =>
  return mkRawNatLit (bitset (· / 65536) tableKeys)

set_option maxRecDepth 2000000

def resL : List Nat := deg5275_residues%
def table : Trie := deg5275_trie%
def bitsLo : Nat := deg5275_bits_lo%
def bitsHi : Nat := deg5275_bits_hi%

noncomputable def inTable (v : Nat) : Bool :=
  inTable16 bitsLo bitsHi table v

def resLo : List Nat := resL.take 2637
def resHi : List Nat := resL.drop 2637

theorem resL_eq : resL = resNat 5274 (stepBit 0x80000000) := by decide +kernel

theorem resL_eq_map : resL = (List.range' 1 5274).map fun i => (ρ i).toNat := by
  rw [resL_eq, ← resNat_ρ]; rfl

theorem inTable_zero : inTable 0 = true := by decide +kernel
theorem listIn_resL : listIn inTable resL = true := by decide +kernel

/-! ### Uniqueness certificate at degree 5275 -/

def w2751 : Nat := (ρ 2751).toNat
def w4508 : Nat := (ρ 4508).toNat
def target5275 : Nat := ((0x80000000 : UInt32) ^^^ ρ 5275).toNat

def inW5275 (x : Nat) : Bool :=
  Nat.beq x w2751 || Nat.beq x w4508

theorem uniq5275_loop : loop1_uniq inTable inW5275 target5275 resL = true := by decide +kernel

theorem filter_resL_w5275 : resL.filter inW5275 = [w2751, w4508] := by decide +kernel

end ZeroMin.Deg5275

end Crc32c
