/-
GF(2^8) byte arithmetic (field polynomial 0x11D), Lagrange coefficients, and
the split-nibble lookup tables that `leanrs_apply` (`cxx/leanrs_apply_arm64.S`)
consumes. Core-only executable code; proven in `ReedSolomon.Field` and
`ReedSolomon.Tables`.
-/

namespace ReedSolomon

/-- Multiply by `x`. -/
@[inline] def gfMulX (a : UInt8) : UInt8 :=
  (a <<< 1) ^^^ (if a &&& 0x80 == 0 then 0 else 0x1d)

/-- `r + a * (low n bits of b)`, by shift and add. -/
def gfMulLoop : Nat → UInt8 → UInt8 → UInt8 → UInt8
  | 0, _, _, r => r
  | n + 1, a, b, r => gfMulLoop n (gfMulX a) (b >>> 1) (if b &&& 1 == 0 then r else r ^^^ a)

/-- Field multiplication. -/
def gfMul (a b : UInt8) : UInt8 := gfMulLoop 8 a b 0

def gfPow (a : UInt8) : Nat → UInt8
  | 0 => 1
  | n + 1 => gfMul a (gfPow a n)

/-- `a^n` by square-and-multiply. -/
def gfPowSq (a : UInt8) (n : Nat) : UInt8 :=
  if h : n = 0 then 1
  else
    let t := gfPowSq (gfMul a a) (n / 2)
    if n % 2 = 1 then gfMul a t else t
termination_by n
decreasing_by omega

/-- `a⁻¹ = a^254` (and `0` for `a = 0`). -/
def gfInv (a : UInt8) : UInt8 := gfPowSq a 254

/-- Numerator and denominator of the Lagrange coefficient over the first `t`
points: `∏ (y - x_u)` and `∏ (x_s - x_u)` for `u < t`, `u ≠ s`. -/
def lagNumDen (xs : ByteArray) (s : Nat) (y : UInt8) : Nat → UInt8 × UInt8
  | 0 => (1, 1)
  | t + 1 =>
    let p := lagNumDen xs s y t
    if t = s then p else (gfMul p.1 (y ^^^ xs[t]!), gfMul p.2 (xs[s]! ^^^ xs[t]!))

/-- The Lagrange coefficient `ℓ_s(y) = ∏_{t ≠ s} (y - x_t) / (x_s - x_t)`. -/
def lagrange (xs : ByteArray) (s : Nat) (y : UInt8) : UInt8 :=
  let p := lagNumDen xs s y xs.size
  gfMul p.1 (gfInv p.2)

/-- Row-major `ys.size × xs.size` matrix of Lagrange coefficients: entry
`j * xs.size + i` is `ℓ_i(ys[j])`. -/
def coeffs (xs ys : ByteArray) : ByteArray :=
  ⟨Array.ofFn (n := ys.size * xs.size) fun n =>
    lagrange xs (n.val % xs.size) ys[n.val / xs.size]!⟩

/-- The 32 table bytes of each coefficient `c`, in coefficient order:
`c * v` for `v = 0..15`, then `c * (v << 4)` for `v = 0..15`. -/
def tablesOf (c : ByteArray) : ByteArray :=
  ⟨Array.ofFn (n := 32 * c.size) fun t =>
    let cf := c[t.val / 32]!
    let v := t.val % 32
    if v < 16 then gfMul cf v.toUInt8 else gfMul cf ((v - 16).toUInt8 <<< 4)⟩

/-- The table `leanrs_apply` needs to compute the shards at the points `ys`
from the shards at the points `xs`. -/
def tables (xs ys : ByteArray) : ByteArray := tablesOf (coeffs xs ys)

/-- For the C library (`cxx/leanrs.cc`). -/
@[export leanrs_tables_lean] def tablesExport (xs ys : ByteArray) : ByteArray := tables xs ys

end ReedSolomon
