/-
Specification of Reed–Solomon erasure coding, over any field.

A stripe is `k` field elements `d 0, …, d (k-1)` placed at `k` distinct points
`xs 0, …, xs (k-1)`. Its code polynomial is the unique polynomial of degree
`< k` through those values, and the shard at any point `y` is the value of that
polynomial at `y`. An `(n, k)` code stores the shards at `n` distinct points,
the first `k` of which are the data itself.

Proven here, with no reference to any implementation:
* `shardAt_node`        — the shard at a data point is the data (systematic);
* `shardAt_reconstruct` — the shards at ANY `k` distinct points determine every
                          shard (recovery from any `n - k` erasures);
* `card_agree_lt`       — two different stripes agree at fewer than `k` points
                          (minimum distance `n - k + 1`: the code is MDS);
* `shardAt_eq_sum`      — the shard at `y` is the linear combination of the data
                          with the Lagrange coefficients `lagrangeCoeff`, which
                          is the form implementations compute.
-/
import Mathlib.LinearAlgebra.Lagrange

namespace ReedSolomon
open Polynomial Finset

variable {F : Type*} [Field F] {k : ℕ}

/-- The polynomial of degree `< k` taking the value `d i` at `xs i`. -/
noncomputable def codePoly (xs d : Fin k → F) : F[X] := Lagrange.interpolate univ xs d

/-- The shard at the point `y` of the stripe with data `d` at the points `xs`. -/
noncomputable def shardAt (xs d : Fin k → F) (y : F) : F := (codePoly xs d).eval y

/-- The Lagrange coefficient `∏_{t ≠ s} (y - x_t) / (x_s - x_t)`. -/
def lagrangeCoeff (xs : Fin k → F) (s : Fin k) (y : F) : F :=
  ∏ t ∈ univ.erase s, (xs s - xs t)⁻¹ * (y - xs t)

variable {xs d : Fin k → F}

theorem degree_codePoly_lt (hx : Function.Injective xs) : (codePoly xs d).degree < k := by
  have h := Lagrange.degree_interpolate_lt (s := univ) (r := d) hx.injOn
  rwa [card_univ, Fintype.card_fin] at h

/-- Systematic: at a data point the shard is the data. -/
theorem shardAt_node (hx : Function.Injective xs) (i : Fin k) : shardAt xs d (xs i) = d i :=
  Lagrange.eval_interpolate_at_node d hx.injOn (mem_univ i)

/-- A polynomial of degree `< k` is the code polynomial of its values at any
`k` distinct points. -/
theorem codePoly_eval {f : F[X]} (hf : f.degree < k) {zs : Fin k → F}
    (hz : Function.Injective zs) : codePoly zs (fun i => f.eval (zs i)) = f :=
  (Lagrange.eq_interpolate (s := univ) hz.injOn (by simpa using hf)).symm

/-- Reconstruction: the shards at any `k` distinct points `zs` determine the
code polynomial of the stripe. -/
theorem codePoly_reconstruct (hx : Function.Injective xs) {zs : Fin k → F}
    (hz : Function.Injective zs) :
    codePoly zs (fun i => shardAt xs d (zs i)) = codePoly xs d :=
  codePoly_eval (degree_codePoly_lt hx) hz

/-- Reconstruction: interpolating the shards at any `k` distinct points `zs`
gives back every shard of the stripe. -/
theorem shardAt_reconstruct (hx : Function.Injective xs) {zs : Fin k → F}
    (hz : Function.Injective zs) (y : F) :
    shardAt zs (fun i => shardAt xs d (zs i)) y = shardAt xs d y := by
  rw [shardAt, codePoly_reconstruct hx hz, shardAt]

/-- In particular the data comes back from any `k` shards. -/
theorem data_reconstruct (hx : Function.Injective xs) {zs : Fin k → F}
    (hz : Function.Injective zs) (i : Fin k) :
    shardAt zs (fun j => shardAt xs d (zs j)) (xs i) = d i := by
  rw [shardAt_reconstruct hx hz, shardAt_node hx]

/-- MDS: two different stripes agree at fewer than `k` of any distinct points,
so among `n` shards they differ in at least `n - k + 1`. -/
theorem card_agree_lt [DecidableEq F] (hx : Function.Injective xs) {d' : Fin k → F} (hd : d ≠ d') {n : ℕ}
    {ys : Fin n → F} (hy : Function.Injective ys) :
    #{j | shardAt xs d (ys j) = shardAt xs d' (ys j)} < k := by
  by_contra hge
  rw [not_lt] at hge
  apply hd
  have heq : codePoly xs d = codePoly xs d' := by
    apply eq_of_degrees_lt_of_eval_index_eq ({j | shardAt xs d (ys j) = shardAt xs d' (ys j)})
      hy.injOn
    · exact (degree_codePoly_lt hx).trans_le (by exact_mod_cast hge)
    · exact (degree_codePoly_lt hx).trans_le (by exact_mod_cast hge)
    · intro j hj; exact (mem_filter.mp hj).2
  funext i
  rw [← shardAt_node (d := d) hx i, ← shardAt_node (d := d') hx i, shardAt, shardAt, heq]

/-- The shard at `y` as the linear combination that implementations compute. -/
theorem shardAt_eq_sum (y : F) : shardAt xs d y = ∑ s, lagrangeCoeff xs s y * d s := by
  simp only [shardAt, codePoly, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C,
    Lagrange.basis, eval_prod, Lagrange.basisDivisor, eval_sub, eval_X, lagrangeCoeff]
  exact sum_congr rfl fun s _ => mul_comm _ _

end ReedSolomon
