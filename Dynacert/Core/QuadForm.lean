import Mathlib

/-!
# Quadratic forms and PSD witnesses


Every matrix inequality in a dynacert certificate is discharged the same way: the untrusted
oracle supplies an exact rational factorization `M = Lᵀ D L` with `D` diagonal and nonnegative,
the Lean kernel checks the factorization by computation (`decide +kernel`), and
`PSDWitness.quad_nonneg` transports the conclusion to real vectors.
-/

namespace Dynacert

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `v ⬝ᵥ Aᵀ w = w ⬝ᵥ A v`. (Later Mathlib versions have this under the same name; the
Mathlib pinned by gnc_lean does not.) -/
theorem dotProduct_transpose_mulVec {m n R : Type*} [Fintype m] [Fintype n] [CommSemiring R]
    (v : n → R) (A : Matrix m n R) (w : m → R) : v ⬝ᵥ Aᵀ *ᵥ w = w ⬝ᵥ A *ᵥ v := by
  rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]

/-- The quadratic form `xᵀ M x`. -/
def quad {R : Type*} [CommRing R] (M : Matrix ι ι R) (x : ι → R) : R :=
  x ⬝ᵥ M *ᵥ x

/-- Entrywise cast of a rational matrix to a real matrix. -/
noncomputable abbrev toReal {m n : Type*} (M : Matrix m n ℚ) : Matrix m n ℝ :=
  M.map (Rat.castHom ℝ)

/-- An exact certificate that the rational matrix `M` is positive semidefinite:
`M = Lᵀ * diagonal d * L` with every `d i ≥ 0`. Both fields are meant to be proved by
`decide +kernel`. -/
structure PSDWitness (M : Matrix ι ι ℚ) where
  L : Matrix ι ι ℚ
  d : ι → ℚ
  d_nonneg : ∀ i, 0 ≤ d i
  factor : M = Lᵀ * diagonal d * L

theorem quad_transpose_diagonal_mul {R : Type*} [CommRing R] (L : Matrix ι ι R) (d : ι → R)
    (x : ι → R) :
    quad (Lᵀ * diagonal d * L) x = ∑ i, d i * (L *ᵥ x) i * (L *ᵥ x) i := by
  unfold quad
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]

/-- Soundness of a PSD witness: the real quadratic form of `M` is nonnegative. -/
theorem PSDWitness.quad_nonneg {M : Matrix ι ι ℚ} (W : PSDWitness M) (x : ι → ℝ) :
    0 ≤ quad (toReal M) x := by
  have hM : toReal M = (toReal W.L)ᵀ * diagonal (fun i => (W.d i : ℝ)) * toReal W.L := by
    conv_lhs => rw [W.factor]
    rw [toReal, Matrix.map_mul, Matrix.map_mul, transpose_map, diagonal_map (by simp)]
    rfl
  rw [hM, quad_transpose_diagonal_mul]
  refine Finset.sum_nonneg fun i _ => ?_
  have := W.d_nonneg i
  rw [mul_assoc]
  exact mul_nonneg (by exact_mod_cast this) (mul_self_nonneg _)

omit [DecidableEq ι] in
/-- The real quadratic form at a rational point is the cast of the rational one, so bounds at
explicit rational points reduce to `decide` over `ℚ`. -/
theorem quad_toReal_cast (M : Matrix ι ι ℚ) (v : ι → ℚ) :
    quad (toReal M) (fun i => (v i : ℝ)) = ((quad M v : ℚ) : ℝ) := by
  simp [quad, dotProduct, mulVec, toReal, Finset.mul_sum]

end Dynacert
