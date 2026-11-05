import Rumoca.Prelude

/-!
# Scalarizing rumoca's array equations

rumoca transcribes a Modelica array `Real v[n]` as a field `v : Fin n → ℝ` (a matrix
`Real M[m, n]` as `Matrix (Fin m) (Fin n) ℝ`), and an array equation as one conjunct relating
vectors (`dx.p = x.v`, `dx.v = p.K *ᵥ x.x + …`), or as a family `∀ i : Fin n, …` /
`∀ i : ℕ, a ≤ i → i ≤ b → …` (a `for` loop). The linear methods treat each array element as a
scalar coordinate: the generated link proof takes components of these conjuncts (`congrFun`,
or instantiating the family) and evaluates them with `simp only` and the lemmas below, which
turn `Rumoca.slice` / `Rumoca.at1` / `Rumoca.at2` subscripts and `Fin.mk` indices into numeral
indices `v 0`, `v 1`, …, so that `linear_combination` sees the same atoms as the coordinates.
-/

namespace Dynacert.Linear

/-- A `Fin.mk` with a numeral value is that numeral (e.g. `⟨2, h⟩ = (2 : Fin 3)`). -/
theorem fin_mk_ofNat {n : ℕ} [NeZero n] (k : ℕ) (h : (OfNat.ofNat k : ℕ) < n) :
    (⟨no_index (OfNat.ofNat k), h⟩ : Fin n) = (OfNat.ofNat k : Fin n) :=
  Fin.ext (by simp [Nat.mod_eq_of_lt h])

/-- `Fin.succ` as a `Fin.mk`, so that closed indices reduce to numerals with `fin_mk_ofNat`. -/
theorem fin_succ_eq_mk {n : ℕ} (i : Fin n) : i.succ = ⟨(i : ℕ) + 1, by omega⟩ := rfl

section Examples

open Matrix

set_option linter.unusedSimpArgs false

/-! The simp set the generator emits (`emit_lti.SCALAR_SIMPS`), on the shapes rumoca produces. -/

example (v : Fin 5 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (a : ℝ)
    (h1 : v ⟨2 - 1, by omega⟩ = a) (h2 : v ⟨1 + 1 * ((1 : Fin 2) : ℕ), by omega⟩ = a)
    (h3 : Rumoca.at1 v 5 = a) (h4 : Rumoca.at2 M 4 2 = a)
    (h5 : (![a, a, a, 0, 1] : Fin 5 → ℝ) 4 = v 3)
    (h6 : (Matrix.of ![![0, 1, 2, 3], ![4, 5, 6, 7], ![8, 9, 10, 11], ![12, 13, 14, a]]
      : Matrix (Fin 4) (Fin 4) ℝ) 3 3 = v 4) :
    v 1 = a ∧ v 2 = a ∧ v 4 = a ∧ M 3 1 = a ∧ 1 = v 3 ∧ a = v 4 := by
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.of_apply, Matrix.cons_val, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_succ, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.isValue, Rumoca.slice,
    Rumoca.at1, Rumoca.at2, Rumoca.skew, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    fin_succ_eq_mk, Fin.val_succ, Fin.val_zero,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul,
    Nat.one_le_ofNat, Nat.reduceLeDiff, and_self, dite_true, le_refl, fin_mk_ofNat,
    Pi.zero_apply, Matrix.zero_apply, cross_apply]
    at h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

example (K : Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (d : ℝ)
    (h : (K *ᵥ x + (2 : ℝ) • x) 3 = d) :
    K 3 0 * x 0 + K 3 1 * x 1 + K 3 2 * x 2 + K 3 3 * x 3 + 2 * x 3 = d := by
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.of_apply, Matrix.cons_val, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_succ, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.isValue, Rumoca.slice,
    Rumoca.at1, Rumoca.at2, Rumoca.skew, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    fin_succ_eq_mk, Fin.val_succ, Fin.val_zero,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul,
    Nat.one_le_ofNat, Nat.reduceLeDiff, and_self, dite_true, le_refl, fin_mk_ofNat,
    Pi.zero_apply, Matrix.zero_apply, cross_apply] at h
  linear_combination h

example (v : Fin 9 → ℝ) (w : Fin 3 → ℝ) (A B : Matrix (Fin 3) (Fin 3) ℝ) (a : ℝ)
    (h1 : Rumoca.slice v 4 2 3 ⬝ᵥ ![1, 2, 3] = a)
    (h2 : (Rumoca.skew w *ᵥ (fun i => 2 * w i)) 2 = a)
    (h3 : (A * B) 2 1 + Aᵀ 0 2 = a) :
    v 4 + 2 * v 6 + 3 * v 8 = a ∧ w 0 * (2 * w 1) - w 1 * (2 * w 0) = a ∧
      A 2 0 * B 0 1 + A 2 1 * B 1 1 + A 2 2 * B 2 1 + A 2 0 = a := by
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.of_apply, Matrix.cons_val, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_succ, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.isValue, Rumoca.slice,
    Rumoca.at1, Rumoca.at2, Rumoca.skew, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    fin_succ_eq_mk, Fin.val_succ, Fin.val_zero,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul,
    Nat.one_le_ofNat, Nat.reduceLeDiff, and_self, dite_true, le_refl, fin_mk_ofNat,
    Pi.zero_apply, Matrix.zero_apply, cross_apply] at h1 h2 h3
  exact ⟨by linear_combination h1, by linear_combination h2, by linear_combination h3⟩

example (w q : Fin 3 → ℝ) (z : Fin 2 → ℝ) (a b : ℝ)
    (h1 : (crossProduct w q) 2 = a) (h2 : (z + (0 : Fin 2 → ℝ)) 1 = b) :
    w 0 * q 1 - w 1 * q 0 = a ∧ z 1 = b := by
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.of_apply, Matrix.cons_val, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_succ, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.isValue, Rumoca.slice,
    Rumoca.at1, Rumoca.at2, Rumoca.skew, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    fin_succ_eq_mk, Fin.val_succ, Fin.val_zero,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul,
    Nat.one_le_ofNat, Nat.reduceLeDiff, and_self, dite_true, le_refl, fin_mk_ofNat,
    Pi.zero_apply, Matrix.zero_apply, cross_apply] at h1 h2
  exact ⟨by linear_combination h1, by linear_combination h2⟩

end Examples

end Dynacert.Linear
