import Dynacert.Linear.Channels

/-!
# Dissipation LMIs with a quadratic supply, checked by diagonal dominance

The sector-multiplier certificate of "Where to Tear" (Theorem 1, LMI (8)) and the subsystem
inequalities of its compositional version (Proposition 1, LMI (9)) have the same shape: for
`ζ = (x, w)` with `ẋ = A x + B w`,

  `V̇ + α V ≤ ζᵀ S ζ`,   `V x = xᵀ P x`,

where the *supply form* `S` collects the disturbance energy `Σ γⱼ wⱼ²`, the sector terms
`-τᵢ (pᵢ - ℓᵢ qᵢ)(uᵢ qᵢ - pᵢ)` and the interconnection supply rates. Every one of these is a
weighted product of two linear forms in `ζ`, so `S` is given as a list of such products
(`form`), and `quad_form` evaluates it once and for all.

The matrix inequality `supplyLmi A B P α S ⪰ 0` is checked with a `DomWitness`: a rational
`Lᵀ diag(d) L` (rounded from a floating-point factorization) plus a remainder that is checked to
be diagonally dominant. Unlike an exact `LDLᵀ`, the data stay small (no denominator blow-up),
so the kernel check is cheap even for 15×15 LMIs.
-/

namespace Dynacert.Sector

open Matrix Set Dynacert Dynacert.Linear

/-! ### PSD by factorization plus a diagonally dominant remainder -/

section Dom

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weak diagonal dominance of a (not necessarily symmetric) rational matrix, in the form used
for the quadratic form: `Σ_{j ≠ i} (|Rᵢⱼ| + |Rⱼᵢ|)/2 ≤ Rᵢᵢ`. -/
def DiagDom (R : Matrix ι ι ℚ) : Prop :=
  ∀ i, ∑ j, (if j = i then 0 else (|R i j| + |R j i|) / 2) ≤ R i i

instance (R : Matrix ι ι ℚ) : Decidable (DiagDom R) := by
  unfold DiagDom; infer_instance

theorem quad_nonneg_of_diagDom {R : Matrix ι ι ℚ} (h : DiagDom R) (x : ι → ℝ) :
    0 ≤ quad (toReal R) x := by
  have hq : quad (toReal R) x = ∑ i, ∑ j, (R i j : ℝ) * x i * x j := by
    simp only [quad, dotProduct, mulVec, toReal, Matrix.map_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by simp; ring
  -- termwise lower bound
  have hterm : ∀ i j, (if j = i then (R i i : ℝ) * x i * x i
      else -(|(R i j : ℝ)| * (x i * x i + x j * x j) / 2)) ≤ (R i j : ℝ) * x i * x j := by
    intro i j
    split_ifs with hji
    · subst hji; exact le_rfl
    · have h1 : -(|(R i j : ℝ)| * (x i * x i + x j * x j) / 2) ≤ (R i j : ℝ) * (x i * x j) := by
        have hab : |x i * x j| ≤ (x i * x i + x j * x j) / 2 := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x i + x j), sq_nonneg (x i - x j)]
        have := neg_abs_le ((R i j : ℝ) * (x i * x j))
        rw [abs_mul] at this
        nlinarith [abs_nonneg (R i j : ℝ), abs_nonneg (x i * x j)]
      linarith [mul_assoc (R i j : ℝ) (x i) (x j)]
  have hsum : ∑ i, ∑ j, (if j = i then (R i i : ℝ) * x i * x i
      else -(|(R i j : ℝ)| * (x i * x i + x j * x j) / 2)) ≤ quad (toReal R) x := by
    rw [hq]; exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  -- rewrite the lower bound as `Σᵢ xᵢ² (Rᵢᵢ - Σ_{j≠i} (|Rᵢⱼ| + |Rⱼᵢ|)/2)`
  have hsplit : ∀ i j, (if j = i then (R i i : ℝ) * x i * x i
      else -(|(R i j : ℝ)| * (x i * x i + x j * x j) / 2)) =
      (if j = i then (R i i : ℝ) * x i * x i else 0)
        - (if j = i then 0 else |(R i j : ℝ)| / 2 * (x i * x i))
        - (if j = i then 0 else |(R i j : ℝ)| / 2 * (x j * x j)) := by
    intro i j; split_ifs <;> ring
  have hdiag : ∀ i, ∑ j, (if j = i then (R i i : ℝ) * x i * x i else 0) = R i i * x i * x i := by
    intro i; rw [Finset.sum_ite_eq']; simp
  have hswap : ∑ i, ∑ j, (if j = i then (0 : ℝ) else |(R i j : ℝ)| / 2 * (x j * x j)) =
      ∑ i, ∑ j, (if j = i then (0 : ℝ) else |(R j i : ℝ)| / 2 * (x i * x i)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij)]
  have hlow : ∑ i, ∑ j, (if j = i then (R i i : ℝ) * x i * x i
      else -(|(R i j : ℝ)| * (x i * x i + x j * x j) / 2)) =
      ∑ i, x i * x i * ((R i i : ℝ) -
        ∑ j, (if j = i then 0 else (|(R i j : ℝ)| + |(R j i : ℝ)|) / 2)) := by
    simp_rw [hsplit, Finset.sum_sub_distrib, hdiag]
    rw [hswap, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_sub, Finset.mul_sum, sub_sub, ← Finset.sum_add_distrib]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
  have hrow : ∀ i, 0 ≤ (R i i : ℝ) -
      ∑ j, (if j = i then 0 else (|(R i j : ℝ)| + |(R j i : ℝ)|) / 2) := by
    intro i
    have := h i
    have hc : ((∑ j, (if j = i then 0 else (|R i j| + |R j i|) / 2) : ℚ) : ℝ) =
        ∑ j, (if j = i then 0 else (|(R i j : ℝ)| + |(R j i : ℝ)|) / 2) := by
      push_cast; refine Finset.sum_congr rfl fun j _ => ?_; split_ifs <;> simp
    have : ((∑ j, (if j = i then 0 else (|R i j| + |R j i|) / 2) : ℚ) : ℝ) ≤ (R i i : ℝ) := by
      exact_mod_cast this
    linarith
  have : 0 ≤ ∑ i, x i * x i * ((R i i : ℝ) -
      ∑ j, (if j = i then 0 else (|(R i j : ℝ)| + |(R j i : ℝ)|) / 2)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_self_nonneg _) (hrow i)
  linarith

/-- A certificate that `M ⪰ 0`: `M = Lᵀ diag(d) L + R` with `d ≥ 0` and `R` diagonally
dominant. Both conditions are decided by the kernel. -/
structure DomWitness (M : Matrix ι ι ℚ) where
  L : Matrix ι ι ℚ
  d : ι → ℚ
  d_nonneg : ∀ i, 0 ≤ d i
  dom : DiagDom (M - Lᵀ * diagonal d * L)

omit [DecidableEq ι] in
theorem quad_add {R : Type*} [CommRing R] (M N : Matrix ι ι R) (x : ι → R) :
    quad (M + N) x = quad M x + quad N x := by
  simp [quad, add_mulVec, dotProduct_add]

theorem DomWitness.quad_nonneg {M : Matrix ι ι ℚ} (W : DomWitness M) (x : ι → ℝ) :
    0 ≤ quad (toReal M) x := by
  have hM : M = W.Lᵀ * diagonal W.d * W.L + (M - W.Lᵀ * diagonal W.d * W.L) := by abel
  have h1 := (PSDWitness.quad_nonneg ⟨W.L, W.d, W.d_nonneg, rfl⟩ x)
  have h2 := quad_nonneg_of_diagDom W.dom x
  rw [hM, toReal, Matrix.map_add (Rat.castHom ℝ) (map_add _), quad_add]
  exact add_nonneg h1 h2

end Dom

/-! ### Supply forms: sums of weighted products of linear forms -/

section Form

variable {ι : Type*} [Fintype ι] {k : ℕ}

/-- `form κ u v` is the symmetric matrix of the quadratic form
`ζ ↦ Σᵢ κᵢ (uᵢ ⬝ ζ)(vᵢ ⬝ ζ)`. -/
def form (κ : Fin k → ℚ) (u v : Fin k → ι → ℚ) : Matrix ι ι ℚ :=
  Matrix.of fun a b => ∑ i, κ i * (u i a * v i b + v i a * u i b) / 2

/-- A rational linear form, cast to the reals. -/
abbrev rv (u : ι → ℚ) : ι → ℝ := fun a => (u a : ℝ)

theorem quad_form (κ : Fin k → ℚ) (u v : Fin k → ι → ℚ) (ζ : ι → ℝ) :
    quad (toReal (form κ u v)) ζ = ∑ i, (κ i : ℝ) * ((rv (u i) ⬝ᵥ ζ) * (rv (v i) ⬝ᵥ ζ)) := by
  have key : ∀ i, (rv (u i) ⬝ᵥ ζ) * (rv (v i) ⬝ᵥ ζ) =
      ∑ a, ∑ b, ζ a * (((u i a : ℝ) * (v i b : ℝ) + (v i a : ℝ) * (u i b : ℝ)) / 2) * ζ b := by
    intro i
    have h1 : (rv (u i) ⬝ᵥ ζ) * (rv (v i) ⬝ᵥ ζ) =
        ∑ a, ∑ b, ζ a * ((u i a : ℝ) * (v i b : ℝ)) * ζ b := by
      simp only [dotProduct, rv, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have h2 : (rv (u i) ⬝ᵥ ζ) * (rv (v i) ⬝ᵥ ζ) =
        ∑ a, ∑ b, ζ a * ((v i a : ℝ) * (u i b : ℝ)) * ζ b := by
      rw [mul_comm]
      simp only [dotProduct, rv, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have h3 : ∑ a, ∑ b, ζ a * (((u i a : ℝ) * (v i b : ℝ) + (v i a : ℝ) * (u i b : ℝ)) / 2)
        * ζ b = ((∑ a, ∑ b, ζ a * ((u i a : ℝ) * (v i b : ℝ)) * ζ b) +
          (∑ a, ∑ b, ζ a * ((v i a : ℝ) * (u i b : ℝ)) * ζ b)) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [h3, ← h1, ← h2]; ring
  simp_rw [key]
  simp only [quad, dotProduct, mulVec, toReal, form, Matrix.map_apply, Matrix.of_apply]
  simp only [Rat.coe_castHom, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_add,
    Rat.cast_ofNat]
  have lhs : ∀ a, ζ a * ∑ b, (∑ i, (κ i : ℝ) * ((u i a : ℝ) * (v i b : ℝ) + (v i a : ℝ) *
      (u i b : ℝ)) / 2) * ζ b = ∑ i, ∑ b, (κ i : ℝ) * (ζ a * (((u i a : ℝ) * (v i b : ℝ) +
      (v i a : ℝ) * (u i b : ℝ)) / 2) * ζ b) := by
    intro a
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [lhs, Finset.mul_sum]
  rw [Finset.sum_comm]

end Form

/-! ### The supply LMI -/

section Supply

variable {n m : ℕ}

/-- `supplyLmi A B P α S = -[[AᵀP + PA + αP, PB], [BᵀP, 0]] + S`. Its quadratic form at
`ζ = (x, w)` is `-(V̇ + α V) + ζᵀ S ζ` for `ẋ = A x + B w`, `V = xᵀ P x`. -/
def supplyLmi (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin m) ℚ)
    (P : Matrix (Fin n) (Fin n) ℚ) (α : ℚ) (S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ :=
  channelLmi A B P α 0 + S

/-- **Supply inequality.** A witness of `supplyLmi A B P α S ⪰ 0` gives, for every state `x`
and every `w`, `V̇ ≤ -α V + ζᵀ S ζ` along `ẋ = A x + B w`. -/
theorem supply_le {A : Matrix (Fin n) (Fin n) ℚ} {B : Matrix (Fin n) (Fin m) ℚ}
    {P : Matrix (Fin n) (Fin n) ℚ} {α : ℚ} {S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ}
    (hP : Pᵀ = P) (W : DomWitness (supplyLmi A B P α S)) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    quadDeriv (toReal P) x (toReal A *ᵥ x + toReal B *ᵥ w) ≤
      -(α : ℝ) * quad (toReal P) x + quad (toReal S) (Sum.elim x w) := by
  have h := W.quad_nonneg (Sum.elim x w)
  have hPr : (toReal P)ᵀ = toReal P := by rw [toReal, ← transpose_map, hP]
  rw [supplyLmi, toReal, Matrix.map_add (Rat.castHom ℝ) (map_add _), quad_add,
    ← toReal, ← toReal, toReal_channelLmi, quad_channelLmi _ _ _ hPr] at h
  simp only [quadDeriv, Pi.zero_apply, Rat.cast_zero, zero_mul, Finset.sum_const_zero,
    add_zero] at h ⊢
  linarith

end Supply

end Dynacert.Sector
