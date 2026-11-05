import Dynacert.Core.QuadForm

/-!
# Univariate matrix sums of squares on `[0, 1]`

A symmetric matrix polynomial `G(s) = Σ_ℓ s^ℓ G_ℓ` (`ℓ < 2d+1`) is positive semidefinite for
every `s ∈ [0, 1]` if it has the Gram form

`G(s) = Z_d(s)ᵀ Q₀ Z_d(s) + s (1 - s) Z_{d-1}(s)ᵀ Q₁ Z_{d-1}(s)`,  `Q₀, Q₁ ⪰ 0`,

with `Z_d(s) = [I, sI, …, s^d I]ᵀ` (Condie, Woodbury, Pant, Goppert, *Continuous-time certified
invariant funnels …*, Proposition 1). The identity is linear in the coefficients:
`G_ℓ = Σ_{a+b=ℓ} Q₀^{[a,b]} + Σ_{a+b=ℓ-1} Q₁^{[a,b]} - Σ_{a+b=ℓ-2} Q₁^{[a,b]}` (`gramCoeff`), so
the kernel checks it exactly (`decide +kernel`), and `PSDWitness` checks `Q₀` and `Q₁`. The
Gram matrices are indexed by `Fin (d+1) × ι`: block `[a, b]` is `fun i j => Q (a, i) (b, j)`.
-/

namespace Dynacert.Nonlinear

open Matrix Finset Dynacert

variable {ι : Type*} [Fintype ι]

/-- Coefficient `ℓ` of the Gram form. -/
def gramCoeff {d : ℕ} (Q0 : Matrix (Fin (d + 1) × ι) (Fin (d + 1) × ι) ℚ)
    (Q1 : Matrix (Fin d × ι) (Fin d × ι) ℚ) (ℓ : ℕ) : Matrix ι ι ℚ :=
  fun i j =>
    (∑ a : Fin (d + 1), ∑ b : Fin (d + 1), if (a : ℕ) + b = ℓ then Q0 (a, i) (b, j) else 0)
    + ∑ a : Fin d, ∑ b : Fin d,
        ((if (a : ℕ) + b + 1 = ℓ then Q1 (a, i) (b, j) else 0)
          - if (a : ℕ) + b + 2 = ℓ then Q1 (a, i) (b, j) else 0)

/-- Index of block `a`, entry `i` of a Gram matrix, flattened through `e : ι ≃ Fin ν`. -/
def gramIdx {D ν : ℕ} (e : ι ≃ Fin ν) : Fin D × ι ≃ Fin (D * ν) :=
  (Equiv.prodCongr (Equiv.refl _) e).trans finProdFinEquiv

/-- A Gram matrix given by a flat rational matrix. -/
def gramOf {D ν : ℕ} (e : ι ≃ Fin ν) (F : Matrix (Fin (D * ν)) (Fin (D * ν)) ℚ) :
    Matrix (Fin D × ι) (Fin D × ι) ℚ :=
  fun p q => F (gramIdx e p) (gramIdx e q)

/-- A univariate SOS certificate that `Σ_{ℓ < 2d+1} s^ℓ M ℓ ⪰ 0` on `[0, 1]`. The Gram
matrices are flat (`Fin` indexed, so they can be written as literals) and reindexed by `e`. -/
structure SOSCert [DecidableEq ι] {ν : ℕ} (d : ℕ) (e : ι ≃ Fin ν) (M : ℕ → Matrix ι ι ℚ) where
  F0 : Matrix (Fin ((d + 1) * ν)) (Fin ((d + 1) * ν)) ℚ
  F1 : Matrix (Fin (d * ν)) (Fin (d * ν)) ℚ
  psd0 : PSDWitness F0
  psd1 : PSDWitness F1
  coeff : ∀ ℓ : Fin (2 * d + 1), M ℓ = gramCoeff (gramOf e F0) (gramOf e F1) ℓ

/-- Gram data of a univariate SOS certificate, as plain rational matrices (so a family of them
can be written as a nested vector literal): the flat Gram matrices and their `LDLᵀ` witnesses. -/
structure GramData (K0 K1 : ℕ) where
  F0 : Matrix (Fin K0) (Fin K0) ℚ
  L0 : Matrix (Fin K0) (Fin K0) ℚ
  D0 : Fin K0 → ℚ
  F1 : Matrix (Fin K1) (Fin K1) ℚ
  L1 : Matrix (Fin K1) (Fin K1) ℚ
  D1 : Fin K1 → ℚ

/-- The kernel's check of a `GramData` against the coefficients `M`. -/
def GramData.Valid [DecidableEq ι] {ν : ℕ} (d : ℕ) (e : ι ≃ Fin ν)
    (g : GramData ((d + 1) * ν) (d * ν)) (M : ℕ → Matrix ι ι ℚ) : Prop :=
  (∀ r, 0 ≤ g.D0 r) ∧ g.F0 = g.L0ᵀ * diagonal g.D0 * g.L0 ∧
  (∀ r, 0 ≤ g.D1 r) ∧ g.F1 = g.L1ᵀ * diagonal g.D1 * g.L1 ∧
  ∀ ℓ : Fin (2 * d + 1), M ℓ = gramCoeff (gramOf e g.F0) (gramOf e g.F1) ℓ

instance [DecidableEq ι] {ν : ℕ} (d : ℕ) (e : ι ≃ Fin ν) (g : GramData ((d + 1) * ν) (d * ν))
    (M : ℕ → Matrix ι ι ℚ) : Decidable (g.Valid d e M) := by
  unfold GramData.Valid; infer_instance

/-- A checked `GramData` is an SOS certificate. -/
def GramData.toCert [DecidableEq ι] {ν d : ℕ} {e : ι ≃ Fin ν} {g : GramData ((d + 1) * ν) (d * ν)}
    {M : ℕ → Matrix ι ι ℚ} (h : g.Valid d e M) : SOSCert d e M where
  F0 := g.F0
  F1 := g.F1
  psd0 := ⟨g.L0, g.D0, h.1, h.2.1⟩
  psd1 := ⟨g.L1, g.D1, h.2.2.1, h.2.2.2.1⟩
  coeff := h.2.2.2.2

/-- The quadratic form as a double sum. -/
theorem quad_eq_sum {κ : Type*} [Fintype κ] (M : Matrix κ κ ℝ) (z : κ → ℝ) :
    quad M z = ∑ i, ∑ j, z i * M i j * z j := by
  simp only [quad, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Collapsing a sum over `ℓ` against an indicator `k a b = ℓ`. -/
theorem sum_range_indicator {α β : Type*} [Fintype α] [Fintype β] (N : ℕ) (k : α → β → ℕ)
    (hk : ∀ a b, k a b < N) (g : ℕ → ℝ) (f : α → β → ℝ) :
    ∑ ℓ ∈ range N, g ℓ * (∑ a, ∑ b, if k a b = ℓ then f a b else 0) =
      ∑ a, ∑ b, g (k a b) * f a b := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq (range N) (k a b) (fun ℓ => g ℓ * f a b)]
  simp [hk a b]

/-- The Gram vector `Z_d(s) z`: component `(a, i)` is `s^a z_i`. -/
def gramVec {d : ℕ} (s : ℝ) (z : ι → ℝ) : Fin d × ι → ℝ := fun p => s ^ (p.1 : ℕ) * z p.2

/-- The quadratic form of a Gram matrix at `Z_d(s) z`, block by block. -/
theorem quad_gramVec {d : ℕ} (Q : Matrix (Fin d × ι) (Fin d × ι) ℝ) (s : ℝ) (z : ι → ℝ) :
    quad Q (gramVec s z) =
      ∑ a : Fin d, ∑ b : Fin d, s ^ ((a : ℕ) + b) * ∑ i, ∑ j, z i * Q (a, i) (b, j) * z j := by
  rw [quad_eq_sum, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [gramVec, pow_add]
  ring

/-- Interchange of two double sums. -/
theorem sum4_comm {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, F i j a b = ∑ a, ∑ b, ∑ i, ∑ j, F i j a b :=
  calc ∑ i, ∑ j, ∑ a, ∑ b, F i j a b = ∑ i, ∑ a, ∑ j, ∑ b, F i j a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, F i j a b := Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, F i j a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The block form `X a b = Σᵢⱼ zᵢ Q(a,i)(b,j) zⱼ`. -/
noncomputable def blockForm {κ : Type*} [Fintype κ] (Q : Matrix (κ × ι) (κ × ι) ℚ) (z : ι → ℝ)
    (a b : κ) : ℝ :=
  ∑ i, ∑ j, z i * (Q (a, i) (b, j) : ℝ) * z j

theorem sum_ite_block {α β : Type*} [Fintype α] [Fintype β] (c : α → β → Prop)
    [∀ a b, Decidable (c a b)] (F : ι → ι → α → β → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, (if c a b then F i j a b else 0) =
      ∑ a, ∑ b, if c a b then ∑ i, ∑ j, F i j a b else 0 := by
  rw [sum4_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : c a b <;> simp [h]

/-- The quadratic form of one Gram coefficient, block by block. -/
theorem quad_gramCoeff {d : ℕ} (Q0 : Matrix (Fin (d + 1) × ι) (Fin (d + 1) × ι) ℚ)
    (Q1 : Matrix (Fin d × ι) (Fin d × ι) ℚ) (ℓ : ℕ) (z : ι → ℝ) :
    quad (toReal (gramCoeff Q0 Q1 ℓ)) z =
      (∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
          if (a : ℕ) + b = ℓ then blockForm Q0 z a b else 0)
        + (∑ a : Fin d, ∑ b : Fin d, if (a : ℕ) + b + 1 = ℓ then blockForm Q1 z a b else 0)
        - (∑ a : Fin d, ∑ b : Fin d, if (a : ℕ) + b + 2 = ℓ then blockForm Q1 z a b else 0) := by
  rw [quad_eq_sum]
  have h : ∀ i j, z i * (toReal (gramCoeff Q0 Q1 ℓ)) i j * z j =
      (∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
          if (a : ℕ) + b = ℓ then z i * (Q0 (a, i) (b, j) : ℝ) * z j else 0)
        + (∑ a : Fin d, ∑ b : Fin d,
            if (a : ℕ) + b + 1 = ℓ then z i * (Q1 (a, i) (b, j) : ℝ) * z j else 0)
        - (∑ a : Fin d, ∑ b : Fin d,
            if (a : ℕ) + b + 2 = ℓ then z i * (Q1 (a, i) (b, j) : ℝ) * z j else 0) := by
    intro i j
    have hc : ∀ (c : Prop) [Decidable c] (q : ℚ),
        z i * ((if c then q else 0 : ℚ) : ℝ) * z j = if c then z i * (q : ℝ) * z j else 0 := by
      intro c _ q; split_ifs <;> simp
    simp only [gramCoeff, toReal, map_apply, Rat.coe_castHom, Rat.cast_add, Rat.cast_sum,
      Rat.cast_sub, Finset.sum_sub_distrib, mul_add, add_mul, mul_sub, sub_mul, Finset.mul_sum,
      Finset.sum_mul, hc]
    ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h i j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_ite_block, sum_ite_block, sum_ite_block]
  rfl

/-- Reindexing a quadratic form along an equivalence. -/
theorem quad_reindex {α κ : Type*} [Fintype α] [Fintype κ] (f : α ≃ κ) (F : Matrix κ κ ℝ)
    (z : α → ℝ) : quad (fun p q => F (f p) (f q)) z = quad F (z ∘ f.symm) := by
  rw [quad_eq_sum, quad_eq_sum]
  rw [← Equiv.sum_comp f.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp f.symm]
  simp

theorem gramOf_nonneg {D ν : ℕ} (e : ι ≃ Fin ν) {F : Matrix (Fin (D * ν)) (Fin (D * ν)) ℚ}
    (W : PSDWitness F) (z : Fin D × ι → ℝ) : 0 ≤ quad (toReal (gramOf e F)) z := by
  have h : toReal (gramOf e F) = fun p q => (toReal F) (gramIdx e p) (gramIdx e q) := by
    ext p q; simp [gramOf, toReal]
  rw [h, quad_reindex]
  exact W.quad_nonneg _

/-- **Gram identity.** Under the coefficient identity, the polynomial's quadratic form is
`quad Q₀ (Z_d z) + s (1 - s) quad Q₁ (Z_{d-1} z)`. -/
theorem SOSCert.quad_eq [DecidableEq ι] {ν d : ℕ} {e : ι ≃ Fin ν} {M : ℕ → Matrix ι ι ℚ}
    (C : SOSCert d e M) (s : ℝ)
    (z : ι → ℝ) :
    ∑ ℓ ∈ range (2 * d + 1), s ^ ℓ * quad (toReal (M ℓ)) z =
      quad (toReal (gramOf e C.F0)) (gramVec s z)
        + s * (1 - s) * quad (toReal (gramOf e C.F1)) (gramVec s z) := by
  have hk0 : ∀ a b : Fin (d + 1), (a : ℕ) + b < 2 * d + 1 := fun a b => by omega
  have hk1 : ∀ a b : Fin d, (a : ℕ) + b + 1 < 2 * d + 1 := fun a b => by omega
  have hk2 : ∀ a b : Fin d, (a : ℕ) + b + 2 < 2 * d + 1 := fun a b => by omega
  have hM : ∀ ℓ ∈ range (2 * d + 1), quad (toReal (M ℓ)) z =
      quad (toReal (gramCoeff (gramOf e C.F0) (gramOf e C.F1) ℓ)) z := fun ℓ hℓ => by
    rw [C.coeff ⟨ℓ, mem_range.mp hℓ⟩]
  rw [Finset.sum_congr rfl (g := fun ℓ => s ^ ℓ * quad (toReal (gramCoeff (gramOf e C.F0) (gramOf e C.F1) ℓ)) z)
    fun ℓ hℓ => by rw [hM ℓ hℓ]]
  simp only [quad_gramCoeff, mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_range_indicator _ _ hk0, sum_range_indicator _ _ hk1, sum_range_indicator _ _ hk2,
    quad_gramVec, quad_gramVec]
  have e1 : (∑ a : Fin d, ∑ b : Fin d, s ^ ((a : ℕ) + b + 1) * blockForm (gramOf e C.F1) z a b)
      - (∑ a : Fin d, ∑ b : Fin d, s ^ ((a : ℕ) + b + 2) * blockForm (gramOf e C.F1) z a b) =
      (s * 1 - s * s) * ∑ a : Fin d, ∑ b : Fin d, s ^ ((a : ℕ) + b) * blockForm (gramOf e C.F1) z a b := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [add_sub_assoc, e1]
  simp [blockForm, toReal]

/-- **Proposition 1.** A checked Gram certificate makes the matrix polynomial positive
semidefinite at every `s ∈ [0, 1]`. -/
theorem SOSCert.nonneg [DecidableEq ι] {ν d : ℕ} {e : ι ≃ Fin ν} {M : ℕ → Matrix ι ι ℚ}
    (C : SOSCert d e M) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (z : ι → ℝ) :
    0 ≤ ∑ ℓ ∈ range (2 * d + 1), s ^ ℓ * quad (toReal (M ℓ)) z := by
  rw [C.quad_eq]
  have h0 := gramOf_nonneg e C.psd0 (gramVec s z)
  have h1 := gramOf_nonneg e C.psd1 (gramVec s z)
  have hs1 : 0 ≤ s * (1 - s) := mul_nonneg hs.1 (by linarith [hs.2])
  nlinarith [mul_nonneg hs1 h1]

end Dynacert.Nonlinear
