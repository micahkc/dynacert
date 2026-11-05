import Dynacert.Sector.Cert
import Dynacert.Linear.Polytopic

/-!
# The normal form: a polytope of linear maps plus quadratic constraints

Every certificate method that ends in a quadratic storage reads the closed loop, on a region,
as

  `ẋ = (Σᵢ λᵢ Aᵢ) x + B w`,   `λ` in the simplex,   `0 ≤ ζᵀ Mⱼ ζ` for `ζ = (x, w)`,

where `w` collects everything that is not linear in the state: residuals of nonlinear atoms,
disturbances and interface signals. The polytope carries time variation and uncertain
parameters (reference envelopes, schedules, parameter boxes). The *quadratic constraints*
`Mⱼ` carry what the atom lemmas prove about the residuals on the region:

* a sector `pⱼ = δ qⱼ ⬝ ζ`, `δ ∈ [ℓ, u]` is `(pⱼ - ℓ q ζ)(u q ζ - pⱼ) ≥ 0` (`qcSector`);
* a norm bound `Σ bⱼ wⱼ² ≤ Σ aᵢ xᵢ²`, e.g. `‖r‖ ≤ ℓ ‖x‖` for a vector residual, is a diagonal
  constraint (`qcDiag`);
* any other S-procedure term is a rational matrix.

Peak-bounded channels are charged as energy `Σ γⱼ wⱼ²`, and interconnection supply rates as
`Σ σₖ (rₖ ⬝ ζ)²`, as in `SectorData`.

`QCCert` is the checked LMI, one per vertex, with a common `P`:

  `-[[AᵢᵀP + PAᵢ + αP, PB], [BᵀP, 0]] + diag(0, γ) - Σⱼ τⱼ Mⱼ + Σₖ σₖ rₖrₖᵀ ⪰ 0`.

`QCCert.supply` turns it into `V̇ ≤ -αV + Σ γ w² + Σ σ (r ζ)²` wherever the constraints hold,
for every convex combination of the vertices. `SectorCert` is the one-vertex case with sector
constraints only; `PolytopicCert` is the case without constraints.

This file is the method-independent part. Per model, a generator only supplies the data, the
link `ẋ = …` (algebra on the model's equations) and the facts `0 ≤ ζᵀMⱼζ` (atom lemmas); no
new theorem is needed.
-/

namespace Dynacert.Normal

open Matrix Set Dynacert Dynacert.Linear Dynacert.Sector

variable {n m v c k : ℕ}

/-- Data of a normal-form certificate: `v` vertices, `c` quadratic constraints, `k` supply
terms, over `ζ = (x, w) ∈ ℝⁿ × ℝᵐ`. -/
structure QCData (n m v c k : ℕ) where
  A : Fin v → Matrix (Fin n) (Fin n) ℚ
  B : Matrix (Fin n) (Fin m) ℚ
  qc : Fin c → Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ
  γ : Fin m → ℚ
  σ : Fin k → ℚ
  r : Fin k → Fin n ⊕ Fin m → ℚ
  P : Matrix (Fin n) (Fin n) ℚ
  α : ℚ
  τ : Fin c → ℚ

namespace QCData

variable (D : QCData n m v c k)

/-- The supply form `diag(0, γ) - Σⱼ τⱼ Mⱼ + Σₖ σₖ rₖrₖᵀ`. -/
def supply : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ :=
  diagonal (Sum.elim 0 D.γ) + ∑ j, (-D.τ j) • D.qc j + form D.σ D.r D.r

/-- The LMI at vertex `i`. -/
def lmi (i : Fin v) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ :=
  supplyLmi (D.A i) D.B D.P D.α D.supply

/-- What the atom lemmas must establish about the signals: every constraint is nonnegative. -/
def Holds (x : Fin n → ℝ) (w : Fin m → ℝ) : Prop :=
  ∀ j, 0 ≤ quad (toReal (D.qc j)) (Sum.elim x w)

/-- The charged disturbance energy `Σⱼ γⱼ wⱼ²`. -/
noncomputable def energy (w : Fin m → ℝ) : ℝ := ∑ j, (D.γ j : ℝ) * (w j * w j)

/-- The interconnection supply `Σₖ σₖ (rₖ ⬝ ζ)²`. -/
noncomputable def coupling (x : Fin n → ℝ) (w : Fin m → ℝ) : ℝ :=
  ∑ i, (D.σ i : ℝ) * ((rv (D.r i) ⬝ᵥ Sum.elim x w) * (rv (D.r i) ⬝ᵥ Sum.elim x w))

end QCData

/-- A checked normal-form certificate. Every field is decided by the kernel. -/
structure QCCert (D : QCData n m v c k) where
  hα : 0 < D.α
  hτ : ∀ j, 0 ≤ D.τ j
  hγ : ∀ j, 0 ≤ D.γ j
  P_symm : D.Pᵀ = D.P
  lmi : ∀ i, DomWitness (D.lmi i)

/-! ### Quadratic forms of sums -/

section Sums

variable {ι : Type*} [Fintype ι]

theorem quad_smul {R : Type*} [CommRing R] (a : R) (M : Matrix ι ι R) (x : ι → R) :
    quad (a • M) x = a * quad M x := by
  simp [quad, smul_mulVec, dotProduct_smul]

theorem quad_sum {R : Type*} [CommRing R] {κ : Type*} (s : Finset κ) (M : κ → Matrix ι ι R)
    (x : ι → R) : quad (∑ j ∈ s, M j) x = ∑ j ∈ s, quad (M j) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quad]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, quad_add, ih]

theorem quad_toReal_sum_smul (τ : Fin c → ℚ) (M : Fin c → Matrix ι ι ℚ) (ζ : ι → ℝ) :
    quad (toReal (∑ j, τ j • M j)) ζ = ∑ j, (τ j : ℝ) * quad (toReal (M j)) ζ := by
  have h : toReal (∑ j, τ j • M j) = ∑ j, (τ j : ℝ) • toReal (M j) := by
    ext a b; simp [toReal, Matrix.sum_apply]
  rw [h, quad_sum]
  exact Finset.sum_congr rfl fun j _ => quad_smul _ _ _

end Sums

namespace QCCert

variable {D : QCData n m v c k}

theorem quad_supply (x : Fin n → ℝ) (w : Fin m → ℝ) :
    quad (toReal D.supply) (Sum.elim x w) =
      D.energy w + ∑ j, ((-D.τ j : ℚ) : ℝ) * quad (toReal (D.qc j)) (Sum.elim x w) +
        D.coupling x w := by
  rw [QCData.supply, toReal, Matrix.map_add (Rat.castHom ℝ) (map_add _),
    Matrix.map_add (Rat.castHom ℝ) (map_add _), quad_add, quad_add, ← toReal, ← toReal,
    ← toReal, quad_diag_energy, quad_toReal_sum_smul, quad_form]
  rfl

/-- **Supply at one vertex.** Wherever the constraints hold,
`V̇ ≤ -αV + Σ γ w² + Σ σ (r ζ)²` along `ẋ = Aᵢ x + B w`. -/
theorem vertex_supply (C : QCCert D) (i : Fin v) (x : Fin n → ℝ) (w : Fin m → ℝ)
    (hF : D.Holds x w) :
    quadDeriv (toReal D.P) x (toReal (D.A i) *ᵥ x + toReal D.B *ᵥ w) ≤
      -(D.α : ℝ) * quad (toReal D.P) x + D.energy w + D.coupling x w := by
  have h := supply_le C.P_symm (C.lmi i) x w
  rw [quad_supply] at h
  have hneg : ∑ j, ((-D.τ j : ℚ) : ℝ) * quad (toReal (D.qc j)) (Sum.elim x w) ≤ 0 := by
    refine Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg ?_ (hF j)
    have := C.hτ j
    push_cast; linarith [(by exact_mod_cast this : (0 : ℝ) ≤ D.τ j)]
  linarith

/-- **Supply on the polytope.** For every convex combination of the vertices. -/
theorem supply (C : QCCert D) (wt : Fin v → ℝ) (hwt : ∀ i, 0 ≤ wt i) (hsum : ∑ i, wt i = 1)
    (x : Fin n → ℝ) (w : Fin m → ℝ) (hF : D.Holds x w) :
    quadDeriv (toReal D.P) x ((∑ i, wt i • toReal (D.A i)) *ᵥ x + toReal D.B *ᵥ w) ≤
      -(D.α : ℝ) * quad (toReal D.P) x + D.energy w + D.coupling x w := by
  have hcomb : (∑ i, wt i • toReal (D.A i)) *ᵥ x + toReal D.B *ᵥ w =
      ∑ i, wt i • (toReal (D.A i) *ᵥ x + toReal D.B *ᵥ w) := by
    rw [Matrix.sum_mulVec]
    simp only [smul_mulVec, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul]
  have hlin : ∀ s : Finset (Fin v), quadDeriv (toReal D.P) x
      (∑ i ∈ s, wt i • (toReal (D.A i) *ᵥ x + toReal D.B *ᵥ w)) =
      ∑ i ∈ s, wt i * quadDeriv (toReal D.P) x (toReal (D.A i) *ᵥ x + toReal D.B *ᵥ w) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [quadDeriv]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, PolytopicCert.quadDeriv_add,
        PolytopicCert.quadDeriv_smul, ih]
  rw [hcomb, hlin]
  have hb := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (C.vertex_supply i x w hF) (hwt i)
  have hr : ∑ i, wt i * (-(D.α : ℝ) * quad (toReal D.P) x + D.energy w + D.coupling x w) =
      -(D.α : ℝ) * quad (toReal D.P) x + D.energy w + D.coupling x w := by
    rw [← Finset.sum_mul, hsum, one_mul]
  linarith

/-- The coupling term vanishes when there are no supply terms. -/
@[simp] theorem coupling_zero {D : QCData n m v c 0} (x : Fin n → ℝ) (w : Fin m → ℝ) :
    D.coupling x w = 0 := by
  simp [QCData.coupling]

/-- **Regional invariance.** The normal form and the constraints are needed only while the
state is in the certified sublevel `{xᵀPx ≤ ρ}`; invariance follows by first exit. -/
theorem regional_invariant {D : QCData n m v c 0} (C : QCCert D) {x x' : ℝ → Fin n → ℝ}
    {w : ℝ → Fin m → ℝ} {T budget ρ : ℝ}
    (hcont : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (x' t) (Ici t) t)
    (hnormal : ∀ t ∈ Ico 0 T, quad (toReal D.P) (x t) ≤ ρ → ∃ wt : Fin v → ℝ,
      (∀ i, 0 ≤ wt i) ∧ ∑ i, wt i = 1 ∧
      x' t = (∑ i, wt i • toReal (D.A i)) *ᵥ x t + toReal D.B *ᵥ w t ∧
      D.Holds (x t) (w t) ∧ D.energy (w t) ≤ budget)
    (h0 : quad (toReal D.P) (x 0) ≤ ρ) (hc : budget / D.α < ρ) :
    ∀ t ∈ Icc 0 T, quad (toReal D.P) (x t) ≤ ρ := by
  have hα : (0 : ℝ) < D.α := by exact_mod_cast C.hα
  have hVc : ContinuousOn (fun t => quad (toReal D.P) (x t)) (Icc 0 T) :=
    (quad_continuous _).comp_continuousOn hcont
  have hV' : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun t => quad (toReal D.P) (x t))
      (quadDeriv (toReal D.P) (x t) (x' t)) (Ici t) t :=
    fun t ht => quad_hasDirDeriv _ _ _ _ _ (hx t ht)
  intro t ht
  refine image_le_of_deriv_right_lt_deriv_boundary hVc hV' h0
    (fun _ => hasDerivAt_const _ ρ) ?_ ht
  intro s hs he
  obtain ⟨wt, hwt, hsum, hrep, hF, hE⟩ := hnormal s hs he.le
  have hsup := C.supply wt hwt hsum (x s) (w s) hF
  rw [← hrep, coupling_zero] at hsup
  have hb : budget < D.α * ρ := by rwa [div_lt_iff₀ hα, mul_comm] at hc
  simp only at he
  rw [he] at hsup
  linarith

end QCCert

/-! ### Constraint builders: what atom lemmas produce -/

/-- The sector constraint `(w_j - ℓ q ζ)(u q ζ - w_j) ≥ 0`. -/
def qcSector (q : Fin n ⊕ Fin m → ℚ) (j : Fin m) (lo hi : ℚ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ :=
  form ![1] ![secU q j lo] ![secV q j hi]

theorem quad_qcSector (q : Fin n ⊕ Fin m → ℚ) (j : Fin m) (lo hi : ℚ) (x : Fin n → ℝ)
    (w : Fin m → ℝ) :
    quad (toReal (qcSector q j lo hi)) (Sum.elim x w) =
      (w j - (lo : ℝ) * (rv q ⬝ᵥ Sum.elim x w)) * ((hi : ℝ) * (rv q ⬝ᵥ Sum.elim x w) - w j) := by
  rw [qcSector, quad_form, Fin.sum_univ_one]
  simp only [Matrix.cons_val_zero, Rat.cast_one, one_mul]
  rw [dot_secU, dot_secV, dot_eW]

/-- A sector atom (`p = δ q`, `δ ∈ [ℓ, u]`) satisfies its constraint. -/
theorem qcSector_nonneg {q : Fin n ⊕ Fin m → ℚ} {j : Fin m} {lo hi : ℚ} {x : Fin n → ℝ}
    {w : Fin m → ℝ} (h : ∃ δ ∈ Icc (lo : ℝ) hi, w j = δ * (rv q ⬝ᵥ Sum.elim x w)) :
    0 ≤ quad (toReal (qcSector q j lo hi)) (Sum.elim x w) := by
  obtain ⟨δ, hδ, hp⟩ := h
  rw [quad_qcSector]
  exact sector_nonneg hp hδ

/-- The diagonal constraint `Σ aᵢ xᵢ² - Σ bⱼ wⱼ² ≥ 0`. With `a = ℓ²` and `b` the indicator of
a block of `w`, it is the norm bound `‖w_block‖ ≤ ℓ ‖x‖`. -/
def qcDiag (a : Fin n → ℚ) (b : Fin m → ℚ) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ :=
  diagonal (Sum.elim a (-b))

theorem quad_qcDiag (a : Fin n → ℚ) (b : Fin m → ℚ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    quad (toReal (qcDiag a b)) (Sum.elim x w) =
      ∑ i, (a i : ℝ) * (x i * x i) - ∑ j, (b j : ℝ) * (w j * w j) := by
  have h : toReal (qcDiag a b) =
      diagonal (Sum.elim (fun i => (a i : ℝ)) (fun j => -(b j : ℝ))) := by
    ext (i | i) (j | j) <;> simp [qcDiag, toReal, diagonal_apply] <;> split_ifs <;> simp
  rw [h]
  simp only [quad, dotProduct, mulVec_diagonal, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, neg_mul, mul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

theorem qcDiag_nonneg {a : Fin n → ℚ} {b : Fin m → ℚ} {x : Fin n → ℝ} {w : Fin m → ℝ}
    (h : ∑ j, (b j : ℝ) * (w j * w j) ≤ ∑ i, (a i : ℝ) * (x i * x i)) :
    0 ≤ quad (toReal (qcDiag a b)) (Sum.elim x w) := by
  rw [quad_qcDiag]; linarith

end Dynacert.Normal
