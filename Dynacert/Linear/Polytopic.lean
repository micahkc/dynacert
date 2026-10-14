import Dynacert.Linear.Channels

/-!
# Polytopic certificates: one storage function for a family of linear systems

For vertex matrices `A₀, …, A_{k-1}` and a common input matrix `B`, a single `P` with the
per-channel LMI at every vertex certifies every system `ẋ = A(t) x + B w` whose matrix is
a convex combination `A(t) = Σᵢ λᵢ(t) Aᵢ` at each time. This covers interval parameter
uncertainty (when the model is affine in the uncertain parameters) and time-varying
operating points.

The convex-combination step needs no matrix LMI over the hull: the supply inequality is
linear in `A`, so it is summed with the weights.
-/

namespace Dynacert.Linear

open Matrix Set Dynacert

variable {n m k : ℕ}

/-- A common quadratic storage for every vertex of a polytope of linear systems. -/
structure PolytopicCert (As : Fin k → Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin m) ℚ)
    where
  P : Matrix (Fin n) (Fin n) ℚ
  α : ℚ
  γ : Fin m → ℚ
  hα : 0 < α
  hγ : ∀ j, 0 ≤ γ j
  P_symm : Pᵀ = P
  lmi : ∀ i, PSDWitness (channelLmi (As i) B P α γ)

namespace PolytopicCert

variable {As : Fin k → Matrix (Fin n) (Fin n) ℚ} {B : Matrix (Fin n) (Fin m) ℚ}

/-- The weighted disturbance energy `Σⱼ γⱼ wⱼ²`. -/
noncomputable def energy (C : PolytopicCert As B) (w : Fin m → ℝ) : ℝ :=
  ∑ j, (C.γ j : ℝ) * (w j * w j)

/-- Componentwise peak bounds give the budget `Σⱼ γⱼ δⱼ²`. -/
theorem energy_le_of_abs_le (C : PolytopicCert As B) {w : Fin m → ℝ} {δ : Fin m → ℚ}
    (hw : ∀ j, |w j| ≤ δ j) : C.energy w ≤ ∑ j, (C.γ j : ℝ) * ((δ j : ℝ) * (δ j : ℝ)) := by
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast C.hγ j)
  have h := hw j
  have h0 : 0 ≤ |w j| := abs_nonneg _
  rw [(abs_mul_abs_self (w j)).symm]
  exact mul_le_mul h h h0 (h0.trans h)

theorem P_symm_real (C : PolytopicCert As B) : (toReal C.P)ᵀ = toReal C.P := by
  rw [toReal, ← transpose_map, C.P_symm]

/-- Supply inequality at one vertex. -/
theorem vertex_supply (C : PolytopicCert As B) (i : Fin k) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    quadDeriv (toReal C.P) x (toReal (As i) *ᵥ x + toReal B *ᵥ w) ≤
      -(C.α : ℝ) * quad (toReal C.P) x + C.energy w := by
  have h := (C.lmi i).quad_nonneg (Sum.elim x w)
  rw [toReal_channelLmi, quad_channelLmi _ _ _ C.P_symm_real] at h
  simp only [quadDeriv, energy]
  linarith

theorem quadDeriv_add (P : Matrix (Fin n) (Fin n) ℝ) (x h₁ h₂ : Fin n → ℝ) :
    quadDeriv P x (h₁ + h₂) = quadDeriv P x h₁ + quadDeriv P x h₂ := by
  simp only [quadDeriv, add_dotProduct, mulVec_add, dotProduct_add]; ring

theorem quadDeriv_smul (P : Matrix (Fin n) (Fin n) ℝ) (x h : Fin n → ℝ) (a : ℝ) :
    quadDeriv P x (a • h) = a * quadDeriv P x h := by
  simp only [quadDeriv, smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul]; ring

/-- Supply inequality for every convex combination of the vertices. -/
theorem supply (C : PolytopicCert As B) (wt : Fin k → ℝ) (hwt : ∀ i, 0 ≤ wt i)
    (hsum : ∑ i, wt i = 1) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    quadDeriv (toReal C.P) x ((∑ i, wt i • toReal (As i)) *ᵥ x + toReal B *ᵥ w) ≤
      -(C.α : ℝ) * quad (toReal C.P) x + C.energy w := by
  have hcomb : (∑ i, wt i • toReal (As i)) *ᵥ x + toReal B *ᵥ w =
      ∑ i, wt i • (toReal (As i) *ᵥ x + toReal B *ᵥ w) := by
    rw [Matrix.sum_mulVec]
    simp only [smul_mulVec, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul]
  have hlin : ∀ s : Finset (Fin k), quadDeriv (toReal C.P) x
      (∑ i ∈ s, wt i • (toReal (As i) *ᵥ x + toReal B *ᵥ w)) =
      ∑ i ∈ s, wt i * quadDeriv (toReal C.P) x (toReal (As i) *ᵥ x + toReal B *ᵥ w) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [quadDeriv]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, quadDeriv_add, quadDeriv_smul, ih]
  rw [hcomb, hlin]
  have hb := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (C.vertex_supply i x w) (hwt i)
  have hr : ∑ i, wt i * (-(C.α : ℝ) * quad (toReal C.P) x + C.energy w) =
      -(C.α : ℝ) * quad (toReal C.P) x + C.energy w := by
    rw [← Finset.sum_mul, hsum, one_mul]
  linarith

/-- **Invariance** of `{xᵀPx ≤ c}` for every solution of a time-varying system inside the
polytope, under disturbances of bounded weighted energy. -/
theorem invariant (C : PolytopicCert As B) {x : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ}
    {wt : ℝ → Fin k → ℝ} {T budget c : ℝ}
    (hcont : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt x
      ((∑ i, wt t i • toReal (As i)) *ᵥ x t + toReal B *ᵥ w t) (Ici t) t)
    (hwt : ∀ t ∈ Ico 0 T, ∀ i, 0 ≤ wt t i) (hsum : ∀ t ∈ Ico 0 T, ∑ i, wt t i = 1)
    (hw : ∀ t ∈ Ico 0 T, C.energy (w t) ≤ budget)
    (h0 : quad (toReal C.P) (x 0) ≤ c) (hc : budget / C.α ≤ c) :
    ∀ t ∈ Icc 0 T, quad (toReal C.P) (x t) ≤ c := by
  have hα : (0 : ℝ) < C.α := by exact_mod_cast C.hα
  have hb := dissipation_bound (v := fun t => quad (toReal C.P) (x t)) (γ := budget) hα
    ((quad_continuous _).comp_continuousOn hcont)
    (fun t ht => quad_hasDirDeriv _ _ _ _ _ (hx t ht))
    (fun t ht => (C.supply (wt t) (hwt t ht) (hsum t ht) (x t) (w t)).trans
      (by linarith [hw t ht]))
  exact fun t ht => (hb t ht).trans (max_le h0 hc)

/-- **Regional invariance.** The polytopic representation of the derivative is needed only
while the state is inside the sublevel `{xᵀPx ≤ c}`; invariance is proved by first exit.
This is the form used for nonlinear systems, whose Jacobian enclosures (and hence vertex
representations) are only valid on a region. Requires the strict budget `budget/α < c`. -/
theorem regional_invariant (C : PolytopicCert As B) {x x' : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ}
    {T budget c : ℝ}
    (hcont : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (x' t) (Ici t) t)
    (hpoly : ∀ t ∈ Ico 0 T, quad (toReal C.P) (x t) ≤ c → ∃ wt : Fin k → ℝ,
      (∀ i, 0 ≤ wt i) ∧ ∑ i, wt i = 1 ∧
        x' t = (∑ i, wt i • toReal (As i)) *ᵥ x t + toReal B *ᵥ w t)
    (hw : ∀ t ∈ Ico 0 T, C.energy (w t) ≤ budget)
    (h0 : quad (toReal C.P) (x 0) ≤ c) (hc : budget / C.α < c) :
    ∀ t ∈ Icc 0 T, quad (toReal C.P) (x t) ≤ c := by
  have hα : (0 : ℝ) < C.α := by exact_mod_cast C.hα
  have hVc : ContinuousOn (fun t => quad (toReal C.P) (x t)) (Icc 0 T) :=
    (quad_continuous _).comp_continuousOn hcont
  have hV' : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun t => quad (toReal C.P) (x t))
      (quadDeriv (toReal C.P) (x t) (x' t)) (Ici t) t :=
    fun t ht => quad_hasDirDeriv _ _ _ _ _ (hx t ht)
  intro t ht
  refine image_le_of_deriv_right_lt_deriv_boundary hVc hV' h0
    (fun _ => hasDerivAt_const _ c) ?_ ht
  intro s hs he
  obtain ⟨wt, hwt, hsum, hrep⟩ := hpoly s hs he.le
  have hsup := C.supply wt hwt hsum (x s) (w s)
  rw [← hrep] at hsup
  have hb : budget < C.α * c := by rwa [div_lt_iff₀ hα, mul_comm] at hc
  simp only at he
  rw [he] at hsup
  linarith [hw s hs]

end PolytopicCert

end Dynacert.Linear
