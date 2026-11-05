import Dynacert.Linear.Polytopic

/-!
# Funnels and initial boxes

Two additions to the quadratic dissipation certificates of `Channels` and `Polytopic`:

* **Funnel.** `V̇ ≤ -αV + γ` gives more than the invariance of `{V ≤ max(V₀, γ/α)}` that
  `dissipation_bound` keeps: Mathlib's Grönwall bound is the shrinking level
  `ρ(t) = V₀ e^{-αt} + (γ/α)(1 - e^{-αt})` (`funnel_bound`). `ChannelCert.funnel` and
  `PolytopicCert.funnel` state it for the quadratic certificates with rational constants.
* **Initial box.** When the initial error-frame state ranges over an affine image of a box,
  `z₀ = c + G e` with `|eᵢ| ≤ ρᵢ`, the storage at `t = 0` is bounded by the rational number
  `boxBound P c G ρ = cᵀPc + 2 Σᵢ |(GᵀPc)ᵢ| ρᵢ + Σᵢⱼ |(GᵀPG)ᵢⱼ| ρᵢ ρⱼ`
  (`quad_le_boxBound`), which the kernel evaluates exactly. It equals the maximum of `V`
  over the box vertices whenever a sign vector `s` makes every term `sᵢ (GᵀPc)ᵢ` and
  `sᵢ sⱼ (GᵀPG)ᵢⱼ` nonnegative (always for one or two box coordinates centred at the
  origin); otherwise it is a sound over-estimate.
-/

namespace Dynacert

open Set

/-- The funnel level `ρ(t) = V₀ e^{-αt} + (γ/α)(1 - e^{-αt})`. -/
noncomputable def funnelLevel (V0 α γ t : ℝ) : ℝ :=
  V0 * Real.exp (-α * t) + γ / α * (1 - Real.exp (-α * t))

theorem gronwallBound_neg_eq {δ α γ s : ℝ} (hα : 0 < α) :
    gronwallBound δ (-α) γ s = funnelLevel δ α γ s := by
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hα.ne'), funnelLevel, div_neg]
  ring

/-- **Funnel.** If `v` is continuous on `[0, T]`, has right derivative `v'` on `[0, T)`,
`v' ≤ -α v + γ` with `α > 0`, and `v 0 ≤ V₀`, then `v t ≤ V₀ e^{-αt} + (γ/α)(1 - e^{-αt})`
on `[0, T]`. This is `dissipation_bound` before weakening Grönwall's bound to a maximum. -/
theorem funnel_bound {v v' : ℝ → ℝ} {α γ T V0 : ℝ} (hα : 0 < α)
    (hv : ContinuousOn v (Icc 0 T))
    (hv' : ∀ t ∈ Ico 0 T, HasDerivWithinAt v (v' t) (Ici t) t)
    (hdiss : ∀ t ∈ Ico 0 T, v' t ≤ -α * v t + γ) (h0 : v 0 ≤ V0) :
    ∀ t ∈ Icc 0 T, v t ≤ funnelLevel V0 α γ t := by
  intro t ht
  have hg := le_gronwallBound_of_liminf_deriv_right_le hv
    (fun s hs _r hr => (hv' s hs).liminf_right_slope_le hr) h0 hdiss t ht
  rwa [sub_zero, gronwallBound_neg_eq hα] at hg

/-- The funnel never exceeds the invariant level `max(V₀, γ/α)`. -/
theorem funnelLevel_le_max {V0 α γ t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) :
    funnelLevel V0 α γ t ≤ max V0 (γ / α) := by
  rw [← gronwallBound_neg_eq hα]
  exact gronwallBound_neg_le_max hα ht

variable {n m : ℕ}

/-- Funnel for a general dissipation certificate. -/
theorem DissipationCert.funnel {S : System n m} {W : Set (Fin m → ℝ)} (C : DissipationCert S W)
    {x : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ} {T V0 : ℝ}
    (hx : S.IsSolution x w T) (hw : ∀ t ∈ Ico 0 T, w t ∈ W) (h0 : C.V (x 0) ≤ V0) :
    ∀ t ∈ Icc 0 T, C.V (x t) ≤ funnelLevel V0 C.α C.γ t :=
  funnel_bound C.hα (C.V_cont.comp_continuousOn hx.cont)
    (fun t ht => C.hDV _ _ _ _ (hx.deriv t ht)) (fun t ht => C.dissipation _ _ (hw t ht)) h0

namespace Linear

open Matrix

/-- The funnel with rational data: `ρ(t) = V₀ e^{-αt} + r (1 - e^{-αt})` where `r = budget/α`. -/
theorem funnelLevel_rat {V0 α budget rate : ℚ} (hr : budget / α = rate) (t : ℝ) :
    funnelLevel (V0 : ℝ) (α : ℝ) (budget : ℝ) t =
      (V0 : ℝ) * Real.exp (-(α : ℝ) * t) + (rate : ℝ) * (1 - Real.exp (-(α : ℝ) * t)) := by
  rw [funnelLevel, ← hr, Rat.cast_div]

/-- **Funnel** for a per-channel certificate: started with `V(z₀) ≤ V₀`, under disturbances of
weighted energy at most `budget`, `zᵀPz ≤ V₀ e^{-αt} + (budget/α)(1 - e^{-αt})` on `[0, T]`. -/
theorem ChannelCert.funnel {M : LTIModel n m} (C : ChannelCert M) {x : ℝ → Fin n → ℝ}
    {w : ℝ → Fin m → ℝ} {T : ℝ} {budget V0 rate : ℚ}
    (hx : M.toSystem.IsSolution x w T) (hw : ∀ t ∈ Ico 0 T, C.energy (w t) ≤ budget)
    (h0 : quad (toReal C.P) (x 0) ≤ V0) (hr : budget / C.α = rate) :
    ∀ t ∈ Icc 0 T, quad (toReal C.P) (x t) ≤
      (V0 : ℝ) * Real.exp (-(C.α : ℝ) * t) + (rate : ℝ) * (1 - Real.exp (-(C.α : ℝ) * t)) := by
  intro t ht
  rw [← funnelLevel_rat hr]
  exact (C.toDissipationCert budget).funnel hx hw h0 t ht

/-- **Funnel** for a polytopic certificate (time-varying system inside the polytope). -/
theorem PolytopicCert.funnel {k : ℕ} {As : Fin k → Matrix (Fin n) (Fin n) ℚ}
    {B : Matrix (Fin n) (Fin m) ℚ} (C : PolytopicCert As B) {x : ℝ → Fin n → ℝ}
    {w : ℝ → Fin m → ℝ} {wt : ℝ → Fin k → ℝ} {T : ℝ} {budget V0 rate : ℚ}
    (hcont : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt x
      ((∑ i, wt t i • toReal (As i)) *ᵥ x t + toReal B *ᵥ w t) (Ici t) t)
    (hwt : ∀ t ∈ Ico 0 T, ∀ i, 0 ≤ wt t i) (hsum : ∀ t ∈ Ico 0 T, ∑ i, wt t i = 1)
    (hw : ∀ t ∈ Ico 0 T, C.energy (w t) ≤ budget)
    (h0 : quad (toReal C.P) (x 0) ≤ V0) (hr : budget / C.α = rate) :
    ∀ t ∈ Icc 0 T, quad (toReal C.P) (x t) ≤
      (V0 : ℝ) * Real.exp (-(C.α : ℝ) * t) + (rate : ℝ) * (1 - Real.exp (-(C.α : ℝ) * t)) := by
  intro t ht
  rw [← funnelLevel_rat hr]
  have hα : (0 : ℝ) < C.α := by exact_mod_cast C.hα
  refine funnel_bound (v := fun t => quad (toReal C.P) (x t)) (γ := (budget : ℝ)) hα
    ((quad_continuous _).comp_continuousOn hcont)
    (fun t ht => quad_hasDirDeriv _ _ _ _ _ (hx t ht))
    (fun t ht => (C.supply (wt t) (hwt t ht) (hsum t ht) (x t) (w t)).trans
      (by linarith [hw t ht])) h0 t ht

/-! ### Initial boxes -/

variable {k : ℕ}

/-- Rational bound on `zᵀPz` over `{c + G e | |eᵢ| ≤ ρᵢ}`:
`cᵀPc + 2 Σᵢ |(GᵀPc)ᵢ| ρᵢ + Σᵢⱼ |(GᵀPG)ᵢⱼ| ρᵢ ρⱼ`. -/
def boxBound (P : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (G : Matrix (Fin n) (Fin k) ℚ)
    (ρ : Fin k → ℚ) : ℚ :=
  quad P c + 2 * ∑ i, |(Gᵀ *ᵥ (P *ᵥ c)) i| * ρ i +
    ∑ i, ∑ j, |(Gᵀ * P * G) i j| * (ρ i * ρ j)

/-- Expansion of a quadratic form at an affine point (symmetric `P`). -/
theorem quad_add_mulVec {R : Type*} [CommRing R] (P : Matrix (Fin n) (Fin n) R) (hP : Pᵀ = P)
    (c : Fin n → R) (G : Matrix (Fin n) (Fin k) R) (e : Fin k → R) :
    quad P (c + G *ᵥ e) = quad P c + 2 * ((Gᵀ *ᵥ (P *ᵥ c)) ⬝ᵥ e) + quad (Gᵀ * P * G) e := by
  have h1 : (G *ᵥ e) ⬝ᵥ P *ᵥ c = (Gᵀ *ᵥ (P *ᵥ c)) ⬝ᵥ e := by
    rw [dotProduct_comm, ← dotProduct_transpose_mulVec, dotProduct_comm]
  have h2 : c ⬝ᵥ P *ᵥ (G *ᵥ e) = (G *ᵥ e) ⬝ᵥ P *ᵥ c := by
    conv_lhs => rw [← hP]
    rw [dotProduct_transpose_mulVec]
  have h3 : quad (Gᵀ * P * G) e = (G *ᵥ e) ⬝ᵥ P *ᵥ (G *ᵥ e) := by
    rw [quad, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]
  rw [h3]
  simp only [quad, add_dotProduct, mulVec_add, dotProduct_add]
  rw [h2, h1]
  ring

/-- **Initial box.** For symmetric `P`, `V(c + G e) ≤ boxBound P c G ρ` whenever
`|eᵢ| ≤ ρᵢ`. -/
theorem quad_le_boxBound {P : Matrix (Fin n) (Fin n) ℚ} {c : Fin n → ℚ}
    {G : Matrix (Fin n) (Fin k) ℚ} {ρ : Fin k → ℚ} {L : ℚ} (hP : Pᵀ = P)
    (hL : boxBound P c G ρ ≤ L) (e : Fin k → ℝ) (he : ∀ i, |e i| ≤ ρ i) :
    quad (toReal P) (fun i => (c i : ℝ) + (toReal G *ᵥ e) i) ≤ L := by
  have hPr : (toReal P)ᵀ = toReal P := by rw [toReal, ← transpose_map, hP]
  set cr : Fin n → ℝ := fun i => (c i : ℝ)
  have hz : (fun i => (c i : ℝ) + (toReal G *ᵥ e) i) = cr + toReal G *ᵥ e := rfl
  rw [hz, quad_add_mulVec _ hPr]
  -- the linear and quadratic terms, entrywise casts of rational data
  have hg : ∀ i, ((toReal G)ᵀ *ᵥ (toReal P *ᵥ cr)) i = (((Gᵀ *ᵥ (P *ᵥ c)) i : ℚ) : ℝ) := by
    intro i
    simp [cr, toReal, mulVec, dotProduct, Finset.mul_sum]
  have hQ : ∀ i j, ((toReal G)ᵀ * toReal P * toReal G) i j = (((Gᵀ * P * G) i j : ℚ) : ℝ) := by
    intro i j
    simp [toReal, Matrix.mul_apply, Finset.sum_mul]
  have hc : quad (toReal P) cr = ((quad P c : ℚ) : ℝ) := quad_toReal_cast P c
  have hlin : (toReal G)ᵀ *ᵥ (toReal P *ᵥ cr) ⬝ᵥ e ≤
      ∑ i, |(((Gᵀ *ᵥ (P *ᵥ c)) i : ℚ) : ℝ)| * (ρ i : ℝ) := by
    simp only [dotProduct, hg]
    refine Finset.sum_le_sum fun i _ => ?_
    calc (((Gᵀ *ᵥ (P *ᵥ c)) i : ℚ) : ℝ) * e i
        ≤ |(((Gᵀ *ᵥ (P *ᵥ c)) i : ℚ) : ℝ) * e i| := le_abs_self _
      _ = |(((Gᵀ *ᵥ (P *ᵥ c)) i : ℚ) : ℝ)| * |e i| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
  have hquad : quad ((toReal G)ᵀ * toReal P * toReal G) e ≤
      ∑ i, ∑ j, |(((Gᵀ * P * G) i j : ℚ) : ℝ)| * ((ρ i : ℝ) * (ρ j : ℝ)) := by
    simp only [quad, dotProduct, mulVec, Finset.mul_sum, hQ]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hi := he i
    have hj := he j
    calc e i * ((((Gᵀ * P * G) i j : ℚ) : ℝ) * e j)
        ≤ |e i * ((((Gᵀ * P * G) i j : ℚ) : ℝ) * e j)| := le_abs_self _
      _ = |(((Gᵀ * P * G) i j : ℚ) : ℝ)| * (|e i| * |e j|) := by
          rw [abs_mul, abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul hi hj (abs_nonneg _) ((abs_nonneg _).trans hi)) (abs_nonneg _)
  have hB : ((boxBound P c G ρ : ℚ) : ℝ) = ((quad P c : ℚ) : ℝ) +
      2 * ∑ i, |(((Gᵀ *ᵥ (P *ᵥ c)) i : ℚ) : ℝ)| * (ρ i : ℝ) +
      ∑ i, ∑ j, |(((Gᵀ * P * G) i j : ℚ) : ℝ)| * ((ρ i : ℝ) * (ρ j : ℝ)) := by
    simp only [boxBound]
    push_cast
    rfl
  have hL' : ((boxBound P c G ρ : ℚ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  rw [hc]
  linarith

end Linear

end Dynacert
