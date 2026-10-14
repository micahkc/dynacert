import Dynacert.Core.Dissipation
import GNC.Control.PolytopicTube

/-!
# Regional quadratic tubes with right derivatives

gnc_lean's tube theorems take two-sided derivatives. dynacert's solution notion uses
continuity on `[0, T]` and right derivatives on `[0, T)`, which admits step disturbances.
This file gives the first-exit invariance argument in that setting, and composes it with
gnc_lean's polytopic vertex supply and a regional residual bound.

Region membership is proved (first exit), never assumed.
-/

namespace Dynacert

open Set GNC.PolytopicTube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem storage_continuous (P : E →L[ℝ] E) : Continuous (storage P) :=
  continuous_id.inner P.continuous

/-- Right derivative of the quadratic storage along a curve. -/
theorem storage_hasDerivWithinAt (P : E →L[ℝ] E)
    (hP : ∀ u v, inner ℝ u (P v) = inner ℝ v (P u))
    {x : ℝ → E} {dx : E} {s : Set ℝ} {t : ℝ} (hx : HasDerivWithinAt x dx s t) :
    HasDerivWithinAt (fun τ => storage P (x τ)) (2 * inner ℝ (x t) (P dx)) s t := by
  simpa only [Function.comp_apply, storage, hP dx (x t), two_mul] using
    hx.inner ℝ (P.hasFDerivAt.comp_hasDerivWithinAt t hx)

/-- **First-exit tube.** If the storage supply `2⟪x, P ẋ⟫ + κ V ≤ β` holds whenever the
state is in the sublevel `{V ≤ ρ}`, and `β < κ ρ`, then a solution starting in the
sublevel stays in it, and `V` decays to `β / κ`. -/
theorem tube_of_supply (P : E →L[ℝ] E) (hP : ∀ u v, inner ℝ u (P v) = inner ℝ v (P u))
    {x x' : ℝ → E} {T κ β ρ : ℝ} (hκ : 0 < κ)
    (hcont : ContinuousOn x (Icc 0 T))
    (hx : ∀ s ∈ Ico 0 T, HasDerivWithinAt x (x' s) (Ici s) s)
    (hinit : storage P (x 0) ≤ ρ) (hbudget : β < κ * ρ)
    (hsupply : ∀ s ∈ Ico 0 T, storage P (x s) ≤ ρ →
      2 * inner ℝ (x s) (P (x' s)) + κ * storage P (x s) ≤ β) :
    ∀ t ∈ Icc 0 T, storage P (x t) ≤ ρ ∧ storage P (x t) ≤ max (storage P (x 0)) (β / κ) := by
  set V := fun t => storage P (x t)
  have hVc : ContinuousOn V (Icc 0 T) := (storage_continuous P).comp_continuousOn hcont
  have hV' : ∀ s ∈ Ico 0 T, HasDerivWithinAt V (2 * inner ℝ (x s) (P (x' s))) (Ici s) s :=
    fun s hs => storage_hasDerivWithinAt P hP (hx s hs)
  have hinv : ∀ t ∈ Icc 0 T, V t ≤ ρ := by
    intro t ht
    refine image_le_of_deriv_right_lt_deriv_boundary hVc hV' hinit
      (fun _ => hasDerivAt_const _ ρ) ?_ ht
    intro s hs he
    have h := hsupply s hs he.le
    change 2 * inner ℝ (x s) (P (x' s)) + κ * V s ≤ β at h
    rw [he] at h
    linarith
  intro t ht
  refine ⟨hinv t ht, ?_⟩
  exact dissipation_bound hκ hVc hV' (fun s hs => by
    have h := hsupply s hs (hinv s ⟨hs.1, hs.2.le⟩)
    change 2 * inner ℝ (x s) (P (x' s)) + κ * V s ≤ β at h
    linarith) t ht

variable {ι W : Type*} [Fintype ι] [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **Polytope + residual tube.** The derivative is a convex combination of vertex fields,
plus a disturbance channel, plus a residual whose supply is bounded by `γ V` on the
sublevel. Vertex inequalities (each discharged by an exact LMI witness), a disturbance
bound `‖d‖ ≤ δ`, and the strict budget `μ δ² < (α - γ) ρ` give invariance and decay. -/
theorem polytopic_residual_tube (P : E →L[ℝ] E) (hP : ∀ u v, inner ℝ u (P v) = inner ℝ v (P u))
    (A : ι → E →L[ℝ] E) (B : W →L[ℝ] E) (weights : ℝ → ι → ℝ) (r : ℝ → E → E)
    {x : ℝ → E} {d : ℝ → W} {T α γ μ δ ρ : ℝ}
    (hμ : 0 ≤ μ) (hdecay : γ < α) (hbudget : μ * δ ^ 2 < (α - γ) * ρ)
    (hvertex : ∀ i y u, 2 * inner ℝ y (P (A i y + B u)) + α * storage P y ≤ μ * ‖u‖ ^ 2)
    (hcont : ContinuousOn x (Icc 0 T))
    (hx : ∀ s ∈ Ico 0 T, HasDerivWithinAt x
      ((∑ i, weights s i • A i (x s)) + B (d s) + r s (x s)) (Ici s) s)
    (hw : ∀ s ∈ Ico 0 T, ∀ i, 0 ≤ weights s i)
    (hsum : ∀ s ∈ Ico 0 T, ∑ i, weights s i = 1)
    (hd : ∀ s ∈ Ico 0 T, ‖d s‖ ≤ δ)
    (hr : ∀ s ∈ Ico 0 T, ∀ y, storage P y ≤ ρ → 2 * inner ℝ y (P (r s y)) ≤ γ * storage P y)
    (hinit : storage P (x 0) ≤ ρ) :
    ∀ t ∈ Icc 0 T, storage P (x t) ≤ ρ ∧
      storage P (x t) ≤ max (storage P (x 0)) (μ * δ ^ 2 / (α - γ)) := by
  refine tube_of_supply P hP (sub_pos.mpr hdecay) hcont hx hinit hbudget ?_
  intro s hs hreg
  have hv := vertex_supply P A B (weights s) α μ (hw s hs) (hsum s hs) hvertex (x s) (d s)
  have hres := hr s hs (x s) hreg
  have hsq : ‖d s‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hd s hs) 2
  have hb := mul_le_mul_of_nonneg_left hsq hμ
  simp only [map_add, inner_add_right] at hv ⊢
  linarith

end Dynacert
