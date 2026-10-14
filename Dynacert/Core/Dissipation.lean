import Mathlib

/-!
# Dissipation comparison lemma


This is the analytic heart of every dissipation-style certificate; it is a corollary of
Mathlib's Grönwall inequality.
-/

namespace Dynacert

open Set

theorem gronwallBound_neg_le_max {δ α γ s : ℝ} (hα : 0 < α) (hs : 0 ≤ s) :
    gronwallBound δ (-α) γ s ≤ max δ (γ / α) := by
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hα.ne')]
  set e := Real.exp (-α * s)
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h1 : δ ≤ max δ (γ / α) := le_max_left _ _
  have h2 : γ / α ≤ max δ (γ / α) := le_max_right _ _
  have key : γ / -α * (e - 1) = γ / α * (1 - e) := by rw [div_neg]; ring
  change δ * e + γ / -α * (e - 1) ≤ max δ (γ / α)
  rw [key]
  nlinarith [mul_le_mul_of_nonneg_right h1 he0, mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr he1)]

/-- If `v` is continuous on `[0, T]`, has right derivative `v'` on `[0, T)`, and
`v' ≤ -α v + γ` with `α > 0`, then `v t ≤ max (v 0) (γ / α)` on `[0, T]`. -/
theorem dissipation_bound {v v' : ℝ → ℝ} {α γ T : ℝ} (hα : 0 < α)
    (hv : ContinuousOn v (Icc 0 T))
    (hv' : ∀ t ∈ Ico 0 T, HasDerivWithinAt v (v' t) (Ici t) t)
    (hdiss : ∀ t ∈ Ico 0 T, v' t ≤ -α * v t + γ) :
    ∀ t ∈ Icc 0 T, v t ≤ max (v 0) (γ / α) := by
  intro t ht
  have hg := le_gronwallBound_of_liminf_deriv_right_le hv
    (fun s hs _r hr => (hv' s hs).liminf_right_slope_le hr) le_rfl hdiss t ht
  rw [sub_zero] at hg
  exact hg.trans (gronwallBound_neg_le_max hα ht.1)

end Dynacert
