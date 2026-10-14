import Mathlib

/-!
# Mean-value enclosures

A scalar nonlinearity `g` whose derivative is enclosed in `[lo, hi]` on an interval acts on
differences like an unknown gain in `[lo, hi]`:
`g a - g b = k (a - b)` with `k = (1 - μ) lo + μ hi` for some `μ ∈ [0, 1]`.
This is how a nonlinear error dynamics becomes a polytope of linear ones on a region; the
enclosure itself is a separate, checked inequality (e.g. bounds on `cos`).
-/

namespace Dynacert.Nonlinear

open Set

/-- Mean value theorem with an enclosed derivative: the difference quotient is a gain in
`[lo, hi]`. -/
theorem sub_eq_gain {g g' : ℝ → ℝ} {a b lo hi : ℝ}
    (hg : ∀ ξ ∈ uIcc a b, HasDerivAt g (g' ξ) ξ)
    (henc : ∀ ξ ∈ uIcc a b, lo ≤ g' ξ ∧ g' ξ ≤ hi) (hlo : lo ≤ hi) :
    ∃ k ∈ Icc lo hi, g a - g b = k * (a - b) := by
  rcases eq_or_ne a b with rfl | hab
  · exact ⟨lo, ⟨le_rfl, hlo⟩, by ring⟩
  wlog h : b < a generalizing a b
  · obtain ⟨l, hl, he⟩ := this (a := b) (b := a) (by rwa [uIcc_comm])
      (by rwa [uIcc_comm]) hab.symm (lt_of_le_of_ne (not_lt.mp h) hab)
    exact ⟨l, hl, by linarith⟩
  have hcont : ContinuousOn g (Icc b a) := fun ξ hξ =>
    (hg ξ (by rw [uIcc_of_ge h.le]; exact hξ)).continuousAt.continuousWithinAt
  have hdiff : ∀ ξ ∈ Ioo b a, HasDerivAt g (g' ξ) ξ := fun ξ hξ =>
    hg ξ (by rw [uIcc_of_ge h.le]; exact Ioo_subset_Icc_self hξ)
  obtain ⟨ξ, hξ, heq⟩ := exists_hasDerivAt_eq_slope g g' h hcont hdiff
  have hm : ξ ∈ uIcc a b := by rw [uIcc_of_ge h.le]; exact Ioo_subset_Icc_self hξ
  refine ⟨g' ξ, henc ξ hm, ?_⟩
  rw [heq]
  field_simp [sub_ne_zero.mpr hab]

/-- The gain as a convex combination of the two endpoints. -/
theorem gain_convex {k lo hi : ℝ} (h : k ∈ Icc lo hi) (hlo : lo < hi) :
    ∃ μ ∈ Icc (0 : ℝ) 1, k = (1 - μ) * lo + μ * hi := by
  refine ⟨(k - lo) / (hi - lo), ⟨div_nonneg (by linarith [h.1]) (by linarith),
    (div_le_one (by linarith)).mpr (by linarith [h.2])⟩, ?_⟩
  have hne : hi - lo ≠ 0 := by linarith
  field_simp
  ring

/-- `cos` is enclosed in `[cos R, 1]` on `[-R, R]` for `0 ≤ R ≤ π`. -/
theorem cos_enclosure {R θ : ℝ} (hR : R ≤ Real.pi) (hθ : |θ| ≤ R) :
    Real.cos R ≤ Real.cos θ ∧ Real.cos θ ≤ 1 := by
  refine ⟨?_, Real.cos_le_one θ⟩
  rw [← Real.cos_abs θ]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) hR hθ

end Dynacert.Nonlinear
