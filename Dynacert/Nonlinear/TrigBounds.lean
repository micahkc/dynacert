import Dynacert.Nonlinear.Enclosure

/-!
# Rational enclosures of `cos` on an interval, and the `sin` gain

For the polytopic embedding of a `sin` nonlinearity (paper, Lemma 1): on the band,
`sin θ - sin θ* = κ (θ - θ*)` with `κ = cos ξ` for some `ξ` between `θ` and `θ*`, and `κ` lies in
an interval with rational endpoints that the kernel checks:

* lower: `1 - M²/2 ≤ cos ξ` for `|ξ| ≤ M ≤ π` (Mathlib's `one_sub_sq_div_two_le_cos` and
  monotonicity of `cos` on `[0, π]`);
* upper: `cos ξ ≤ 1 - u²/2 + u⁴/24` at the endpoint closest to zero (`cos_le_taylor4`, proved
  here), or `1` if the interval contains `0`.
-/

namespace Dynacert.Nonlinear

open Set Real

/-- `x - x³/6 ≤ sin x` for `x ≥ 0`. -/
theorem sin_ge_cubic {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ sin x := by
  let G : ℝ → ℝ := fun y => sin y - y + y ^ 3 / 6
  have hG' : ∀ y, HasDerivAt G (cos y - 1 + y ^ 2 / 2) y := by
    intro y
    have := ((hasDerivAt_sin y).sub (hasDerivAt_id y)).add ((hasDerivAt_pow 3 y).div_const 6)
    convert this using 1
    simp; ring
  have hmono : MonotoneOn G (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hG' y).continuousAt.continuousWithinAt)
      (fun y _ => (hG' y).differentiableAt.differentiableWithinAt) ?_
    intro y _
    rw [(hG' y).deriv]
    linarith [one_sub_sq_div_two_le_cos (x := y)]
  have := hmono (left_mem_Ici) hx hx
  have h0 : G 0 = 0 := by simp [G]
  have := hmono (left_mem_Ici) (mem_Ici.mpr hx) hx
  simp only [G, sin_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, add_zero] at this
  linarith

/-- `cos x ≤ 1 - x²/2 + x⁴/24` for every real `x`. -/
theorem cos_le_taylor4 (x : ℝ) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  suffices h : ∀ y, 0 ≤ y → cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 / 24 by
    rcases le_total 0 x with hx | hx
    · exact h x hx
    · have := h (-x) (by linarith)
      rwa [cos_neg, neg_sq, show (-x) ^ 4 = x ^ 4 by ring] at this
  intro y hy
  let F : ℝ → ℝ := fun z => 1 - z ^ 2 / 2 + z ^ 4 / 24 - cos z
  have hF' : ∀ z, HasDerivAt F (-z + z ^ 3 / 6 + sin z) z := by
    intro z
    have := (((hasDerivAt_const z (1 : ℝ)).sub ((hasDerivAt_pow 2 z).div_const 2)).add
      ((hasDerivAt_pow 4 z).div_const 24)).sub (hasDerivAt_cos z)
    convert this using 1
    simp; ring
  have hmono : MonotoneOn F (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun z _ => (hF' z).continuousAt.continuousWithinAt)
      (fun z _ => (hF' z).differentiableAt.differentiableWithinAt) ?_
    intro z hz
    rw [(hF' z).deriv]
    have hz0 : 0 ≤ z := le_of_lt (by simpa using hz)
    linarith [sin_ge_cubic hz0]
  have := hmono left_mem_Ici (mem_Ici.mpr hy) hy
  simp only [F, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero,
    add_zero, cos_zero, sub_self] at this
  linarith

/-- **Enclosure of `cos` on `[u, v]`** with `max |u| |v| ≤ π`: below by `1 - M²/2`, above by
the quartic Taylor bound at the endpoint nearest `0` (or `1` if `0 ∈ [u, v]`). -/
theorem cos_mem_Icc {u v ξ : ℝ} (hξ : ξ ∈ Icc u v) (hM : max |u| |v| ≤ π) :
    1 - (max |u| |v|) ^ 2 / 2 ≤ cos ξ ∧
      cos ξ ≤ (if 0 < u then 1 - u ^ 2 / 2 + u ^ 4 / 24
        else if v < 0 then 1 - v ^ 2 / 2 + v ^ 4 / 24 else 1) := by
  have habs : |ξ| ≤ max |u| |v| := by
    rcases le_total 0 ξ with h | h
    · rw [abs_of_nonneg h]; exact (hξ.2.trans (le_abs_self v)).trans (le_max_right _ _)
    · rw [abs_of_nonpos h]; exact (neg_le_neg hξ.1 |>.trans (neg_le_abs u)).trans (le_max_left _ _)
  constructor
  · have hM0 : 0 ≤ max |u| |v| := (abs_nonneg u).trans (le_max_left _ _)
    calc 1 - (max |u| |v|) ^ 2 / 2 ≤ cos (max |u| |v|) := one_sub_sq_div_two_le_cos
      _ ≤ cos |ξ| := cos_le_cos_of_nonneg_of_le_pi (abs_nonneg ξ) hM habs
      _ = cos ξ := cos_abs ξ
  · split_ifs with hu hv
    · have hξ0 : 0 ≤ ξ := hu.le.trans hξ.1
      have hξπ : ξ ≤ π := (le_abs_self ξ).trans (habs.trans hM)
      exact (cos_le_cos_of_nonneg_of_le_pi hu.le hξπ hξ.1).trans (cos_le_taylor4 u)
    · have hξ0 : ξ ≤ 0 := hξ.2.trans hv.le
      have hπ : -ξ ≤ π := (neg_le_abs ξ).trans (habs.trans hM)
      have := cos_le_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ -v) hπ (by linarith [hξ.2])
      rw [cos_neg, cos_neg] at this
      exact this.trans (cos_le_taylor4 v)
    · exact cos_le_one ξ

/-- **`sin` gain.** If `θ*` and `θ` lie in `[u, v]` and `cos` is enclosed in `[lo, hi]` there,
then `sin θ - sin θ* = κ (θ - θ*)` with `κ ∈ [lo, hi]`. -/
theorem sin_sub_gain {θ θs u v lo hi : ℝ} (hθ : θ ∈ Icc u v) (hθs : θs ∈ Icc u v)
    (henc : ∀ ξ ∈ Icc u v, lo ≤ cos ξ ∧ cos ξ ≤ hi) (hlo : lo ≤ hi) :
    ∃ κ ∈ Icc lo hi, sin θ - sin θs = κ * (θ - θs) := by
  refine sub_eq_gain (g' := cos) (fun ξ _ => hasDerivAt_sin ξ) (fun ξ hξ => henc ξ ?_) hlo
  exact uIcc_subset_Icc hθ hθs hξ

end Dynacert.Nonlinear
