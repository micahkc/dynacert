import Dynacert.Nonlinear.TrigBounds
import Rumoca.Prelude

/-!
# Rigorous sector and peak bounds for the nonlinear atoms of a vehicle model

The residual channels of a sector certificate are built from a few nonlinear *atoms*: `sin θ`,
`cos θ`, the thrust magnitude `√(s² + h²)`, and the thrust-direction command `atan2(y, h)`.
On a box region `|θ| ≤ a`, `|s| ≤ b`, `h ∈ [h₀, h₁]` each atom splits into its first-order
part plus a remainder that is either a *sector* term `δ·q` with `δ` in a known interval, or a
*bounded* term. The intervals are explicit rational functions of the region, proved here once
from Taylor inequalities (no grid, no floating point): this is the "rigorous bounds" step of the
paper's Directions, checked in the proof assistant.

| Atom | First order | Remainder | Lemma |
|---|---|---|---|
| `sin θ` | `θ` | `sin θ - θ = δ θ`, `δ ∈ [-a²/6, 0]` | `sin_sub_self_gain` |
| `sin θ` (as a gain) | — | `\|sin θ\| ≤ a` | `abs_sin_le_of` |
| `cos θ` | `1` | `\|cos θ - 1\| ≤ a²/2` | `abs_cos_sub_one_le` |
| `√(s² + h²)` | `h` | `0 ≤ √(s²+h²) - h ≤ b²/(2h₀)` | `sqrt_sub_mem` |
| `atan2(y, h)` | `k y` (`k = 1/h(0)`) | `atan2(y,h) - k y = δ y`, `δ ∈ [(1-b²/(3h₀²))/h₁ - k, 1/h₀ - k]` | `atan2_sub_gain` |
| `q₀ = √(1 - x)`, `x = \|q_v\|²` | `1` | `\|q₀ - 1\| ≤ X/(2 - X)` for `x ≤ X ≤ 1` | `sqrt_one_sub_sub_one_le` |

Polynomial residuals (the 3D vehicle) are products of region coordinates and `q₀ - 1`, bounded
factor by factor with `abs_mul_le_of` and summed with `abs_add_le_of`.
-/

namespace Dynacert.Sector

open Set Real

/-! ### Products of bounded factors -/

theorem abs_mul_le_of {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg y) ((abs_nonneg x).trans hx)

/-- A sector channel `p = δ q` that is also scaled: `c p = (c δ) q`. -/
theorem gain_scale {p q δ lo hi c : ℝ} (hp : p = δ * q) (hδ : δ ∈ Icc lo hi) (hc : 0 ≤ c) :
    c * p = (c * δ) * q ∧ c * δ ∈ Icc (c * lo) (c * hi) :=
  ⟨by rw [hp]; ring, mul_le_mul_of_nonneg_left hδ.1 hc, mul_le_mul_of_nonneg_left hδ.2 hc⟩

/-- A bounded factor turns a linear form into a sector channel: `p = y q` with `|y| ≤ Y`. -/
theorem gain_of_abs {y Y lo hi : ℝ} (hy : |y| ≤ Y) (hlo : lo ≤ -Y) (hhi : Y ≤ hi) :
    y ∈ Icc lo hi :=
  ⟨hlo.trans (neg_le_of_abs_le hy), (le_abs_self y).trans (hy.trans hhi)⟩

/-! ### sin and cos -/

theorem abs_sin_le_of {θ a : ℝ} (h : |θ| ≤ a) : |sin θ| ≤ a := abs_sin_le_abs.trans h

theorem sq_le_of_abs_le {θ a : ℝ} (h : |θ| ≤ a) : θ ^ 2 ≤ a ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg θ) h 2

theorem sin_sub_self_mem_of_nonneg {θ : ℝ} (h : 0 ≤ θ) :
    -(θ ^ 3 / 6) ≤ sin θ - θ ∧ sin θ - θ ≤ 0 :=
  ⟨by linarith [Nonlinear.sin_ge_cubic h], by linarith [sin_le h]⟩

/-- **`sin θ - θ` is a sector term in `θ`.** -/
theorem sin_sub_self_gain {θ a lo hi : ℝ} (h : |θ| ≤ a) (hlo : lo ≤ -(a ^ 2 / 6))
    (hhi : 0 ≤ hi) : ∃ δ ∈ Icc lo hi, sin θ - θ = δ * θ := by
  have ha2 := sq_le_of_abs_le h
  rcases lt_trichotomy θ 0 with hneg | hz | hpos
  · obtain ⟨h1, h2⟩ := sin_sub_self_mem_of_nonneg (neg_nonneg.mpr hneg.le)
    rw [sin_neg] at h1 h2
    refine ⟨(sin θ - θ) / θ, ⟨?_, ?_⟩, (div_mul_cancel₀ _ hneg.ne).symm⟩
    · rw [le_div_iff_of_neg hneg]
      have hc : (-θ) ^ 3 = -(θ ^ 2 * θ) := by ring
      rw [hc] at h1
      have : 0 ≤ (lo + θ ^ 2 / 6) * θ :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hneg.le
      nlinarith
    · rw [div_le_iff_of_neg hneg]
      have : hi * θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hhi hneg.le
      linarith
  · exact ⟨0, ⟨by nlinarith [sq_nonneg a], hhi⟩, by simp [hz]⟩
  · obtain ⟨h1, h2⟩ := sin_sub_self_mem_of_nonneg hpos.le
    refine ⟨(sin θ - θ) / θ, ⟨?_, ?_⟩, (div_mul_cancel₀ _ hpos.ne').symm⟩
    · rw [le_div_iff₀ hpos]
      have : (lo + θ ^ 2 / 6) * θ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
      nlinarith
    · exact (div_nonpos_of_nonpos_of_nonneg h2 hpos.le).trans hhi

/-- `|cos θ - 1| ≤ a²/2` on `|θ| ≤ a`. -/
theorem abs_cos_sub_one_le {θ a : ℝ} (h : |θ| ≤ a) : |cos θ - 1| ≤ a ^ 2 / 2 := by
  have h1 := one_sub_sq_div_two_le_cos (x := θ)
  have h2 := cos_le_one θ
  have := sq_le_of_abs_le h
  rw [abs_le]; constructor <;> nlinarith

/-! ### Thrust magnitude `√(s² + h²)` -/

/-- **`√(s² + h²) - h` is small:** `0 ≤ √(s² + h²) - h ≤ b²/(2h₀)` for `|s| ≤ b`, `h ≥ h₀ > 0`. -/
theorem sqrt_sub_mem {s h b h0 : ℝ} (hh0 : 0 < h0) (hh : h0 ≤ h) (hs : |s| ≤ b) :
    0 ≤ √(s ^ 2 + h ^ 2) - h ∧ √(s ^ 2 + h ^ 2) - h ≤ b ^ 2 / (2 * h0) := by
  have hpos : 0 < h := hh0.trans_le hh
  have hs2 := sq_le_of_abs_le hs
  constructor
  · have : √(h ^ 2) ≤ √(s ^ 2 + h ^ 2) := sqrt_le_sqrt (by nlinarith [sq_nonneg s])
    rw [sqrt_sq hpos.le] at this; linarith
  · have hup : √(s ^ 2 + h ^ 2) ≤ h + s ^ 2 / (2 * h) := by
      have hnn : 0 ≤ h + s ^ 2 / (2 * h) := by positivity
      rw [show h + s ^ 2 / (2 * h) = √((h + s ^ 2 / (2 * h)) ^ 2) from (sqrt_sq hnn).symm]
      apply sqrt_le_sqrt
      have : (h + s ^ 2 / (2 * h)) ^ 2 = s ^ 2 + h ^ 2 + (s ^ 2 / (2 * h)) ^ 2 := by
        field_simp; ring
      rw [this]; nlinarith [sq_nonneg (s ^ 2 / (2 * h))]
    have : s ^ 2 / (2 * h) ≤ b ^ 2 / (2 * h0) := by
      apply div_le_div₀ (sq_nonneg b) hs2 (by positivity) (by linarith)
    linarith

/-- The thrust magnitude itself: `|√(s² + h²)| ≤ h₁ + b²/(2h₀)` for `h ∈ [h₀, h₁]`. -/
theorem abs_sqrt_le {s h b h0 h1 : ℝ} (hh0 : 0 < h0) (hh : h ∈ Icc h0 h1) (hs : |s| ≤ b) :
    |√(s ^ 2 + h ^ 2)| ≤ h1 + b ^ 2 / (2 * h0) := by
  rw [abs_of_nonneg (sqrt_nonneg _)]
  linarith [(sqrt_sub_mem hh0 hh.1 hs).2, hh.2]

/-- The remainder as an absolute bound. -/
theorem abs_sqrt_sub_le {s h b h0 : ℝ} (hh0 : 0 < h0) (hh : h0 ≤ h) (hs : |s| ≤ b) :
    |√(s ^ 2 + h ^ 2) - h| ≤ b ^ 2 / (2 * h0) := by
  obtain ⟨h1, h2⟩ := sqrt_sub_mem hh0 hh hs
  rw [abs_of_nonneg h1]; exact h2

/-! ### Unit-quaternion chart `q₀ = √(1 - |q_v|²)` -/

/-- **The scalar part of a unit quaternion is close to 1:** for `0 ≤ x ≤ X ≤ 1`,
`|√(1 - x) - 1| ≤ X / (2 - X)` (from `1 - √(1-x) = x / (1 + √(1-x))` and `√(1-x) ≥ 1 - x`). -/
theorem sqrt_one_sub_sub_one_le {x X : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ X) (hX : X ≤ 1) :
    |√(1 - x) - 1| ≤ X / (2 - X) := by
  have h1x : 0 ≤ 1 - x := by linarith
  have hr2 : √(1 - x) ^ 2 = 1 - x := sq_sqrt h1x
  have hr1 : √(1 - x) ≤ 1 := sqrt_le_one.mpr (by linarith)
  have hr0 : 1 - x ≤ √(1 - x) := (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith))
  rw [abs_of_nonpos (by linarith), le_div_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left (show 2 - X ≤ 1 + √(1 - x) by linarith)
    (show 0 ≤ 1 - √(1 - x) by linarith)
  nlinarith

theorem abs_add_le_of {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x + y| ≤ X + Y :=
  (abs_add_le x y).trans (add_le_add hx hy)

/-! ### Thrust-direction command `atan2(y, h)` -/

/-- Modelica's `atan2(y, x)` is `arctan (y / x)` in the right half plane. -/
theorem atan2_of_pos {y x : ℝ} (hx : 0 < x) : Rumoca.atan2 y x = arctan (y / x) := by
  unfold Rumoca.atan2
  set z : ℂ := ⟨x, y⟩
  have hlt : |Complex.arg z| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  rw [abs_lt] at hlt
  have := arctan_tan hlt.1 hlt.2
  rw [Complex.tan_arg] at this
  exact this.symm

theorem arctan_le_self {r : ℝ} (hr : 0 ≤ r) : arctan r ≤ r := by
  let G : ℝ → ℝ := fun x => x - arctan x
  have hG' : ∀ x, HasDerivAt G (1 - 1 / (1 + x ^ 2)) x :=
    fun x => (hasDerivAt_id x).sub (hasDerivAt_arctan x)
  have hmono : MonotoneOn G (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hG' x).continuousAt.continuousWithinAt)
      (fun x _ => (hG' x).differentiableAt.differentiableWithinAt) ?_
    intro x _
    rw [(hG' x).deriv]
    have : 1 / (1 + x ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg x]
    linarith
  have := hmono self_mem_Ici (mem_Ici.mpr hr) hr
  simp only [G, arctan_zero, sub_zero] at this
  linarith

theorem sub_cube_le_arctan {r : ℝ} (hr : 0 ≤ r) : r - r ^ 3 / 3 ≤ arctan r := by
  let G : ℝ → ℝ := fun x => arctan x - x + x ^ 3 / 3
  have hG' : ∀ x, HasDerivAt G (1 / (1 + x ^ 2) - 1 + x ^ 2) x := by
    intro x
    have := ((hasDerivAt_arctan x).sub (hasDerivAt_id x)).add ((hasDerivAt_pow 3 x).div_const 3)
    convert this using 1
    simp
  have hmono : MonotoneOn G (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hG' x).continuousAt.continuousWithinAt)
      (fun x _ => (hG' x).differentiableAt.differentiableWithinAt) ?_
    intro x _
    rw [(hG' x).deriv]
    have hp : 0 < 1 + x ^ 2 := by positivity
    have : 1 / (1 + x ^ 2) - 1 + x ^ 2 = x ^ 4 / (1 + x ^ 2) := by field_simp; ring
    rw [this]; positivity
  have := hmono self_mem_Ici (mem_Ici.mpr hr) hr
  simp only [G, arctan_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, add_zero] at this
  linarith

/-- `arctan r / r ∈ [1 - r²/3, 1]` for `r ≠ 0`. -/
theorem arctan_div_mem {r : ℝ} (hr : r ≠ 0) :
    1 - r ^ 2 / 3 ≤ arctan r / r ∧ arctan r / r ≤ 1 := by
  rcases hr.lt_or_gt with hneg | hpos
  · have h1 := arctan_le_self (neg_nonneg.mpr hneg.le)
    have h2 := sub_cube_le_arctan (neg_nonneg.mpr hneg.le)
    rw [arctan_neg] at h1 h2
    constructor
    · rw [le_div_iff_of_neg hneg]; nlinarith
    · rw [div_le_iff_of_neg hneg]; linarith
  · have h1 := arctan_le_self hpos.le
    have h2 := sub_cube_le_arctan hpos.le
    constructor
    · rw [le_div_iff₀ hpos]; nlinarith
    · rw [div_le_iff₀ hpos]; linarith

/-- **`atan2(y, h) - k y` is a sector term in `y`** on `|y| ≤ b ≤ h₀`, `h ∈ [h₀, h₁]`. -/
theorem atan2_sub_gain {y h b h0 h1 k lo hi : ℝ} (hh0 : 0 < h0) (hh : h ∈ Icc h0 h1)
    (hy : |y| ≤ b) (hb : b ≤ h0) (hlo : lo ≤ (1 - b ^ 2 / (3 * h0 ^ 2)) / h1 - k)
    (hhi : 1 / h0 - k ≤ hi) : ∃ δ ∈ Icc lo hi, Rumoca.atan2 y h - k * y = δ * y := by
  have hpos : 0 < h := hh0.trans_le hh.1
  have h1pos : 0 < h1 := hpos.trans_le hh.2
  have hb0 : 0 ≤ b := (abs_nonneg y).trans hy
  -- the lower end of the multiplier `arctan r / r`
  have hm0 : 0 ≤ 1 - b ^ 2 / (3 * h0 ^ 2) := by
    have : b ^ 2 ≤ h0 ^ 2 := pow_le_pow_left₀ hb0 hb 2
    rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
  have hlohi : (1 - b ^ 2 / (3 * h0 ^ 2)) / h1 ≤ 1 / h0 := by
    have : 1 - b ^ 2 / (3 * h0 ^ 2) ≤ 1 := by
      have : 0 ≤ b ^ 2 / (3 * h0 ^ 2) := by positivity
      linarith
    calc (1 - b ^ 2 / (3 * h0 ^ 2)) / h1 ≤ 1 / h1 := div_le_div_of_nonneg_right this h1pos.le
      _ ≤ 1 / h0 := one_div_le_one_div_of_le hh0 (hh.1.trans hh.2)
  rw [atan2_of_pos hpos]
  rcases eq_or_ne y 0 with hz | hz
  · refine ⟨lo, ⟨le_rfl, by linarith⟩, by simp [hz]⟩
  set r := y / h with hr
  have hr0 : r ≠ 0 := div_ne_zero hz hpos.ne'
  obtain ⟨m1, m2⟩ := arctan_div_mem hr0
  set m := arctan r / r
  have harc : arctan r = m * y / h := by
    simp only [m, hr]; field_simp
  refine ⟨m / h - k, ⟨?_, ?_⟩, by rw [harc]; field_simp⟩
  · have hr2 : r ^ 2 ≤ b ^ 2 / h0 ^ 2 := by
      rw [hr, div_pow]
      exact div_le_div₀ (sq_nonneg b) (sq_le_of_abs_le hy) (by positivity)
        (pow_le_pow_left₀ hh0.le hh.1 2)
    have hm : 1 - b ^ 2 / (3 * h0 ^ 2) ≤ m := by
      have : b ^ 2 / (3 * h0 ^ 2) = (b ^ 2 / h0 ^ 2) / 3 := by field_simp
      linarith
    have hmn : 0 ≤ m := hm0.trans hm
    have : (1 - b ^ 2 / (3 * h0 ^ 2)) / h1 ≤ m / h :=
      div_le_div₀ hmn hm hpos hh.2
    linarith
  · have : m / h ≤ 1 / h0 := div_le_div₀ zero_le_one m2 hh0 hh.1
    linarith

end Dynacert.Sector
