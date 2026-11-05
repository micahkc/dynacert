import Rumoca.Fn.LieGroups.SO3.Quat.to_DCM
import Rumoca.Fn.LieGroups.SO3.Quat.kinematics
import Rumoca.Fn.LieGroups.SO3.Quat.product
import Rumoca.Fn.LieGroups.SO3.Quat.inverse
import Rumoca.Fn.LieGroups.SO3.Quat.normalize
import Rumoca.Fn.LieGroups.SO3.Quat.log_map
import Mathlib

/-!
# The LieGroups quaternion functions, as transcribed by rumoca

rumoca transcribes each Modelica function of `modelica_models/LieGroups` once
(`Rumoca/Fn/LieGroups/...`, identical text for every model that calls it). These lemmas, proved
once, give the closed forms of the polynomial ones, so any certificate for a model that calls
them can rewrite the calls into explicit polynomials:

* `to_DCM_apply`: the rotation matrix of a quaternion `{w, x, y, z}`;
* `kinematics_apply`: `q̇ = ½ q ⊗ (0, ω)`, and `kinematics_norm`: it preserves `|q|²`;
* `product_apply`, `inverse_apply`: Hamilton product and conjugate;
* `normalize_of_norm_one`: `normalize q = q` on the unit sphere.
-/

namespace Dynacert.Lie.QuatFn

open Matrix

theorem upd1_apply {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (a : ℝ) (i : Fin n) :
    Rumoca.upd1 v k a i = if (i : ℕ) + 1 = k then a else v i := rfl

theorem upd2_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (r c : ℕ) (a : ℝ) (i : Fin m)
    (j : Fin n) : Rumoca.upd2 M r c a i j = if (i : ℕ) + 1 = r ∧ (j : ℕ) + 1 = c then a else M i j :=
  rfl

/-- The rotation matrix (body → world) of `q = {w, x, y, z}`. -/
def dcm (q : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q 0 ^ 2 + q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2, 2 * (q 1 * q 2 - q 0 * q 3), 2 * (q 1 * q 3 + q 0 * q 2);
     2 * (q 1 * q 2 + q 0 * q 3), q 0 ^ 2 - q 1 ^ 2 + q 2 ^ 2 - q 3 ^ 2, 2 * (q 2 * q 3 - q 0 * q 1);
     2 * (q 1 * q 3 - q 0 * q 2), 2 * (q 2 * q 3 + q 0 * q 1), q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 + q 3 ^ 2]

theorem to_DCM_apply (q : Fin 4 → ℝ) : LieGroups.SO3.Quat.to_DCM q = dcm q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LieGroups.SO3.Quat.to_DCM, upd2_apply, dcm] <;> ring

/-- `½ q ⊗ (0, ω)`. -/
noncomputable def qdot (q : Fin 4 → ℝ) (ω : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![(1 / 2) * (-(q 1 * ω 0) - q 2 * ω 1 - q 3 * ω 2),
    (1 / 2) * (q 0 * ω 0 - q 3 * ω 1 + q 2 * ω 2),
    (1 / 2) * (q 3 * ω 0 + q 0 * ω 1 - q 1 * ω 2),
    (1 / 2) * (-(q 2 * ω 0) + q 1 * ω 1 + q 0 * ω 2)]

theorem kinematics_apply (q : Fin 4 → ℝ) (ω : Fin 3 → ℝ) :
    LieGroups.SO3.Quat.kinematics q ω = qdot q ω := by
  funext i
  fin_cases i <;> simp [LieGroups.SO3.Quat.kinematics, upd1_apply, qdot] <;> norm_num

/-- The quaternion kinematics are tangent to the spheres `|q|² = const`. -/
theorem kinematics_norm (q : Fin 4 → ℝ) (ω : Fin 3 → ℝ) :
    ∑ i, q i * LieGroups.SO3.Quat.kinematics q ω i = 0 := by
  rw [kinematics_apply]
  simp [qdot, Fin.sum_univ_succ]
  ring

/-- Hamilton product `q ⊗ p`. -/
def qmul (q p : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![q 0 * p 0 - q 1 * p 1 - q 2 * p 2 - q 3 * p 3,
    q 1 * p 0 + q 0 * p 1 - q 3 * p 2 + q 2 * p 3,
    q 2 * p 0 + q 3 * p 1 + q 0 * p 2 - q 1 * p 3,
    q 3 * p 0 - q 2 * p 1 + q 1 * p 2 + q 0 * p 3]

theorem product_apply (q p : Fin 4 → ℝ) : LieGroups.SO3.Quat.product q p = qmul q p := by
  funext i
  fin_cases i <;> simp [LieGroups.SO3.Quat.product, upd1_apply, qmul]

theorem inverse_apply (q : Fin 4 → ℝ) : LieGroups.SO3.Quat.inverse q = ![q 0, -q 1, -q 2, -q 3] := by
  funext i
  fin_cases i <;> simp [LieGroups.SO3.Quat.inverse, upd1_apply]

theorem normalize_of_norm_one {q : Fin 4 → ℝ} (h : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1) :
    LieGroups.SO3.Quat.normalize q = q := by
  simp only [LieGroups.SO3.Quat.normalize, h, Real.sqrt_one]
  rw [max_eq_left (by norm_num), inv_one, one_smul]

/-- The rotation matrix of a unit quaternion is orthogonal. -/
theorem dcm_orthogonal {q : Fin 4 → ℝ} (h : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1) :
    (dcm q)ᵀ * dcm q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dcm, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
    first | ring1 | linear_combination (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 + 1) * h

/-- `atan2 r w = arcsin r` for a point `(w, r)` on the unit circle with `w ≥ 0`. -/
theorem atan2_eq_arcsin {r w : ℝ} (hw : 0 ≤ w) (h : w ^ 2 + r ^ 2 = 1) :
    Rumoca.atan2 r w = Real.arcsin r := by
  unfold Rumoca.atan2
  rw [Complex.arg_of_re_nonneg (by simpa using hw)]
  congr 1
  have hn : ‖(⟨w, r⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, show w * w + r * r = 1 by nlinarith, Real.sqrt_one]
  simp [hn]

/-- **Sector form of the transcribed SO(3) log.** For a unit quaternion with `q₀ ≥ c > 0` (attitude
error angle below `2 arccos c`), `log_map q = κ · (q₁, q₂, q₃)` with `κ ∈ [2, 2/c]`: the log is the
vector part times a gain between `2` (at the identity) and `2/q₀`. Both branches of the Modelica
function (the small-angle Taylor branch and the `atan2` branch) satisfy it. -/
theorem log_map_sector {q : Fin 4 → ℝ} {c : ℝ} (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1)
    (hc : 0 < c) (hw : c ≤ q 0) :
    ∃ κ ∈ Set.Icc (2 : ℝ) (2 / c), LieGroups.SO3.Quat.log_map q = κ • ![q 1, q 2, q 3] := by
  have hw0 : 0 < q 0 := lt_of_lt_of_le hc hw
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg (q 1), sq_nonneg (q 2), sq_nonneg (q 3)]
  have h2c : (2 : ℝ) ≤ 2 / c := by rw [le_div_iff₀ hc]; linarith
  set r := Real.sqrt (q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 := Real.sq_sqrt (by positivity)
  have hq0le : q 0 ≤ 1 := by nlinarith [sq_nonneg (q 1), sq_nonneg (q 2), sq_nonneg (q 3)]
  have hclamp : min (max (q 0) (-1.0)) 1.0 = q 0 := by
    rw [max_eq_left (by norm_num; linarith), min_eq_left (by norm_num; linarith)]
  simp only [LieGroups.SO3.Quat.log_map, normalize_of_norm_one hq, not_lt.mpr hw0.le, if_false,
    hclamp, ← hr]
  by_cases hsmall : r < 0.0000000001
  · refine ⟨2, ⟨le_rfl, h2c⟩, ?_⟩
    simp only [hsmall, if_true]
    funext i; fin_cases i <;> simp [upd1_apply] <;> norm_num
  · simp only [hsmall, if_false]
    have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) (not_lt.mp hsmall)
    have hmax : max r 0.0000000001 = r := max_eq_left (not_lt.mp hsmall)
    have hcirc : q 0 ^ 2 + r ^ 2 = 1 := by rw [hr2]; linarith
    have hat : Rumoca.atan2 r (q 0) = Real.arcsin r := atan2_eq_arcsin hw0.le hcirc
    rw [hmax, hat]
    set θ := Real.arcsin r
    have hr1 : r < 1 := by nlinarith
    have hθ0 : 0 ≤ θ := Real.arcsin_nonneg.mpr hr0
    have hθπ : θ < Real.pi / 2 := by
      rw [Real.arcsin_lt_pi_div_two]; exact hr1
    have hsin : Real.sin θ = r := Real.sin_arcsin (by linarith) hr1.le
    have hcos : Real.cos θ = q 0 := by
      rw [Real.cos_arcsin, show 1 - r ^ 2 = q 0 ^ 2 by linarith, Real.sqrt_sq hw0.le]
    have hlo : r ≤ θ := hsin ▸ Real.sin_le hθ0
    have hhi : θ ≤ r / q 0 := by
      have := Real.le_tan hθ0 hθπ
      rwa [Real.tan_eq_sin_div_cos, hsin, hcos] at this
    refine ⟨2.0 * θ / r, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hrpos]; norm_num; linarith
    · rw [div_le_div_iff₀ hrpos hc]
      have : θ * q 0 ≤ r := by rwa [le_div_iff₀ hw0] at hhi
      norm_num; nlinarith
    · funext i; fin_cases i <;> simp [upd1_apply] <;> ring

end Dynacert.Lie.QuatFn
