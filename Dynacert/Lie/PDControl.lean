import Dynacert.Lie.Supply
import GNC.Analysis.Coefficients
import GNC.Lie.ZeroAttitude
import GNC.Lie.Control

/-!
# A body-frame PD controller in log coordinates

The controller a Modelica model writes in body-frame errors,

    a = -kp · R̄ᵀ(p - p̄) - kd · R̄ᵀ(v - v̄) + d,     ω = -kR · ½ vee(R̄ᵀR - RᵀR̄),

is, in terms of the principal log error `ξ = log(Y⁻¹X)`, exactly linear plus a residual:

* `R̄ᵀ(p - p̄) = J_l(ξ_R) ξ_p` and `R̄ᵀ(v - v̄) = J_l(ξ_R) ξ_v` (the exponential's components);
* `½ vee(E - Eᵀ) = (sin θ / θ) ξ_R` for `E = Exp ξ_R`, `θ = ‖ξ_R‖` (`attErr_rotationExp`).

Combined with gnc's exact control decomposition (`control_decomposition`), the log-error field
of a vehicle tracking a coasting reference (`ā = 0`, `ω̄ = 0`) is

    field = A ξ + (0, d, 0) + r(ξ) + gravity term,     A ξ = (ξ_v, -kp ξ_p - kd ξ_v, -kR ξ_R),

with an explicit sector bound `‖r‖ ≤ pdGain · ‖ξ‖` on `‖ξ‖ ≤ D ≤ 2`, `‖d‖ ≤ δ`
(`pdResidual_le`). Everything is proved; the gains and `D`, `δ` are the only data.
-/

noncomputable section

namespace Dynacert.Lie

open GNC Set Real
open scoped Matrix

theorem enorm_zero' : GNC.enorm (0 : Vec3) = 0 := by simp [GNC.enorm]

/-! ## Scalar bounds -/

theorem sub_sin_le {t : ℝ} (ht : 0 ≤ t) : t - sin t ≤ t ^ 3 / 6 := by
  let f : ℝ → ℝ := fun s => s ^ 3 / 6 - s + sin s
  have hd : ∀ s, HasDerivAt f (s ^ 2 / 2 - 1 + cos s) s := by
    intro s
    have := (((hasDerivAt_pow 3 s).div_const 6).sub (hasDerivAt_id s)).add (hasDerivAt_sin s)
    convert this using 1; simp; ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun s _ => (hd s).continuousAt.continuousWithinAt
    · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
    · intro s _
      rw [(hd s).deriv]
      have := one_sub_sq_div_two_le_cos (x := s)
      linarith
  have h := hmono (self_mem_Ici) ht ht
  simp only [f] at h
  norm_num at h
  linarith

theorem one_sub_cos_le (t : ℝ) : 1 - cos t ≤ t ^ 2 / 2 := by
  have := one_sub_sq_div_two_le_cos (x := t); linarith

/-- `β(t) = 1 - (t/2) cot(t/2) ≤ t²/8` on `(0, 2]`. -/
theorem beta_le {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) : Coefficients.beta t ≤ t ^ 2 / 8 := by
  unfold Coefficients.beta
  set x := t / 2 with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by linarith
  have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hx0 (by linarith [pi_gt_three])
  have hsx : sin x ≤ x := sin_le hx0.le
  have hc : 1 - x ^ 2 / 2 ≤ cos x := one_sub_sq_div_two_le_cos
  have hc0 : 0 ≤ cos x := by nlinarith
  have key : cos x ≤ x * (cos x / sin x) := by
    rw [mul_div_assoc', le_div_iff₀ hs]
    exact mul_le_mul_of_nonneg_left hsx hc0 |>.trans_eq (mul_comm _ _) |>.trans' (by ring_nf; rfl)
  nlinarith

/-- `α(t) = t/(4 sin²(t/2)) - cos(t/2)/(2 sin(t/2)) ≤ t/4` on `(0, 2]`. -/
theorem alpha_le {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) : Coefficients.alpha t ≤ t / 4 := by
  unfold Coefficients.alpha
  set x := t / 2 with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by linarith
  have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hx0 (by linarith [pi_gt_three])
  have hsl : x - x ^ 3 / 6 ≤ sin x := by have := sub_sin_le hx0.le; linarith
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have hx3 : x ^ 3 ≤ x := by nlinarith [mul_le_mul_of_nonneg_left hx2 hx0.le]
  have hs56 : 5 * x / 6 ≤ sin x := by linarith
  -- t - sin t ≤ t³/6 at t = 2x, with sin 2x = 2 sin x cos x
  have h2 : 2 * x - 2 * sin x * cos x ≤ (2 * x) ^ 3 / 6 := by
    have := sub_sin_le (t := 2 * x) (by positivity)
    rwa [sin_two_mul] at this
  have heq : t / (4 * sin x ^ 2) - cos x / (2 * sin x) =
      (2 * x - 2 * sin x * cos x) / (4 * sin x ^ 2) := by
    rw [hx]; field_simp; ring
  rw [heq, div_le_iff₀ (by positivity)]
  have hss : 25 * x ^ 2 / 36 ≤ sin x ^ 2 := by nlinarith
  nlinarith

/-! ## The attitude error `½ vee(E - Eᵀ)` -/

/-- Modelica's attitude error `0.5*{R[3,2]-R[2,3], R[1,3]-R[3,1], R[2,1]-R[1,2]}`. -/
def attErr (R : Matrix (Fin 3) (Fin 3) ℝ) : Vec3 :=
  ![(1 / 2 : ℝ) * (R 2 1 - R 1 2), (1 / 2 : ℝ) * (R 0 2 - R 2 0), (1 / 2 : ℝ) * (R 1 0 - R 0 1)]

/-- On the exponential, the attitude error is `(sin θ / θ) ξ_R`. -/
theorem attErr_rotationExp (q : Vec3) :
    attErr (rotationExp q).val = (sin (GNC.enorm q) / GNC.enorm q) • q := by
  have h := rotationExp_antisymmetric q
  have e21 := congrFun (congrFun h 2) 1
  have e02 := congrFun (congrFun h 0) 2
  have e10 := congrFun (congrFun h 1) 0
  simp [Matrix.sub_apply, Matrix.transpose_apply, skew] at e21 e02 e10
  ext i
  fin_cases i <;> simp [attErr] <;> [rw [e21]; rw [e02]; rw [e10]] <;> ring

theorem enorm_attErr_le (q : Vec3) : GNC.enorm (attErr (rotationExp q).val) ≤ GNC.enorm q := by
  rw [attErr_rotationExp, GNC.enorm_smul]
  by_cases hq : GNC.enorm q = 0
  · simp [hq]
  · have hpos : 0 < GNC.enorm q := lt_of_le_of_ne (GNC.enorm_nonneg q) (Ne.symm hq)
    rw [abs_div, abs_of_pos hpos, div_mul_cancel₀ _ hq]
    exact abs_sin_le_abs.trans_eq (abs_of_pos hpos)

/-- The attitude error differs from `ξ_R` by at most `θ³/6`. -/
theorem enorm_attErr_sub_le (q : Vec3) :
    GNC.enorm (attErr (rotationExp q).val - q) ≤ GNC.enorm q ^ 3 / 6 := by
  rw [attErr_rotationExp]
  by_cases hq : GNC.enorm q = 0
  · rw [(GNC.enorm_eq_zero_iff q).mp hq]; simp [enorm_zero']
  · have hpos : 0 < GNC.enorm q := lt_of_le_of_ne (GNC.enorm_nonneg q) (Ne.symm hq)
    have : (sin (GNC.enorm q) / GNC.enorm q) • q - q = (sin (GNC.enorm q) / GNC.enorm q - 1) • q := by
      rw [sub_smul, one_smul]
    rw [this, GNC.enorm_smul]
    have hsl := sin_le hpos.le
    have hsub := sub_sin_le hpos.le
    have habs : |sin (GNC.enorm q) / GNC.enorm q - 1| = (GNC.enorm q - sin (GNC.enorm q)) / GNC.enorm q := by
      rw [show sin (GNC.enorm q) / GNC.enorm q - 1 = -((GNC.enorm q - sin (GNC.enorm q)) / GNC.enorm q) by
        field_simp; ring, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hpos.le)]
    rw [habs, div_mul_cancel₀ _ hq]
    linarith

/-! ## Jacobian distortion `J_l(q) v - v` -/

theorem enorm_leftAt_sub_le (q v : Vec3) :
    GNC.enorm (Jacobian.leftAt q v - v) ≤ (GNC.enorm q / 2 + GNC.enorm q ^ 2 / 6) * GNC.enorm v := by
  by_cases hq : GNC.enorm q = 0
  · rw [(GNC.enorm_eq_zero_iff q).mp hq]; simp [Jacobian.leftAt, enorm_zero']
  · have hθ : 0 < GNC.enorm q := lt_of_le_of_ne (GNC.enorm_nonneg q) (Ne.symm hq)
    set θ := GNC.enorm q
    have hsub : Jacobian.leftAt q v - v = ((1 - cos θ) / θ ^ 2) • (q ⨯₃ v) +
        ((θ - sin θ) / θ ^ 3) • (q ⨯₃ (q ⨯₃ v)) := by
      simp only [Jacobian.leftAt]; abel
    rw [hsub]
    have h1 : GNC.enorm (((1 - cos θ) / θ ^ 2) • (q ⨯₃ v)) ≤ θ / 2 * GNC.enorm v := by
      rw [GNC.enorm_smul, abs_of_nonneg (div_nonneg (by linarith [cos_le_one θ]) (by positivity))]
      calc (1 - cos θ) / θ ^ 2 * GNC.enorm (q ⨯₃ v) ≤ (1 - cos θ) / θ ^ 2 * (θ * GNC.enorm v) :=
            mul_le_mul_of_nonneg_left (GNC.cross_enorm_le q v)
              (div_nonneg (by linarith [cos_le_one θ]) (by positivity))
        _ = (1 - cos θ) / θ * GNC.enorm v := by field_simp
        _ ≤ θ / 2 * GNC.enorm v := by
            apply mul_le_mul_of_nonneg_right _ (GNC.enorm_nonneg v)
            rw [div_le_iff₀ hθ]; nlinarith [one_sub_cos_le θ]
    have h2 : GNC.enorm (((θ - sin θ) / θ ^ 3) • (q ⨯₃ (q ⨯₃ v))) ≤ θ ^ 2 / 6 * GNC.enorm v := by
      have hn : 0 ≤ θ - sin θ := by linarith [sin_le hθ.le]
      rw [GNC.enorm_smul, abs_of_nonneg (div_nonneg hn (by positivity))]
      have hc : GNC.enorm (q ⨯₃ (q ⨯₃ v)) ≤ θ * (θ * GNC.enorm v) :=
        (GNC.cross_enorm_le _ _).trans (mul_le_mul_of_nonneg_left (GNC.cross_enorm_le q v) hθ.le)
      calc (θ - sin θ) / θ ^ 3 * GNC.enorm (q ⨯₃ (q ⨯₃ v))
          ≤ (θ - sin θ) / θ ^ 3 * (θ * (θ * GNC.enorm v)) :=
            mul_le_mul_of_nonneg_left hc (div_nonneg hn (by positivity))
        _ = (θ - sin θ) / θ * GNC.enorm v := by field_simp
        _ ≤ θ ^ 2 / 6 * GNC.enorm v := by
            apply mul_le_mul_of_nonneg_right _ (GNC.enorm_nonneg v)
            rw [div_le_iff₀ hθ]; nlinarith [sub_sin_le hθ.le]
    calc _ ≤ _ := GNC.enorm_add_le _ _
      _ ≤ θ / 2 * GNC.enorm v + θ ^ 2 / 6 * GNC.enorm v := add_le_add h1 h2
      _ = _ := by ring

/-! ## The exact decomposition -/

/-- The PD acceleration command in terms of the group error `E = Y⁻¹X`. -/
def pdAccel (kp kd : ℝ) (E : SE23) (d : Vec3) : Vec3 := -kp • E.pos - kd • E.vel + d

/-- The PD rate command in terms of the group error. -/
def pdRate (kR : ℝ) (E : SE23) : Vec3 := -kR • attErr E.rot.val

/-- The closed-loop linear part `(ξ_v, -kp ξ_p - kd ξ_v, -kR ξ_R)`. -/
def pdLin (kp kd kR : ℝ) (ξ : LogState) : LogState := ![ξ 1, -kp • ξ 0 - kd • ξ 1, -kR • ξ 2]

/-- Everything else: Jacobian distortion of the errors, the input-dependent drift, and gnc's
control residual. -/
def pdResidual (kp kd kR : ℝ) (ξ : LogState) (a w : Vec3) : LogState :=
  Jacobian.controlInput
      (-kp • (Jacobian.leftAt (ξ 2) (ξ 0) - ξ 0) - kd • (Jacobian.leftAt (ξ 2) (ξ 1) - ξ 1))
      (-kR • (attErr (rotationExp (ξ 2)).val - ξ 2)) -
    (1 / 2 : ℝ) • ad (Jacobian.controlInput a w) ξ + Jacobian.controlResidual ξ a w

/-- **Exact decomposition.** For a coasting reference (`ā = 0`, `ω̄ = 0`) the control part of
the log-error field under the PD law is `pdLin ξ + (0, d, 0) + pdResidual`. -/
theorem pd_field (kp kd kR : ℝ) (ξ : LogState) (d : Vec3) :
    logDrift (Jacobian.controlInput (pdAccel kp kd (groupExp ξ) d) (pdRate kR (groupExp ξ))) ξ +
      Jacobian.blockInverse ξ (Jacobian.controlInput (pdAccel kp kd (groupExp ξ) d - 0)
        (pdRate kR (groupExp ξ) - 0)) =
    pdLin kp kd kR ξ + velocityOnly d +
      pdResidual kp kd kR ξ (pdAccel kp kd (groupExp ξ) d) (pdRate kR (groupExp ξ)) := by
  rw [sub_zero, sub_zero, Jacobian.control_decomposition]
  simp only [logDrift, mismatchCorrection, pdResidual]
  funext i
  fin_cases i <;>
    simp [pdLin, Jacobian.controlInput, velocityOnly, pdAccel, pdRate, groupExp,
      Matrix.vecHead, Matrix.vecTail, Pi.smul_apply] <;> module

/-! ## The sector bound -/

theorem flat_norm_le_sum (ξ : LogState) :
    ‖flat ξ‖ ≤ GNC.enorm (ξ 0) + GNC.enorm (ξ 1) + GNC.enorm (ξ 2) := by
  have h := flat_norm_sq ξ
  have h0 := GNC.enorm_nonneg (ξ 0)
  have h1 := GNC.enorm_nonneg (ξ 1)
  have h2 := GNC.enorm_nonneg (ξ 2)
  have hn := norm_nonneg (flat ξ)
  nlinarith [sq_nonneg (‖flat ξ‖ - (GNC.enorm (ξ 0) + GNC.enorm (ξ 1) + GNC.enorm (ξ 2))),
    mul_nonneg h0 h1, mul_nonneg h1 h2, mul_nonneg h0 h2]

theorem pdResidual_apply (kp kd kR : ℝ) (ξ : LogState) (a w : Vec3) :
    pdResidual kp kd kR ξ a w 0 = -((1 / 2 : ℝ) • (w ⨯₃ ξ 0)) + Jacobian.controlResidual ξ a w 0 ∧
    pdResidual kp kd kR ξ a w 1 =
      (-kp • (Jacobian.leftAt (ξ 2) (ξ 0) - ξ 0) - kd • (Jacobian.leftAt (ξ 2) (ξ 1) - ξ 1)) -
        (1 / 2 : ℝ) • (w ⨯₃ ξ 1 + a ⨯₃ ξ 2) + Jacobian.controlResidual ξ a w 1 ∧
    pdResidual kp kd kR ξ a w 2 = -kR • (attErr (rotationExp (ξ 2)).val - ξ 2) -
        (1 / 2 : ℝ) • (w ⨯₃ ξ 2) + Jacobian.controlResidual ξ a w 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [pdResidual, ad, Jacobian.controlInput, Matrix.vecHead, Matrix.vecTail] <;> module

/-- gnc's control residual, with explicit coefficient bounds, for `θ ≤ 2` (including `θ = 0`). -/
theorem controlResidual_le (ξ : LogState) (a w : Vec3) (hθ : GNC.enorm (ξ 2) ≤ 2) :
    GNC.enorm (Jacobian.controlResidual ξ a w 0) ≤
        GNC.enorm (ξ 2) / 4 * GNC.enorm (ξ 0) * GNC.enorm w ∧
    GNC.enorm (Jacobian.controlResidual ξ a w 1) ≤
        GNC.enorm (ξ 2) ^ 2 / 8 * GNC.enorm a + GNC.enorm (ξ 2) / 4 * GNC.enorm (ξ 1) * GNC.enorm w ∧
    GNC.enorm (Jacobian.controlResidual ξ a w 2) ≤ GNC.enorm (ξ 2) ^ 2 / 8 * GNC.enorm w := by
  set θ := GNC.enorm (ξ 2) with hθdef
  rcases (GNC.enorm_nonneg (ξ 2)).lt_or_eq with hpos | hzero
  · have hk := Jacobian.unitAxis_unit (ξ 2) hpos
    have hrec : ξ = ![ξ 0, ξ 1, θ • Jacobian.unitAxis (ξ 2)] := by
      funext i; fin_cases i <;> simp [θ, Jacobian.unitAxis_reconstruct (ξ 2) hpos]
    have hb := Jacobian.control_residual_bounds (ξ 0) (ξ 1) (Jacobian.unitAxis (ξ 2)) a w hk θ
      hpos (by linarith [pi_gt_three])
    rw [← hrec] at hb
    obtain ⟨h0, h1, h2⟩ := hb
    have hα := alpha_le hpos hθ
    have hβ := beta_le hpos hθ
    have hw := GNC.enorm_nonneg w
    have ha := GNC.enorm_nonneg a
    have hP := GNC.enorm_nonneg (ξ 0)
    have hV := GNC.enorm_nonneg (ξ 1)
    refine ⟨h0.trans ?_, h1.trans ?_, h2.trans ?_⟩
    · gcongr
    · gcongr
    · gcongr
  · have hz : ξ 2 = 0 := (GNC.enorm_eq_zero_iff _).mp hzero.symm
    rw [Jacobian.controlResidual_at_zero ξ a w hz]
    have h0 : (0 : ℝ) ≤ θ := GNC.enorm_nonneg _
    have hP := GNC.enorm_nonneg (ξ 0)
    have hV := GNC.enorm_nonneg (ξ 1)
    have hw := GNC.enorm_nonneg w
    have ha := GNC.enorm_nonneg a
    simp only [Pi.zero_apply, enorm_zero']
    refine ⟨?_, ?_, ?_⟩
    · exact mul_nonneg (mul_nonneg (by linarith) hP) hw
    · exact add_nonneg (mul_nonneg (by positivity) ha) (mul_nonneg (mul_nonneg (by linarith) hV) hw)
    · exact mul_nonneg (by positivity) hw

/-- The three components of the PD residual, bounded by the norms of the commands. -/
theorem pdResidual_components_le (kp kd kR : ℝ) (hkp : 0 ≤ kp) (hkd : 0 ≤ kd) (hkR : 0 ≤ kR)
    (ξ : LogState) (a w : Vec3) (hθ : GNC.enorm (ξ 2) ≤ 2) :
    GNC.enorm (pdResidual kp kd kR ξ a w 0) ≤
        GNC.enorm w * GNC.enorm (ξ 0) / 2 + GNC.enorm (ξ 2) / 4 * GNC.enorm (ξ 0) * GNC.enorm w ∧
    GNC.enorm (pdResidual kp kd kR ξ a w 1) ≤
        (kp * ((GNC.enorm (ξ 2) / 2 + GNC.enorm (ξ 2) ^ 2 / 6) * GNC.enorm (ξ 0)) +
          kd * ((GNC.enorm (ξ 2) / 2 + GNC.enorm (ξ 2) ^ 2 / 6) * GNC.enorm (ξ 1))) +
        (GNC.enorm w * GNC.enorm (ξ 1) + GNC.enorm a * GNC.enorm (ξ 2)) / 2 +
        (GNC.enorm (ξ 2) ^ 2 / 8 * GNC.enorm a +
          GNC.enorm (ξ 2) / 4 * GNC.enorm (ξ 1) * GNC.enorm w) ∧
    GNC.enorm (pdResidual kp kd kR ξ a w 2) ≤
        kR * (GNC.enorm (ξ 2) ^ 3 / 6) + GNC.enorm w * GNC.enorm (ξ 2) / 2 +
          GNC.enorm (ξ 2) ^ 2 / 8 * GNC.enorm w := by
  obtain ⟨rc0, rc1, rc2⟩ := controlResidual_le ξ a w hθ
  obtain ⟨e0, e1, e2⟩ := pdResidual_apply kp kd kR ξ a w
  have hhalf : ∀ v : Vec3, GNC.enorm ((1 / 2 : ℝ) • v) = GNC.enorm v / 2 := by
    intro v; rw [GNC.enorm_smul]; norm_num; ring
  have hsub : ∀ u v : Vec3, GNC.enorm (u - v) ≤ GNC.enorm u + GNC.enorm v := by
    intro u v; rw [sub_eq_add_neg]
    exact (GNC.enorm_add_le _ _).trans_eq (by rw [GNC.enorm_neg])
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]
    refine (GNC.enorm_add_le _ _).trans (add_le_add ?_ rc0)
    rw [GNC.enorm_neg, hhalf]
    have := GNC.cross_enorm_le w (ξ 0)
    linarith
  · rw [e1]
    refine (GNC.enorm_add_le _ _).trans (add_le_add ((hsub _ _).trans (add_le_add ?_ ?_)) rc1)
    · refine (hsub _ _).trans (add_le_add ?_ ?_)
      · rw [GNC.enorm_smul, abs_neg, abs_of_nonneg hkp]
        exact mul_le_mul_of_nonneg_left (enorm_leftAt_sub_le _ _) hkp
      · rw [GNC.enorm_smul, abs_of_nonneg hkd]
        exact mul_le_mul_of_nonneg_left (enorm_leftAt_sub_le _ _) hkd
    · rw [hhalf]
      have := GNC.enorm_add_le (w ⨯₃ ξ 1) (a ⨯₃ ξ 2)
      have := GNC.cross_enorm_le w (ξ 1)
      have := GNC.cross_enorm_le a (ξ 2)
      linarith
  · rw [e2]
    refine (GNC.enorm_add_le _ _).trans (add_le_add ((hsub _ _).trans (add_le_add ?_ ?_)) rc2)
    · rw [GNC.enorm_smul, abs_neg, abs_of_nonneg hkR]
      exact mul_le_mul_of_nonneg_left (enorm_attErr_sub_le _) hkR
    · rw [hhalf]
      have := GNC.cross_enorm_le w (ξ 2)
      linarith

/-- The sector gain of the PD residual on `‖ξ‖ ≤ D`, `‖d‖ ≤ δ`. -/
def pdGain (kp kd kR D δ : ℝ) : ℝ :=
  (kR * D / 2 + kR * D ^ 2 / 4) +
  ((kp + kd) * (D / 2 + D ^ 2 / 6) + (kR * D + (kp + kd) * D + δ) / 2 +
    D / 8 * ((kp + kd) * D + δ) + kR * D ^ 2 / 4) +
  (kR * D ^ 2 / 6 + kR * D / 2 + kR * D ^ 2 / 8)

/-- The scalar half of the sector bound. -/
theorem pdGain_bound {kp kd kR D δ N nP nV θ A W : ℝ} (hkp : 0 ≤ kp) (hkd : 0 ≤ kd)
    (hkR : 0 ≤ kR) (hδ : 0 ≤ δ) (hP0 : 0 ≤ nP) (hV0 : 0 ≤ nV) (hθ0 : 0 ≤ θ)
    (hPN : nP ≤ N) (hVN : nV ≤ N) (hθN : θ ≤ N) (hND : N ≤ D)
    (hA0 : 0 ≤ A) (hW0 : 0 ≤ W) (hA : A ≤ (kp + kd) * N + δ) (hW : W ≤ kR * θ) :
    (W * nP / 2 + θ / 4 * nP * W) +
      ((kp * ((θ / 2 + θ ^ 2 / 6) * nP) + kd * ((θ / 2 + θ ^ 2 / 6) * nV)) +
        (W * nV + A * θ) / 2 + (θ ^ 2 / 8 * A + θ / 4 * nV * W)) +
      (kR * (θ ^ 3 / 6) + W * θ / 2 + θ ^ 2 / 8 * W) ≤ pdGain kp kd kR D δ * N := by
  have hN0 : 0 ≤ N := hθ0.trans hθN
  have hD0 : 0 ≤ D := hN0.trans hND
  have hθD : θ ≤ D := hθN.trans hND
  have hWD : W ≤ kR * D := hW.trans (mul_le_mul_of_nonneg_left hθD hkR)
  have hAD : A ≤ (kp + kd) * D + δ := hA.trans (by gcongr)
  have hJ : θ / 2 + θ ^ 2 / 6 ≤ D / 2 + D ^ 2 / 6 := by gcongr
  have h1 : W * nP / 2 ≤ kR * D * N / 2 := by gcongr
  have h2 : θ / 4 * nP * W ≤ D / 4 * N * (kR * D) := by gcongr
  have h3 : kp * ((θ / 2 + θ ^ 2 / 6) * nP) ≤ kp * ((D / 2 + D ^ 2 / 6) * N) := by gcongr
  have h4 : kd * ((θ / 2 + θ ^ 2 / 6) * nV) ≤ kd * ((D / 2 + D ^ 2 / 6) * N) := by gcongr
  have h5 : W * nV ≤ kR * D * N := by gcongr
  have h6 : A * θ ≤ ((kp + kd) * D + δ) * N := by gcongr
  have h7 : θ ^ 2 / 8 * A ≤ (D * N) / 8 * ((kp + kd) * D + δ) := by
    have : θ ^ 2 ≤ D * N := by nlinarith
    gcongr
  have h8 : θ / 4 * nV * W ≤ D / 4 * N * (kR * D) := by gcongr
  have hθ3 : θ ^ 3 ≤ D ^ 2 * N := by
    calc θ ^ 3 = θ ^ 2 * θ := by ring
      _ ≤ D ^ 2 * N := by gcongr
  have h9 : kR * (θ ^ 3 / 6) ≤ kR * (D ^ 2 * N / 6) := by gcongr
  have h10 : W * θ / 2 ≤ kR * D * N / 2 := by gcongr
  have h11 : θ ^ 2 / 8 * W ≤ kR * θ ^ 3 / 8 := by
    calc θ ^ 2 / 8 * W ≤ θ ^ 2 / 8 * (kR * θ) := by gcongr
      _ = kR * θ ^ 3 / 8 := by ring
  have h12 : kR * θ ^ 3 / 8 ≤ kR * (D ^ 2 * N) / 8 := by gcongr
  unfold pdGain
  nlinarith

/-- **Sector bound.** On `‖ξ‖ ≤ D ≤ 2` with `‖d‖ ≤ δ`, the PD residual is at most
`pdGain · ‖ξ‖`. -/
theorem pdResidual_le {kp kd kR D δ : ℝ} (hkp : 0 ≤ kp) (hkd : 0 ≤ kd) (hkR : 0 ≤ kR)
    (hD2 : D ≤ 2) (ξ : LogState) (d : Vec3) (hξ : ‖flat ξ‖ ≤ D) (hd : GNC.enorm d ≤ δ) :
    ‖flat (pdResidual kp kd kR ξ (pdAccel kp kd (groupExp ξ) d) (pdRate kR (groupExp ξ)))‖ ≤
      pdGain kp kd kR D δ * ‖flat ξ‖ := by
  have hθN := enorm_component_le_flat ξ 2
  have hθ2 : GNC.enorm (ξ 2) ≤ 2 := (hθN.trans hξ).trans hD2
  have hθπ : GNC.enorm (ξ 2) < 2 * π := by linarith [pi_gt_three]
  have hw : GNC.enorm (pdRate kR (groupExp ξ)) ≤ kR * GNC.enorm (ξ 2) := by
    rw [pdRate, GNC.enorm_smul, abs_neg, abs_of_nonneg hkR]
    exact mul_le_mul_of_nonneg_left (enorm_attErr_le (ξ 2)) hkR
  have ha : GNC.enorm (pdAccel kp kd (groupExp ξ) d) ≤ (kp + kd) * ‖flat ξ‖ + δ := by
    rw [pdAccel]
    have e1 : GNC.enorm (-kp • (groupExp ξ).pos) ≤ kp * GNC.enorm (ξ 0) := by
      rw [GNC.enorm_smul, abs_neg, abs_of_nonneg hkp]
      exact mul_le_mul_of_nonneg_left (leftAt_nonexpansive (ξ 2) (ξ 0) hθπ) hkp
    have e2 : GNC.enorm (kd • (groupExp ξ).vel) ≤ kd * GNC.enorm (ξ 1) := by
      rw [GNC.enorm_smul, abs_of_nonneg hkd]
      exact mul_le_mul_of_nonneg_left (leftAt_nonexpansive (ξ 2) (ξ 1) hθπ) hkd
    have e3 : GNC.enorm (-kp • (groupExp ξ).pos - kd • (groupExp ξ).vel) ≤
        GNC.enorm (-kp • (groupExp ξ).pos) + GNC.enorm (kd • (groupExp ξ).vel) := by
      rw [sub_eq_add_neg]; exact (GNC.enorm_add_le _ _).trans_eq (by rw [GNC.enorm_neg])
    have e4 := GNC.enorm_add_le (-kp • (groupExp ξ).pos - kd • (groupExp ξ).vel) d
    have hP := enorm_component_le_flat ξ 0
    have hV := enorm_component_le_flat ξ 1
    nlinarith
  obtain ⟨c0, c1, c2⟩ := pdResidual_components_le kp kd kR hkp hkd hkR ξ
    (pdAccel kp kd (groupExp ξ) d) (pdRate kR (groupExp ξ)) hθ2
  calc _ ≤ _ := flat_norm_le_sum _
    _ ≤ _ := add_le_add (add_le_add c0 c1) c2
    _ ≤ _ := pdGain_bound hkp hkd hkR ((GNC.enorm_nonneg d).trans hd) (GNC.enorm_nonneg _)
          (GNC.enorm_nonneg _) (GNC.enorm_nonneg _) (enorm_component_le_flat ξ 0)
          (enorm_component_le_flat ξ 1) hθN hξ (GNC.enorm_nonneg _) (GNC.enorm_nonneg _) ha hw

end Dynacert.Lie
