import Dynacert.Lie.PDControl

/-!
# The log-error field for any inputs: reference drift + input + residual

For a vehicle `X` driven by body acceleration `a` and rate `w` and a reference `Y` driven by
`ā, ω̄`, the exact log-error field splits, for **every** choice of inputs, as

    field = refDrift ā ω̄ ξ + (0, ã, ω̃) + inputResidual ξ ã ω̃ + gravity term,

with `ã = a - ā`, `ω̃ = w - ω̄` (`field_split`). The pieces are:

* `refDrift ā ω̄ ξ = (ξ_v, 0, 0) - ad(0, ā, ω̄) ξ`, linear in `ξ` with coefficients linear in
  `(ā, ω̄)`: an envelope on the reference is a polytope of linear maps;
* `(0, ã, ω̃)`, the input correction, where a controller enters;
* `inputResidual ξ ã ω̃ = -½ ad(0, ã, ω̃) ξ + controlResidual ξ ã ω̃`, bilinear in `(ξ, ũ)` up
  to Jacobian coefficients, with the sector bound `‖inputResidual‖ ≤ inputGain · ‖ξ‖` on
  `‖ξ‖ ≤ D ≤ 2` whenever `‖ã‖ ≤ A`, `‖ω̃‖ ≤ W` (`inputResidual_le`).

No control law appears. A controller written in group-error coordinates contributes
`ũ = K ξ + (coordinate residuals)`, bounded by the coordinate atoms `enorm_leftAt_sub_le`,
`enorm_attErr_sub_le`; one written in log coordinates contributes `ũ = K ξ` directly.
-/

noncomputable section

namespace Dynacert.Lie

open GNC Set Real
open scoped Matrix

/-- The drift of the log error along the reference: linear in `ξ`. -/
def refDrift (abar wbar : Vec3) (ξ : LogState) : LogState :=
  logDrift (Jacobian.controlInput abar wbar) ξ

/-- Everything in the field that is neither reference drift nor input correction. -/
def inputResidual (ξ : LogState) (da dw : Vec3) : LogState :=
  -((1 / 2 : ℝ) • ad (Jacobian.controlInput da dw) ξ) + Jacobian.controlResidual ξ da dw

theorem ad_controlInput_split (a w abar wbar : Vec3) (ξ : LogState) :
    ad (Jacobian.controlInput a w) ξ =
      ad (Jacobian.controlInput abar wbar) ξ +
        ad (Jacobian.controlInput (a - abar) (w - wbar)) ξ := by
  funext i
  fin_cases i <;>
    simp [ad, Jacobian.controlInput, map_sub, LinearMap.sub_apply] <;> abel

/-- **Exact split of the log-error field, any inputs.** -/
theorem field_split (X Y : ℝ → SE23) (a w abar wbar g gbar : Vec3) (t : ℝ) :
    logErrorField X Y a w abar wbar g gbar t =
      refDrift abar wbar (principalError X Y t) + Jacobian.controlInput (a - abar) (w - wbar) +
        inputResidual (principalError X Y t) (a - abar) (w - wbar) +
        Jacobian.blockRightInverse (principalError X Y t)
          (adjoint (X t)⁻¹ (velocityOnly (g - gbar))) := by
  rw [logErrorField, Jacobian.control_decomposition]
  simp only [refDrift, inputResidual, logDrift, mismatchCorrection,
    ad_controlInput_split a w abar wbar]
  module

/-! ## The sector bound of the input residual -/

theorem inputResidual_apply (ξ : LogState) (da dw : Vec3) :
    inputResidual ξ da dw 0 =
      -((1 / 2 : ℝ) • (dw ⨯₃ ξ 0)) + Jacobian.controlResidual ξ da dw 0 ∧
    inputResidual ξ da dw 1 =
      -((1 / 2 : ℝ) • (dw ⨯₃ ξ 1 + da ⨯₃ ξ 2)) + Jacobian.controlResidual ξ da dw 1 ∧
    inputResidual ξ da dw 2 = -((1 / 2 : ℝ) • (dw ⨯₃ ξ 2)) + Jacobian.controlResidual ξ da dw 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [inputResidual, ad, Jacobian.controlInput, ]

/-- The sector gain of the input residual on `‖ξ‖ ≤ D` for inputs bounded by `A`, `W`. -/
def inputGain (D A W : ℝ) : ℝ := W * (3 / 2 + 5 * D / 8) + A * (1 / 2 + D / 8)

theorem inputGain_nonneg {D A W : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) (hW : 0 ≤ W) :
    0 ≤ inputGain D A W := by
  unfold inputGain; positivity

/-- **Sector bound, any inputs.** On `‖ξ‖ ≤ D ≤ 2`, with `‖ã‖ ≤ A` and `‖ω̃‖ ≤ W`,
`‖inputResidual ξ ã ω̃‖ ≤ inputGain D A W · ‖ξ‖`. -/
theorem inputResidual_le {D A W : ℝ} (hD2 : D ≤ 2) (ξ : LogState) (da dw : Vec3)
    (hξ : ‖flat ξ‖ ≤ D) (hA : GNC.enorm da ≤ A) (hW : GNC.enorm dw ≤ W) :
    ‖flat (inputResidual ξ da dw)‖ ≤ inputGain D A W * ‖flat ξ‖ := by
  have hP := enorm_component_le_flat ξ 0
  have hV := enorm_component_le_flat ξ 1
  have hθ := enorm_component_le_flat ξ 2
  have hθ2 : GNC.enorm (ξ 2) ≤ 2 := (hθ.trans hξ).trans hD2
  have hN0 : 0 ≤ ‖flat ξ‖ := norm_nonneg _
  have hsum := flat_norm_le_sum (inputResidual ξ da dw)
  generalize ‖flat ξ‖ = N at hP hV hθ hξ hN0 ⊢
  obtain ⟨rc0, rc1, rc2⟩ := controlResidual_le ξ da dw hθ2
  obtain ⟨e0, e1, e2⟩ := inputResidual_apply ξ da dw
  have hhalf : ∀ v : Vec3, GNC.enorm (-((1 / 2 : ℝ) • v)) = GNC.enorm v / 2 := by
    intro v; rw [GNC.enorm_neg, GNC.enorm_smul]; norm_num; ring
  have c0 : GNC.enorm (inputResidual ξ da dw 0) ≤
      GNC.enorm dw * GNC.enorm (ξ 0) / 2 + GNC.enorm (ξ 2) / 4 * GNC.enorm (ξ 0) * GNC.enorm dw := by
    rw [e0]
    refine (GNC.enorm_add_le _ _).trans (add_le_add ?_ rc0)
    rw [hhalf]; have := GNC.cross_enorm_le dw (ξ 0); linarith
  have c1 : GNC.enorm (inputResidual ξ da dw 1) ≤
      (GNC.enorm dw * GNC.enorm (ξ 1) + GNC.enorm da * GNC.enorm (ξ 2)) / 2 +
        (GNC.enorm (ξ 2) ^ 2 / 8 * GNC.enorm da +
          GNC.enorm (ξ 2) / 4 * GNC.enorm (ξ 1) * GNC.enorm dw) := by
    rw [e1]
    refine (GNC.enorm_add_le _ _).trans (add_le_add ?_ rc1)
    rw [hhalf]
    have := GNC.enorm_add_le (dw ⨯₃ ξ 1) (da ⨯₃ ξ 2)
    have := GNC.cross_enorm_le dw (ξ 1)
    have := GNC.cross_enorm_le da (ξ 2)
    linarith
  have c2 : GNC.enorm (inputResidual ξ da dw 2) ≤
      GNC.enorm dw * GNC.enorm (ξ 2) / 2 + GNC.enorm (ξ 2) ^ 2 / 8 * GNC.enorm dw := by
    rw [e2]
    refine (GNC.enorm_add_le _ _).trans (add_le_add ?_ rc2)
    rw [hhalf]; have := GNC.cross_enorm_le dw (ξ 2); linarith
  have hP0 := GNC.enorm_nonneg (ξ 0)
  have hV0 := GNC.enorm_nonneg (ξ 1)
  have hθ0 := GNC.enorm_nonneg (ξ 2)
  have ha0 := GNC.enorm_nonneg da
  have hw0 := GNC.enorm_nonneg dw
  -- each term is at most its coefficient times `N`
  have t1 : GNC.enorm dw * GNC.enorm (ξ 0) / 2 ≤ W * N / 2 := by gcongr; linarith
  have hD4 : 0 ≤ D / 4 := by linarith
  have t2 : GNC.enorm (ξ 2) / 4 * GNC.enorm (ξ 0) * GNC.enorm dw ≤ D / 4 * N * W :=
    mul_le_mul (mul_le_mul (by linarith) hP hP0 hD4) hW hw0 (mul_nonneg hD4 hN0)
  have t3 : (GNC.enorm dw * GNC.enorm (ξ 1) + GNC.enorm da * GNC.enorm (ξ 2)) / 2 ≤
      (W * N + A * N) / 2 := by gcongr <;> linarith
  have t4 : GNC.enorm (ξ 2) ^ 2 / 8 * GNC.enorm da ≤ D * N / 8 * A := by
    have h2 : GNC.enorm (ξ 2) ^ 2 / 8 ≤ D * N / 8 := by nlinarith
    exact mul_le_mul h2 hA ha0 (by nlinarith)
  have t5 : GNC.enorm (ξ 2) / 4 * GNC.enorm (ξ 1) * GNC.enorm dw ≤ D / 4 * N * W :=
    mul_le_mul (mul_le_mul (by linarith) hV hV0 hD4) hW hw0 (mul_nonneg hD4 hN0)
  have t6 : GNC.enorm dw * GNC.enorm (ξ 2) / 2 ≤ W * N / 2 := by gcongr; linarith
  have t7 : GNC.enorm (ξ 2) ^ 2 / 8 * GNC.enorm dw ≤ D * N / 8 * W := by
    have h2 : GNC.enorm (ξ 2) ^ 2 / 8 ≤ D * N / 8 := by nlinarith
    exact mul_le_mul h2 hW hw0 (by nlinarith)
  calc ‖flat (inputResidual ξ da dw)‖ ≤ _ := hsum
    _ ≤ (W * N / 2 + D / 4 * N * W) + ((W * N + A * N) / 2 + (D * N / 8 * A + D / 4 * N * W)) +
          (W * N / 2 + D * N / 8 * W) :=
      add_le_add (add_le_add (c0.trans (add_le_add t1 t2))
        (c1.trans (add_le_add t3 (add_le_add t4 t5)))) (c2.trans (add_le_add t6 t7))
    _ = inputGain D A W * N := by unfold inputGain; ring

end Dynacert.Lie
