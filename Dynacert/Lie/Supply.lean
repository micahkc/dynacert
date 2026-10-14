import Dynacert.Lie.PhysicalOutput
import GNC.Control.PolytopicResidualTube
import GNC.Dynamics.GravityMismatch
import GNC.Dynamics.MixedErrorDynamics
import GNC.Dynamics.ForcedLogDynamics

/-!
# Supply from vertex LMIs and a list of residuals

`log_error_tube` takes the supply inequality for the log-error field as a hypothesis. This file
discharges it from checkable data:

* the field, in flat coordinates, splits as `Σ wᵢ Aᵢ ξ + B d + Σₖ rₖ` (a polytope of linear
  maps, a bounded exogenous input, and a finite list of residuals);
* each residual has a sector bound `‖rₖ‖ ≤ ℓₖ ‖ξ‖` on the certified sublevel;
* the vertex LMIs `2⟨y, P(Aᵢy + Bu)⟩ + α yᵀPy ≤ μ‖u‖²` hold.

The residual list is what distinguishes models with the same group structure. For a quadrotor
in constant gravity the gravity residual is identically zero (`gravity_residual_const`: the
field is group-affine); for a spacecraft in inverse-square gravity it is a sector on the
certified region (`gravity_residual_inverse_square`, from gnc's sharp mismatch bound). Both use
the same `log_tube_of_residuals`.
-/

noncomputable section

namespace Dynacert.Lie

open GNC Set Real GNC.PolytopicTube
open scoped BigOperators

/-! ## Generic: polytope + residual list ⇒ supply -/

section Generic

variable {ι κ E W : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The storage loss of a sum of sector-bounded residuals, with a rational bound `pn` on the
operator norm of `P`. -/
theorem residual_sum_supply (P : E →L[ℝ] E) {m pn : ℝ} (ℓ : κ → ℝ) (hm : 0 < m)
    (hℓ : ∀ k, 0 ≤ ℓ k) (hPn : ‖P‖ ≤ pn) (x : E) (r : κ → E)
    (hcoerce : m * ‖x‖ ^ 2 ≤ storage P x) (hr : ∀ k, ‖r k‖ ≤ ℓ k * ‖x‖) :
    2 * inner ℝ x (P (∑ k, r k)) ≤ (2 * pn * (∑ k, ℓ k) / m) * storage P x := by
  have hL : 0 ≤ ∑ k, ℓ k := Finset.sum_nonneg fun k _ => hℓ k
  have hsum : ‖∑ k, r k‖ ≤ (∑ k, ℓ k) * ‖x‖ :=
    calc ‖∑ k, r k‖ ≤ ∑ k, ‖r k‖ := norm_sum_le _ _
      _ ≤ ∑ k, ℓ k * ‖x‖ := Finset.sum_le_sum fun k _ => hr k
      _ = (∑ k, ℓ k) * ‖x‖ := by rw [Finset.sum_mul]
  have h := GNC.PolytopicResidualTube.sector_supply P x (∑ k, r k) hm hL hcoerce hsum
  have hV : 0 ≤ storage P x := le_trans (by positivity) hcoerce
  have hmono : (2 * ‖P‖ * (∑ k, ℓ k) / m) * storage P x ≤
      (2 * pn * (∑ k, ℓ k) / m) * storage P x := by
    apply mul_le_mul_of_nonneg_right _ hV
    apply div_le_div_of_nonneg_right _ hm.le
    have := mul_le_mul_of_nonneg_right hPn hL
    nlinarith
  linarith

/-- **Residual supply.** Vertex LMIs and sector-bounded residuals give the supply inequality
with decay rate `α - 2 pn Σℓ / m`. -/
theorem residual_supply (P : E →L[ℝ] E) (A : ι → E →L[ℝ] E) (B : W →L[ℝ] E) (wt : ι → ℝ)
    {α μ m pn : ℝ} (ℓ : κ → ℝ) (hm : 0 < m) (hℓ : ∀ k, 0 ≤ ℓ k) (hPn : ‖P‖ ≤ pn)
    (hw : ∀ i, 0 ≤ wt i) (hs : ∑ i, wt i = 1)
    (hvertex : ∀ i y u, 2 * inner ℝ y (P (A i y + B u)) + α * storage P y ≤ μ * ‖u‖ ^ 2)
    (x : E) (d : W) (r : κ → E) (hcoerce : m * ‖x‖ ^ 2 ≤ storage P x)
    (hr : ∀ k, ‖r k‖ ≤ ℓ k * ‖x‖) :
    2 * inner ℝ x (P ((∑ i, wt i • A i x) + B d + ∑ k, r k)) +
      (α - 2 * pn * (∑ k, ℓ k) / m) * storage P x ≤ μ * ‖d‖ ^ 2 := by
  have h1 := vertex_supply P A B wt α μ hw hs hvertex x d
  have h2 := residual_sum_supply P ℓ hm hℓ hPn x r hcoerce hr
  rw [map_add, inner_add_right]
  nlinarith

end Generic

/-! ## The log tube from vertex LMIs and residuals -/

section Log

variable {ι κ W : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

local notation "E9" => EuclideanSpace ℝ (Fin 9)

/-- **Log tube from residuals.** The chart-closing log-error tube, with its supply hypothesis
discharged by vertex LMIs and a list of sector-bounded residuals. Only the decomposition of
the field (`hdecomp`) and the residual sectors (`hres`) are model-specific, and both are needed
only on the certified sublevel inside the principal domain. -/
theorem log_tube_of_residuals (P : E9 →L[ℝ] E9) (hP : ∀ u v, inner ℝ u (P v) = inner ℝ v (P u))
    (A : ι → E9 →L[ℝ] E9) (B : W →L[ℝ] E9)
    {X Y : ℝ → SE23} {a w abar wbar g gbar : ℝ → Vec3} {T α μ m pn δ ρ Rc : ℝ}
    (wt : ℝ → ι → ℝ) (d : ℝ → W) (ℓ : κ → ℝ) (r : ℝ → κ → E9)
    (hX : SpacecraftSolution X a w g T) (hY : SpacecraftSolution Y abar wbar gbar T)
    (hm : 0 < m) (hcoerce : ∀ x, m * ‖x‖ ^ 2 ≤ storage P x) (hℓ : ∀ k, 0 ≤ ℓ k)
    (hPn : ‖P‖ ≤ pn)
    (hvertex : ∀ i y u, 2 * inner ℝ y (P (A i y + B u)) + α * storage P y ≤ μ * ‖u‖ ^ 2)
    (hκ : 0 < α - 2 * pn * (∑ k, ℓ k) / m)
    (hbudget : μ * δ ^ 2 < (α - 2 * pn * (∑ k, ℓ k) / m) * ρ)
    (hμ : 0 ≤ μ) (hRc : Rc < π)
    (hchart : ∀ ξ : LogState, storage P (flat ξ) ≤ ρ → GNC.enorm (ξ 2) ≤ Rc)
    (hdom0 : SE23.error (Y 0) (X 0) ∈ PrincipalLog.domain)
    (hinit : storage P (flat (principalError X Y 0)) ≤ ρ)
    (hw : ∀ t ∈ Ico 0 T, ∀ i, 0 ≤ wt t i) (hs : ∀ t ∈ Ico 0 T, ∑ i, wt t i = 1)
    (hd : ∀ t ∈ Ico 0 T, ‖d t‖ ≤ δ)
    (hdecomp : ∀ t ∈ Ico 0 T, SE23.error (Y t) (X t) ∈ PrincipalLog.domain →
      storage P (flat (principalError X Y t)) ≤ ρ →
      flat (logErrorField X Y (a t) (w t) (abar t) (wbar t) (g t) (gbar t) t) =
        (∑ i, wt t i • A i (flat (principalError X Y t))) + B (d t) + ∑ k, r t k)
    (hres : ∀ t ∈ Ico 0 T, SE23.error (Y t) (X t) ∈ PrincipalLog.domain →
      storage P (flat (principalError X Y t)) ≤ ρ →
      ∀ k, ‖r t k‖ ≤ ℓ k * ‖flat (principalError X Y t)‖) :
    ∀ t ∈ Icc 0 T, SE23.error (Y t) (X t) ∈ PrincipalLog.domain ∧
      storage P (flat (principalError X Y t)) ≤ ρ ∧
      storage P (flat (principalError X Y t)) ≤
        max (storage P (flat (principalError X Y 0)))
          (μ * δ ^ 2 / (α - 2 * pn * (∑ k, ℓ k) / m)) := by
  refine log_error_tube P hP hX hY hκ hbudget hRc hchart hdom0 hinit ?_
  intro t ht hdom hρ
  rw [hdecomp t ht hdom hρ]
  have h := residual_supply P A B (wt t) ℓ hm hℓ hPn (hw t ht) (hs t ht) hvertex
    (flat (principalError X Y t)) (d t) (r t) (hcoerce _) (hres t ht hdom hρ)
  have hd2 : ‖d t‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hd t ht) 2
  nlinarith [mul_le_mul_of_nonneg_left hd2 hμ]

end Log

/-! ## Gravity residuals -/

/-- `‖flat (velocityOnly v)‖` is the Euclidean norm of `v`. -/
theorem flat_velocityOnly (v : Vec3) : ‖flat (velocityOnly v)‖ = GNC.enorm v := by
  unfold velocityOnly
  have h := flat_norm_sq ![0, v, 0]
  have h0 : GNC.enorm (0 : Vec3) = 0 := by simp [GNC.enorm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, h0] at h
  have := GNC.enorm_nonneg v
  have hn := norm_nonneg (flat (![0, v, 0] : LogState))
  nlinarith [sq_nonneg (‖flat (![0, v, 0] : LogState)‖ - GNC.enorm v),
    sq_nonneg (‖flat (![0, v, 0] : LogState)‖ + GNC.enorm v)]

/-- **Constant gravity.** When the vehicle and the reference see the same gravity, the gravity
term of the log-error field vanishes: the field is group-affine. -/
theorem gravity_residual_const (X : SE23) (ξ : LogState) (g : Vec3) :
    Jacobian.blockRightInverse ξ (adjoint X⁻¹ (velocityOnly (g - g))) = 0 := by
  funext i
  fin_cases i <;>
    simp [Jacobian.blockRightInverse, Jacobian.blockInverse, adjoint, velocityOnly, rotate]

/-- A rational bound on the inverse-Jacobian gain `(θ/2)/sin(θ/2)` for `θ ≤ 2`. -/
theorem inverseJacobianGain_le {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ ≤ 2) :
    Gravity.inverseJacobianGain θ ≤ 1 / (1 - θ ^ 2 / 16) := by
  unfold Gravity.inverseJacobianGain
  split_ifs with hz
  · subst hz; norm_num
  · have hθ : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hz)
    set x := θ / 2 with hx
    have hx0 : 0 < x := by positivity
    have hx1 : x ≤ 1 := by linarith
    have hs := sin_gt_sub_cube hx0 hx1
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hx3' : x ^ 3 ≤ x := by nlinarith
    have hx3 : 0 < x - x ^ 3 / 4 := by linarith
    have hsin : 0 < sin x := hx3.trans hs
    have hden : 0 < 1 - θ ^ 2 / 16 := by nlinarith
    have heq : 1 / (1 - θ ^ 2 / 16) = x / (x - x ^ 3 / 4) := by
      rw [hx]; field_simp; ring
    rw [heq]
    exact div_le_div_of_nonneg_left hx0.le hx3 hs.le

theorem inverseJacobianGain_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ < π) :
    0 ≤ Gravity.inverseJacobianGain θ := by
  unfold Gravity.inverseJacobianGain
  split_ifs with hz
  · norm_num
  · have hθ : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hz)
    exact div_nonneg (by linarith) (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))

/-- The sharp inverse-square mismatch is a sector on `d ≤ D < r_min ≤ r`. -/
theorem mismatchBound_le {μ r d rmin D : ℝ} (hμ : 0 ≤ μ) (hd : 0 ≤ d) (hdD : d ≤ D)
    (hDr : D < rmin) (hr : rmin ≤ r) :
    Gravity.mismatchBound μ r d ≤ (2 * μ / (rmin * (rmin - D) ^ 2)) * d := by
  unfold Gravity.mismatchBound
  have hrm : 0 < rmin := lt_of_le_of_lt (hd.trans hdD) hDr
  have hr0 : 0 < r := hrm.trans_le hr
  have hgap : 0 < rmin - D := by linarith
  have hgap' : rmin - D ≤ r - d := by linarith
  have hrd : 0 < r - d := hgap.trans_le hgap'
  have key : (2 * r - d) * (rmin * (rmin - D) ^ 2) ≤ 2 * (r ^ 2 * (r - d) ^ 2) := by
    have h1 : (2 * r - d) ≤ 2 * r := by linarith
    have h2 : rmin * (rmin - D) ^ 2 ≤ r * (r - d) ^ 2 :=
      mul_le_mul hr (pow_le_pow_left₀ hgap.le hgap' 2) (by positivity) hr0.le
    calc (2 * r - d) * (rmin * (rmin - D) ^ 2) ≤ (2 * r) * (r * (r - d) ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * (r ^ 2 * (r - d) ^ 2) := by ring
  have hmd : 0 ≤ μ * d := mul_nonneg hμ hd
  have hc : 0 < rmin * (rmin - D) ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  have hK : 2 * μ / (rmin * (rmin - D) ^ 2) * d * (r ^ 2 * (r - d) ^ 2) =
      μ * d * (2 * (r ^ 2 * (r - d) ^ 2)) / (rmin * (rmin - D) ^ 2) := by
    field_simp
  rw [hK, le_div_iff₀ hc]
  calc μ * d * (2 * r - d) * (rmin * (rmin - D) ^ 2)
      = μ * d * ((2 * r - d) * (rmin * (rmin - D) ^ 2)) := by ring
    _ ≤ μ * d * (2 * (r ^ 2 * (r - d) ^ 2)) := mul_le_mul_of_nonneg_left key hmd

/-- **Inverse-square gravity.** On the certified region (`‖ξ‖ ≤ D` below the reference radius
`r_min`, attitude error `≤ Rc ≤ 2`), the gravity term of the log-error field for vehicle `X` and
reference `Y` in the field `-μ p/‖p‖³` is a sector:
`‖gravity term‖ ≤ (1/(1 - Rc²/16)) · (2μ/(r_min (r_min - D)²)) · ‖ξ‖`. -/
theorem gravity_residual_inverse_square (μ : ℝ) (hμ : 0 ≤ μ) (Y X : SE23)
    (hd : SE23.error Y X ∈ PrincipalLog.domain) {rmin D Rc : ℝ} (hRc0 : 0 ≤ Rc) (hRc : Rc ≤ 2)
    (hDr : D < rmin) (hr : rmin ≤ GNC.enorm Y.pos)
    (hξ : ‖flat (PrincipalLog.log (SE23.error Y X))‖ ≤ D)
    (hθ : GNC.enorm (PrincipalLog.log (SE23.error Y X) 2) ≤ Rc) :
    ‖flat (Jacobian.blockRightInverse (PrincipalLog.log (SE23.error Y X))
        (adjoint X⁻¹ (velocityOnly (Gravity.field3 μ X.pos - Gravity.field3 μ Y.pos))))‖ ≤
      (1 / (1 - Rc ^ 2 / 16)) * (2 * μ / (rmin * (rmin - D) ^ 2)) *
        ‖flat (PrincipalLog.log (SE23.error Y X))‖ := by
  set ξ := PrincipalLog.log (SE23.error Y X) with hξdef
  have hspec := PrincipalLog.log_spec hd
  have hφ : GNC.enorm (ξ 2) < π := hspec.1
  have he : SE23.error Y X = groupExp ξ := hspec.2.symm
  rw [gravity_right_transport Y X ξ _ he (by linarith [pi_pos]),
    Jacobian.blockInverse_velocityOnly, flat_velocityOnly,
    physical_separation Y X ξ he]
  have hρ0 : GNC.enorm (ξ 0) ≤ ‖flat ξ‖ := enorm_component_le_flat ξ 0
  have hρ : GNC.enorm (ξ 0) < GNC.enorm Y.pos := by linarith
  have hb := Gravity.log_mismatch_bound μ hμ Y.rot Y.pos (ξ 0) (ξ 2) hρ hφ
  have hg0 := inverseJacobianGain_nonneg (GNC.enorm_nonneg (ξ 2)) hφ
  have hg := inverseJacobianGain_le (GNC.enorm_nonneg (ξ 2)) (hθ.trans hRc)
  have hden : 0 < 1 - Rc ^ 2 / 16 := by nlinarith
  have hgmono : 1 / (1 - GNC.enorm (ξ 2) ^ 2 / 16) ≤ 1 / (1 - Rc ^ 2 / 16) := by
    apply one_div_le_one_div_of_le hden
    have := pow_le_pow_left₀ (GNC.enorm_nonneg (ξ 2)) hθ 2
    linarith
  have hm := mismatchBound_le hμ (GNC.enorm_nonneg (ξ 0)) (hρ0.trans hξ) hDr hr
  have hm0 : 0 ≤ Gravity.mismatchBound μ (GNC.enorm Y.pos) (GNC.enorm (ξ 0)) := by
    unfold Gravity.mismatchBound
    have hr0 : 0 < GNC.enorm Y.pos := lt_of_le_of_lt (GNC.enorm_nonneg _) hρ
    apply div_nonneg
    · apply mul_nonneg (mul_nonneg hμ (GNC.enorm_nonneg _)); linarith
    · positivity
  have hrm : 0 < rmin := lt_of_le_of_lt ((norm_nonneg _).trans hξ) hDr
  have hk : 0 ≤ 2 * μ / (rmin * (rmin - D) ^ 2) := by
    apply div_nonneg (by linarith); have : 0 < rmin - D := by linarith
    positivity
  calc GNC.enorm (Jacobian.inverseAt (ξ 2) (rotate Y.rot⁻¹
        (Gravity.field3 μ (Y.pos + physicalImpulse Y.rot (ξ 2) (ξ 0)) -
          Gravity.field3 μ Y.pos)))
      ≤ Gravity.inverseJacobianGain (GNC.enorm (ξ 2)) *
          Gravity.mismatchBound μ (GNC.enorm Y.pos) (GNC.enorm (ξ 0)) := hb
    _ ≤ (1 / (1 - Rc ^ 2 / 16)) * ((2 * μ / (rmin * (rmin - D) ^ 2)) * GNC.enorm (ξ 0)) :=
        mul_le_mul (hg.trans hgmono) hm hm0 (by positivity)
    _ ≤ (1 / (1 - Rc ^ 2 / 16)) * ((2 * μ / (rmin * (rmin - D) ^ 2)) * ‖flat ξ‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hρ0 hk
    _ = _ := by ring

end Dynacert.Lie
