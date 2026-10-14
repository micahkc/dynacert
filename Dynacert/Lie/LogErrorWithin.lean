import GNC.Control.LocalLogBackstepping

/-!
# Right-derivative log error dynamics on SE₂(3)

gnc_lean's `principal_proposition1_at` gives the principal-log error ODE when the vehicle and
reference have two-sided derivatives at `t`. dynacert's solution notion only provides right
derivatives (`HasDerivWithinAt _ _ (Ici t) t`). This file proves the same identity for right
derivatives.

The proof does not redo the Lie theory. Near a point of the principal domain, the principal
error is a fixed function `errorLogMat E₀` of the pair of 5×5 matrices `(Y, X)`, and that
function is Fréchet differentiable. So the one-sided derivative of the log error is
`fderiv (errorLogMat E₀) (Y t, X t)` applied to the matrix derivatives. For two-sided
comparison curves with the same values and derivatives at `t`, gnc's theorem identifies this
number with the closed-form vector field.
-/

noncomputable section

namespace Dynacert.Lie

open GNC Matrix Set Filter
open scoped Matrix Matrix.Norms.Operator Topology Manifold ContDiff

/-- The three physical equations (position, velocity, attitude) with **right** derivatives at
`t`; the one-sided analogue of gnc's `SpacecraftODEAt`. -/
def SpacecraftODEWithin (X : ℝ → SE23) (a w g : Vec3) (t : ℝ) : Prop :=
  HasDerivWithinAt (fun s => (X s).pos) (X t).vel (Ici t) t ∧
  HasDerivWithinAt (fun s => (X s).vel) (rotate (X t).rot a + g) (Ici t) t ∧
  HasDerivWithinAt (fun s => (X s).rot.val) ((X t).rot.val * skew w) (Ici t) t

/-- The closed-form principal-log error vector field (right-hand side of gnc's
`principal_proposition1_at`). -/
def logErrorField (X Y : ℝ → SE23) (a w abar wbar g gbar : Vec3) (t : ℝ) : LogState :=
  logDrift (Jacobian.controlInput a w) (principalError X Y t) +
    Jacobian.blockInverse (principalError X Y t) (Jacobian.controlInput (a - abar) (w - wbar)) +
    Jacobian.blockRightInverse (principalError X Y t) (adjoint (X t)⁻¹ (velocityOnly (g - gbar)))

/-! ## Componentwise derivatives and continuity give the matrix curve -/

theorem matrix_hasDerivWithinAt {X : ℝ → SE23} {a w g : Vec3} {S : Set ℝ} {t : ℝ}
    (hp : HasDerivWithinAt (fun s => (X s).pos) (X t).vel S t)
    (hv : HasDerivWithinAt (fun s => (X s).vel) (rotate (X t).rot a + g) S t)
    (hr : HasDerivWithinAt (fun s => (X s).rot.val) ((X t).rot.val * skew w) S t) :
    HasDerivWithinAt (fun s => SE23.toMatrix (X s))
      (spacecraftDerivative (X t) (Jacobian.controlInput a w) g) S t := by
  rw [spacecraftDerivative_components]
  apply hasDerivWithinAt_pi.mpr
  intro i
  apply hasDerivWithinAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> first
    | exact hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp hr _) _
    | exact hasDerivWithinAt_pi.mp hv _
    | exact hasDerivWithinAt_pi.mp hp _
    | exact hasDerivWithinAt_const t S (0:ℝ)
    | exact hasDerivWithinAt_const t S (1:ℝ)

theorem matrix_continuousWithinAt {X : ℝ → SE23} {S : Set ℝ} {t : ℝ}
    (hp : ContinuousWithinAt (fun s => (X s).pos) S t)
    (hv : ContinuousWithinAt (fun s => (X s).vel) S t)
    (hr : ContinuousWithinAt (fun s => (X s).rot.val) S t) :
    ContinuousWithinAt (fun s => SE23.toMatrix (X s)) S t := by
  apply continuousWithinAt_pi.mpr
  intro i
  apply continuousWithinAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> first
    | exact continuousWithinAt_pi.mp (continuousWithinAt_pi.mp hr _) _
    | exact continuousWithinAt_pi.mp hv _
    | exact continuousWithinAt_pi.mp hp _
    | exact continuousWithinAt_const

/-- Continuity of the matrix curve gives continuity in the Lie group topology. -/
theorem se23_continuousWithinAt {X : ℝ → SE23} {S : Set ℝ} {t : ℝ}
    (hM : ContinuousWithinAt (fun s => SE23.toMatrix (X s)) S t) :
    ContinuousWithinAt X S t := by
  have hr : ContinuousWithinAt (fun s => (X s).rot.val) S t := by
    simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', rotationBlock_toMatrix]
      using rotationBlock.toContinuousLinearMap.continuous.continuousAt.comp_continuousWithinAt hM
  have hv : ContinuousWithinAt (fun s => (X s).vel) S t := by
    simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', velocityBlock_toMatrix]
      using velocityBlock.toContinuousLinearMap.continuous.continuousAt.comp_continuousWithinAt hM
  have hp : ContinuousWithinAt (fun s => (X s).pos) S t := by
    simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', positionBlock_toMatrix]
      using positionBlock.toContinuousLinearMap.continuous.continuousAt.comp_continuousWithinAt hM
  have hrc : ContinuousWithinAt (fun s => (X s).rot) S t :=
    Topology.IsInducing.subtypeVal.continuousWithinAt_iff.mpr hr
  exact SE23.productHomeomorph.symm.continuous.continuousAt.comp_continuousWithinAt
    (hrc.prodMk (hv.prodMk hp))

/-! ## The principal log as a differentiable function of matrices near a domain point -/

/-- Chart coordinates of a 5×5 matrix, in the gnc chart centred at `E₀`. -/
def chartMat (E₀ : SE23) (M : Mat5) : SE23.Model :=
  (Cayley.unskew (Cayley.ratio ((E₀.rot⁻¹).val * rotationBlock M)), velocityBlock M,
    positionBlock M)

/-- The principal log read through the chart at `E₀`, as a function of a 5×5 matrix. -/
def logNear (E₀ : SE23) (M : Mat5) : LogState :=
  PrincipalLog.log ((extChartAt 𝓘(ℝ, SE23.Model) E₀).symm (chartMat E₀ M))

/-- The principal log of `Y⁻¹ X` as a function of the pair of matrices `(Y, X)`. -/
def errorLogMat (E₀ : SE23) (p : Mat5 × Mat5) : LogState :=
  logNear E₀ (Ring.inverse p.1 * p.2)

theorem chartMat_toMatrix (E₀ Z : SE23) :
    chartMat E₀ (SE23.toMatrix Z) = extChartAt 𝓘(ℝ, SE23.Model) E₀ Z := by
  rw [SE23.extChartAt_apply]
  simp only [chartMat, rotationBlock_toMatrix, velocityBlock_toMatrix, positionBlock_toMatrix,
    Cayley.coordinates]
  rfl

theorem logNear_toMatrix {E₀ Z : SE23} (hZ : Z ∈ (extChartAt 𝓘(ℝ, SE23.Model) E₀).source) :
    logNear E₀ (SE23.toMatrix Z) = PrincipalLog.log Z := by
  rw [logNear, chartMat_toMatrix, PartialEquiv.left_inv _ hZ]

theorem errorLogMat_toMatrix {E₀ Y X : SE23}
    (hZ : SE23.error Y X ∈ (extChartAt 𝓘(ℝ, SE23.Model) E₀).source) :
    errorLogMat E₀ (SE23.toMatrix Y, SE23.toMatrix X) = PrincipalLog.log (SE23.error Y X) := by
  rw [errorLogMat, matrix_inverse, ← SE23.toMatrix_mul]
  exact logNear_toMatrix hZ

theorem chartMat_contDiffAt (E₀ : SE23) : ContDiffAt ℝ ∞ (chartMat E₀) (SE23.toMatrix E₀) := by
  have hunit : IsUnit ((E₀.rot⁻¹).val * rotationBlock (SE23.toMatrix E₀) + 1).det := by
    rw [rotationBlock_toMatrix]
    change E₀.rot⁻¹ * E₀.rot ∈ Cayley.domain
    simpa using Cayley.one_mem_domain
  have hlin : ContDiff ℝ ∞ (fun M : Mat5 => (E₀.rot⁻¹).val * rotationBlock M) :=
    contDiff_const.mul rotationBlock.toContinuousLinearMap.contDiff
  have h0 : ContDiffAt ℝ ∞ (fun M : Mat5 => (E₀.rot⁻¹).val * rotationBlock M)
      (SE23.toMatrix E₀) := hlin.contDiffAt
  have hr : ContDiffAt ℝ ∞ (fun A => Cayley.unskew (Cayley.ratio A))
      ((E₀.rot⁻¹).val * rotationBlock (SE23.toMatrix E₀)) :=
    Cayley.contDiff_unskew.contDiffAt.comp _ (Cayley.contDiffAt_ratio _ hunit)
  have h1 := ContDiffAt.comp (SE23.toMatrix E₀) hr h0
  exact h1.prodMk (velocityBlock.toContinuousLinearMap.contDiff.contDiffAt.prodMk
    positionBlock.toContinuousLinearMap.contDiff.contDiffAt)

theorem logNear_differentiableAt {E₀ : SE23} (hd : E₀ ∈ PrincipalLog.domain) :
    DifferentiableAt ℝ (logNear E₀) (SE23.toMatrix E₀) := by
  have hm := ((PrincipalLog.log_contMDiffAt hd).mdifferentiableAt (by simp))
  rw [mdifferentiableAt_iff] at hm
  have hw := hm.2
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    modelWithCornersSelf_coe, range_id, differentiableWithinAt_univ] at hw
  have hc := (chartMat_contDiffAt E₀).differentiableAt (by simp)
  rw [← chartMat_toMatrix] at hw
  exact hw.comp _ hc

theorem errorLogMat_differentiableAt {Y X : SE23} (hd : SE23.error Y X ∈ PrincipalLog.domain) :
    DifferentiableAt ℝ (errorLogMat (SE23.error Y X)) (SE23.toMatrix Y, SE23.toMatrix X) := by
  have hri : DifferentiableAt ℝ (Ring.inverse : Mat5 → Mat5) (SE23.toMatrix Y) :=
    (hasFDerivAt_ringInverse (𝕜 := ℝ) (SE23.matrixUnits Y)).differentiableAt
  have hinv : DifferentiableAt ℝ (fun p : Mat5 × Mat5 => Ring.inverse p.1)
      (SE23.toMatrix Y, SE23.toMatrix X) :=
    hri.comp (x := (SE23.toMatrix Y, SE23.toMatrix X)) (g := Ring.inverse) differentiableAt_fst
  have hprod : DifferentiableAt ℝ (fun p : Mat5 × Mat5 => Ring.inverse p.1 * p.2)
      (SE23.toMatrix Y, SE23.toMatrix X) := hinv.mul differentiableAt_snd
  have hval : Ring.inverse (SE23.toMatrix Y, SE23.toMatrix X).1 *
      (SE23.toMatrix Y, SE23.toMatrix X).2 = SE23.toMatrix (SE23.error Y X) := by
    simp only [matrix_inverse, SE23.error, SE23.toMatrix_mul]
  have hl := logNear_differentiableAt hd
  rw [← hval] at hl
  exact DifferentiableAt.comp (g := logNear (SE23.error Y X))
    (f := fun p : Mat5 × Mat5 => Ring.inverse p.1 * p.2) _ hl hprod

/-- **Key lemma.** Along any set `S`, the derivative within `S` of the principal error is a
fixed linear map applied to the matrix derivatives of `Y` and `X`. -/
theorem principalError_hasDerivWithinAt_of_matrix {X Y : ℝ → SE23} {S : Set ℝ} {t : ℝ}
    {dX dY : Mat5}
    (hX : HasDerivWithinAt (fun s => SE23.toMatrix (X s)) dX S t)
    (hY : HasDerivWithinAt (fun s => SE23.toMatrix (Y s)) dY S t)
    (hd : SE23.error (Y t) (X t) ∈ PrincipalLog.domain) :
    HasDerivWithinAt (principalError X Y)
      (fderiv ℝ (errorLogMat (SE23.error (Y t) (X t))) (SE23.toMatrix (Y t), SE23.toMatrix (X t))
        (dY, dX)) S t := by
  set E₀ := SE23.error (Y t) (X t)
  have hH := (errorLogMat_differentiableAt hd).hasFDerivAt
  have hcomp := hH.comp_hasDerivWithinAt t (hY.prodMk hX)
  have hEc : ContinuousWithinAt (fun s => SE23.error (Y s) (X s)) S t :=
    ((se23_continuousWithinAt hY.continuousWithinAt).inv).mul
      (se23_continuousWithinAt hX.continuousWithinAt)
  have hsrc : (extChartAt 𝓘(ℝ, SE23.Model) E₀).source ∈ 𝓝 E₀ :=
    extChartAt_source_mem_nhds E₀
  have hev : ∀ᶠ s in 𝓝[S] t, SE23.error (Y s) (X s) ∈ (extChartAt 𝓘(ℝ, SE23.Model) E₀).source :=
    hEc hsrc
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hev] with s hs
    exact (errorLogMat_toMatrix hs).symm
  · exact (errorLogMat_toMatrix (mem_extChartAt_source E₀)).symm

/-- Continuity of the principal error within any set, at a point whose error lies in the
principal domain. -/
theorem principalError_continuousWithinAt {X Y : ℝ → SE23} {S : Set ℝ} {t : ℝ}
    (hX : ContinuousWithinAt (fun s => SE23.toMatrix (X s)) S t)
    (hY : ContinuousWithinAt (fun s => SE23.toMatrix (Y s)) S t)
    (hd : SE23.error (Y t) (X t) ∈ PrincipalLog.domain) :
    ContinuousWithinAt (principalError X Y) S t := by
  set E₀ := SE23.error (Y t) (X t)
  have hH := (errorLogMat_differentiableAt hd).continuousAt
  have hcomp := ContinuousAt.comp_continuousWithinAt
    (f := fun s => (SE23.toMatrix (Y s), SE23.toMatrix (X s))) hH (hY.prodMk hX)
  have hEc : ContinuousWithinAt (fun s => SE23.error (Y s) (X s)) S t :=
    ((se23_continuousWithinAt hY).inv).mul (se23_continuousWithinAt hX)
  have hev : ∀ᶠ s in 𝓝[S] t, SE23.error (Y s) (X s) ∈ (extChartAt 𝓘(ℝ, SE23.Model) E₀).source :=
    hEc (extChartAt_source_mem_nhds E₀)
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hev] with s hs
    exact (errorLogMat_toMatrix hs).symm
  · exact (errorLogMat_toMatrix (mem_extChartAt_source E₀)).symm

/-! ## Two-sided comparison curves -/

/-- A smooth curve through `x₀` at time `t` whose two-sided derivative at `t` matches the
spacecraft kinematics with inputs `a`, `w`, `g`. -/
def comparisonCurve (x₀ : SE23) (a w g : Vec3) (t s : ℝ) : SE23 :=
  ⟨x₀.rot * rotationExp ((s - t) • w), x₀.vel + (s - t) • (rotate x₀.rot a + g),
    x₀.pos + (s - t) • x₀.vel⟩

theorem skew_zero' : skew (0 : Vec3) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [skew]

theorem rotationExp_zero' : rotationExp 0 = 1 := by
  apply Subtype.ext
  simp [rotationExp, skew_zero']

theorem comparisonCurve_self (x₀ : SE23) (a w g : Vec3) (t : ℝ) :
    comparisonCurve x₀ a w g t t = x₀ := by
  simp [comparisonCurve, rotationExp_zero']

theorem comparisonCurve_ode (x₀ : SE23) (a w g : Vec3) (t : ℝ) :
    SpacecraftODEAt (comparisonCurve x₀ a w g t) a w g t := by
  rw [SpacecraftODEAt, comparisonCurve_self]
  have hlin : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  refine ⟨?_, ?_, ?_⟩
  · simpa [comparisonCurve] using (hlin.smul_const x₀.vel).const_add x₀.pos
  · simpa [comparisonCurve] using (hlin.smul_const (rotate x₀.rot a + g)).const_add x₀.vel
  · have he : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • skew w))
        (NormedSpace.exp ((t - t) • skew w) * skew w) (t - t) :=
      hasDerivAt_exp_smul_const (skew w) (t - t)
    have he' := HasDerivAt.scomp (h := fun s : ℝ => s - t) t he hlin
    have hm := he'.const_mul x₀.rot.val
    simp only [sub_self, zero_smul, NormedSpace.exp_zero, one_mul, Function.comp_def,
      one_smul] at hm
    convert hm using 1
    funext s
    simp [comparisonCurve, rotationExp, skew_smul]

/-- **Right-derivative Proposition 1.** With only right derivatives of the vehicle and
reference kinematics at `t`, and the error at `t` in the principal domain, the principal log
error has right derivative given by gnc's closed-form vector field. -/
theorem principal_proposition1_within {X Y : ℝ → SE23} {a w abar wbar g gbar : Vec3} {t : ℝ}
    (hX : SpacecraftODEWithin X a w g t) (hY : SpacecraftODEWithin Y abar wbar gbar t)
    (hd : SE23.error (Y t) (X t) ∈ PrincipalLog.domain) :
    HasDerivWithinAt (principalError X Y) (logErrorField X Y a w abar wbar g gbar t)
      (Ici t) t := by
  set X' := comparisonCurve (X t) a w g t
  set Y' := comparisonCurve (Y t) abar wbar gbar t
  have hXt : X' t = X t := comparisonCurve_self _ _ _ _ _
  have hYt : Y' t = Y t := comparisonCurve_self _ _ _ _ _
  have hX'ode := comparisonCurve_ode (X t) a w g t
  have hY'ode := comparisonCurve_ode (Y t) abar wbar gbar t
  have hd' : SE23.error (Y' t) (X' t) ∈ PrincipalLog.domain := by rwa [hXt, hYt]
  -- one-sided derivative of the true error
  have h1 := principalError_hasDerivWithinAt_of_matrix
    (matrix_hasDerivWithinAt hX.1 hX.2.1 hX.2.2) (matrix_hasDerivWithinAt hY.1 hY.2.1 hY.2.2) hd
  -- two-sided derivative of the comparison error, with the same value
  have h2 := principalError_hasDerivWithinAt_of_matrix (S := univ)
    ((spacecraft_ode_iff _ a w g t).mp hX'ode).hasDerivWithinAt
    ((spacecraft_ode_iff _ abar wbar gbar t).mp hY'ode).hasDerivWithinAt hd'
  rw [hasDerivWithinAt_univ] at h2
  have h3 := principal_proposition1_at hX'ode hY'ode hd'
  rw [h2.deriv] at h3
  have hpe : principalError X' Y' t = principalError X Y t := by
    simp only [principalError, hXt, hYt]
  rw [hpe] at h3
  simp only [comparisonCurve_self] at h3
  convert h1 using 1
  rw [logErrorField]
  exact h3.symm

end Dynacert.Lie
