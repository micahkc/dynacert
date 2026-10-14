import Dynacert.Core.Tube
import Dynacert.Lie.LogErrorWithin
import GNC.Lie.PrincipalDomain
import GNC.Lie.ExponentialCoordinates

/-!
# Chart-closing first-exit tube for the SE₂(3) log error

The principal log error `ξ = log (Y⁻¹ X)` is only differentiable while the group error stays in
the principal domain. This file proves, from continuity and right derivatives of the physical
trajectories alone, that a quadratic sublevel set `{storage P (flat ξ) ≤ ρ}` whose attitude
part is bounded by `Rc < π` is invariant, and that the error never leaves the principal chart.

The chart is closed on the group: on the sublevel set, `trace (Y⁻¹X).R = 1 + 2 cos ‖ξ_R‖ ≥
1 + 2 cos Rc > -1`, a closed condition on the continuous group error, so a limit of good times
is still in the principal domain.
-/

noncomputable section

namespace Dynacert.Lie

open GNC Matrix Set Filter Real GNC.PolytopicTube
open scoped Matrix Matrix.Norms.Operator Topology

/-! ## Flattening `LogState` to `ℝ⁹` -/

/-- Components ordered `(p₀,p₁,p₂, v₀,v₁,v₂, R₀,R₁,R₂)`. -/
def flatFun (ξ : LogState) : Fin 9 → ℝ :=
  ![ξ 0 0, ξ 0 1, ξ 0 2, ξ 1 0, ξ 1 1, ξ 1 2, ξ 2 0, ξ 2 1, ξ 2 2]

def unflatFun (z : Fin 9 → ℝ) : LogState :=
  ![![z 0, z 1, z 2], ![z 3, z 4, z 5], ![z 6, z 7, z 8]]

def flatLinearEquiv : LogState ≃ₗ[ℝ] (Fin 9 → ℝ) where
  toFun := flatFun
  invFun := unflatFun
  map_add' x y := by ext k; fin_cases k <;> rfl
  map_smul' c x := by ext k; fin_cases k <;> rfl
  left_inv ξ := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  right_inv z := by ext k; fin_cases k <;> rfl

/-- The flattening `LogState ≃L[ℝ] ℝ⁹`, components `(p, v, R)` in slots `0..8`. -/
def flat : LogState ≃L[ℝ] EuclideanSpace ℝ (Fin 9) :=
  (flatLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin 9 → ℝ)).symm).toContinuousLinearEquiv

@[simp] theorem flat_apply (ξ : LogState) (k : Fin 9) : flat ξ k = flatFun ξ k := rfl

theorem flat_norm_sq (ξ : LogState) :
    ‖flat ξ‖ ^ 2 = GNC.enorm (ξ 0) ^ 2 + GNC.enorm (ξ 1) ^ 2 + GNC.enorm (ξ 2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, enorm_sq, enorm_sq, enorm_sq]
  simp [Fin.sum_univ_succ, flatFun, lengthSq, sq_abs]
  ring

theorem enorm_attitude_le_flat (ξ : LogState) : GNC.enorm (ξ 2) ≤ ‖flat ξ‖ := by
  have h := flat_norm_sq ξ
  have h0 := sq_nonneg (GNC.enorm (ξ 0))
  have h1 := sq_nonneg (GNC.enorm (ξ 1))
  have h2 := GNC.enorm_nonneg (ξ 2)
  have h3 := norm_nonneg (flat ξ)
  by_contra hc
  push Not at hc
  nlinarith [mul_lt_mul'' hc hc h3 h3]

/-- A coercivity witness `m‖x‖² ≤ storage P x` with `ρ ≤ m Rc²` discharges the chart
hypothesis of `log_error_tube`. -/
theorem chart_of_coercive (P : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9))
    {m ρ Rc : ℝ} (hm : 0 < m) (hRc : 0 ≤ Rc)
    (hcoer : ∀ x, m * ‖x‖ ^ 2 ≤ storage P x) (hρ : ρ ≤ m * Rc ^ 2) :
    ∀ ξ : LogState, storage P (flat ξ) ≤ ρ → GNC.enorm (ξ 2) ≤ Rc := by
  intro ξ hξ
  have h1 := hcoer (flat ξ)
  have h2 := enorm_attitude_le_flat ξ
  have h3 : ‖flat ξ‖ ^ 2 ≤ Rc ^ 2 := by
    by_contra hc
    push Not at hc
    nlinarith
  have h4 : ‖flat ξ‖ ≤ Rc := by
    nlinarith [norm_nonneg (flat ξ)]
  exact h2.trans h4

/-! ## Closing the principal chart through the trace -/

theorem trace_groupExp_ge {ξ : LogState} {Rc : ℝ} (hRc : Rc ≤ π) (hξ : GNC.enorm (ξ 2) ≤ Rc) :
    1 + 2 * cos Rc ≤ (groupExp ξ).rot.val.trace := by
  change 1 + 2 * cos Rc ≤ (rotationExp (ξ 2)).val.trace
  rw [rotationExp_trace]
  have := cos_le_cos_of_nonneg_of_le_pi (enorm_nonneg _) hRc hξ
  linarith

theorem mem_domain_of_trace_ge {Z : SE23} {Rc : ℝ} (h0 : 0 ≤ Rc) (hRc : Rc < π)
    (hZ : 1 + 2 * cos Rc ≤ Z.rot.val.trace) : Z ∈ PrincipalLog.domain := by
  rw [PrincipalLog.domain_iff_trace]
  have hc : cos π < cos Rc := cos_lt_cos_of_nonneg_of_le_pi h0 le_rfl hRc
  rw [cos_pi] at hc
  intro h
  linarith

/-! ## Physical solutions with right derivatives -/

/-- A spacecraft trajectory on `[0, T]`: continuous components on `[0, T]` and the three
kinematic equations with right derivatives on `[0, T)`. A Modelica model with nine scalar
attitude states provides this once `R ∈ SO(3)` is established (see `Dynacert.Lie.SO3`). -/
structure SpacecraftSolution (X : ℝ → SE23) (a w g : ℝ → Vec3) (T : ℝ) : Prop where
  pos_cont : ContinuousOn (fun s => (X s).pos) (Icc 0 T)
  vel_cont : ContinuousOn (fun s => (X s).vel) (Icc 0 T)
  rot_cont : ContinuousOn (fun s => (X s).rot.val) (Icc 0 T)
  ode : ∀ t ∈ Ico 0 T, SpacecraftODEWithin X (a t) (w t) (g t) t

theorem SpacecraftSolution.matrix_continuousOn {X : ℝ → SE23} {a w g : ℝ → Vec3} {T : ℝ}
    (hX : SpacecraftSolution X a w g T) :
    ContinuousOn (fun s => SE23.toMatrix (X s)) (Icc 0 T) := fun t ht =>
  matrix_continuousWithinAt (hX.pos_cont t ht) (hX.vel_cont t ht) (hX.rot_cont t ht)

theorem SpacecraftSolution.matrix_hasDerivWithinAt {X : ℝ → SE23} {a w g : ℝ → Vec3} {T : ℝ}
    (hX : SpacecraftSolution X a w g T) {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => SE23.toMatrix (X s))
      (spacecraftDerivative (X t) (Jacobian.controlInput (a t) (w t)) (g t)) (Ici t) t :=
  Dynacert.Lie.matrix_hasDerivWithinAt (hX.ode t ht).1 (hX.ode t ht).2.1 (hX.ode t ht).2.2

/-- Eventually-on-the-right decrease from a negative right derivative. -/
theorem eventually_lt_of_hasDerivWithinAt_neg {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivWithinAt f f' (Ici x) x) (hneg : f' < 0) : ∀ᶠ z in 𝓝[>] x, f z < f x := by
  have h := hasDerivWithinAt_iff_tendsto_slope.mp hf
  rw [Ici_diff_left] at h
  filter_upwards [h (Iio_mem_nhds hneg), self_mem_nhdsWithin] with z hz hzx
  simp only [mem_preimage, mem_Iio, slope_def_field] at hz
  have hpos : 0 < z - x := sub_pos.mpr hzx
  have := (div_neg_iff.mp hz)
  rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
  · linarith
  · linarith

variable (P : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9))

/-- **Chart-closing log-error tube.** Vehicle `X` and reference `Y` solve the spacecraft
kinematics with right derivatives. If the supply inequality for the closed-form log-error
vector field holds on the sublevel `{storage ≤ ρ}` (whenever the error is in the principal
domain), `β < κρ`, the sublevel is attitude-bounded by `Rc < π`, and the error starts in the
principal domain inside the sublevel, then the error stays in the principal domain and in the
sublevel on `[0, T]`, and the storage decays to `β/κ`. -/
theorem log_error_tube
    (hP : ∀ u v, inner ℝ u (P v) = inner ℝ v (P u))
    {X Y : ℝ → SE23} {a w abar wbar g gbar : ℝ → Vec3} {T κ β ρ Rc : ℝ}
    (hX : SpacecraftSolution X a w g T) (hY : SpacecraftSolution Y abar wbar gbar T)
    (hκ : 0 < κ) (hbudget : β < κ * ρ) (hRc : Rc < π)
    (hchart : ∀ ξ : LogState, storage P (flat ξ) ≤ ρ → GNC.enorm (ξ 2) ≤ Rc)
    (hdom0 : SE23.error (Y 0) (X 0) ∈ PrincipalLog.domain)
    (hinit : storage P (flat (principalError X Y 0)) ≤ ρ)
    (hsupply : ∀ t ∈ Ico 0 T, SE23.error (Y t) (X t) ∈ PrincipalLog.domain →
      storage P (flat (principalError X Y t)) ≤ ρ →
      2 * inner ℝ (flat (principalError X Y t))
          (P (flat (logErrorField X Y (a t) (w t) (abar t) (wbar t) (g t) (gbar t) t))) +
        κ * storage P (flat (principalError X Y t)) ≤ β) :
    ∀ t ∈ Icc 0 T, SE23.error (Y t) (X t) ∈ PrincipalLog.domain ∧
      storage P (flat (principalError X Y t)) ≤ ρ ∧
      storage P (flat (principalError X Y t)) ≤
        max (storage P (flat (principalError X Y 0))) (β / κ) := by
  set ξ := principalError X Y with hξdef
  set V : ℝ → ℝ := fun t => storage P (flat (ξ t)) with hVdef
  set F : ℝ → LogState := fun t => logErrorField X Y (a t) (w t) (abar t) (wbar t) (g t) (gbar t) t
  set E : ℝ → SE23 := fun t => SE23.error (Y t) (X t) with hEdef
  have hRc0 : 0 ≤ Rc := (enorm_nonneg _).trans (hchart _ hinit)
  have hXM := hX.matrix_continuousOn
  have hYM := hY.matrix_continuousOn
  -- continuity of the group error on [0, T]
  have hEc : ContinuousOn E (Icc 0 T) := fun t ht =>
    ((se23_continuousWithinAt (hYM t ht)).inv).mul (se23_continuousWithinAt (hXM t ht))
  -- V is continuous within any set at a domain point, given continuity of X, Y there
  have hVc : ∀ t ∈ Icc 0 T, E t ∈ PrincipalLog.domain → ContinuousWithinAt V (Icc 0 T) t :=
    fun t ht hd => (storage_continuous P).continuousAt.comp_continuousWithinAt
      (flat.continuous.continuousAt.comp_continuousWithinAt
        (principalError_continuousWithinAt (hXM t ht) (hYM t ht) hd))
  -- right derivative of V at a domain point
  have hVd : ∀ t ∈ Ico 0 T, E t ∈ PrincipalLog.domain →
      HasDerivWithinAt V (2 * inner ℝ (flat (ξ t)) (P (flat (F t)))) (Ici t) t := by
    intro t ht hd
    have h := principal_proposition1_within (hX.ode t ht) (hY.ode t ht) hd
    exact storage_hasDerivWithinAt P hP (flat.hasFDerivAt.comp_hasDerivWithinAt t h)
  -- the good set
  set good : Set ℝ := {t | E t ∈ PrincipalLog.domain ∧ V t ≤ ρ} with hgood
  have hgood_trace : ∀ t ∈ good, 1 + 2 * cos Rc ≤ (E t).rot.val.trace := by
    intro t ht
    have hspec := PrincipalLog.log_spec ht.1
    have hb := hchart (ξ t) ht.2
    rw [← hspec.2]
    exact trace_groupExp_ge hRc.le hb
  have hclosed : IsClosed (good ∩ Icc 0 T) := by
    apply isClosed_of_closure_subset
    intro t ht
    have htI : t ∈ Icc 0 T :=
      (isClosed_Icc.closure_subset_iff.mpr inter_subset_right) ht
    have htrc : ContinuousWithinAt (fun s => (E s).rot.val.trace) (good ∩ Icc 0 T) t :=
      ((continuous_id.matrix_trace).comp (continuous_subtype_val.comp SE23.continuous_rot)
        ).continuousAt.comp_continuousWithinAt ((hEc t htI).mono inter_subset_right)
    have htr : 1 + 2 * cos Rc ≤ (E t).rot.val.trace :=
      ContinuousWithinAt.closure_le (f := fun _ => 1 + 2 * cos Rc)
        (g := fun s => (E s).rot.val.trace) ht continuousWithinAt_const
        htrc (fun s hs => hgood_trace s hs.1)
    have hd : E t ∈ PrincipalLog.domain := mem_domain_of_trace_ge hRc0 hRc htr
    have hV : V t ≤ ρ :=
      ContinuousWithinAt.closure_le (f := V) (g := fun _ => ρ) ht
        ((hVc t htI hd).mono inter_subset_right) continuousWithinAt_const
        (fun s hs => hs.1.2)
    exact ⟨⟨hd, hV⟩, htI⟩
  have hopen : ∀ x ∈ good ∩ Ico 0 T, good ∈ 𝓝[>] x := by
    rintro x ⟨⟨hxd, hxV⟩, hxI⟩
    have hle : 𝓝[>] x ≤ 𝓝[≥] x := nhdsWithin_mono _ Ioi_subset_Ici_self
    -- the error stays in the (open) domain to the right
    have hEx : ContinuousWithinAt E (Ici x) x :=
      ((se23_continuousWithinAt (hY.matrix_hasDerivWithinAt hxI).continuousWithinAt).inv).mul
        (se23_continuousWithinAt (hX.matrix_hasDerivWithinAt hxI).continuousWithinAt)
    have hdom : ∀ᶠ s in 𝓝[≥] x, E s ∈ PrincipalLog.domain :=
      hEx (PrincipalLog.isOpen_domain.mem_nhds hxd)
    have hVx := hVd x hxI hxd
    have hVle : ∀ᶠ s in 𝓝[>] x, V s ≤ ρ := by
      rcases hxV.lt_or_eq with hlt | heq
      · exact hle (hVx.continuousWithinAt.eventually (gt_mem_nhds hlt) |>.mono
          fun s hs => hs.le)
      · have hs := hsupply x hxI hxd hxV
        have hneg : 2 * inner ℝ (flat (ξ x)) (P (flat (F x))) < 0 := by
          change 2 * inner ℝ (flat (ξ x)) (P (flat (F x))) + κ * V x ≤ β at hs
          rw [heq] at hs
          linarith
        exact (eventually_lt_of_hasDerivWithinAt_neg hVx hneg).mono
          fun s hs => (hs.trans_eq heq).le
    filter_upwards [hle hdom, hVle] with s h1 h2
    exact ⟨h1, h2⟩
  have hall : ∀ t ∈ Icc 0 T, t ∈ good := by
    intro t ht
    have h0 : (0 : ℝ) ∈ good := ⟨hdom0, hinit⟩
    exact IsClosed.Icc_subset_of_forall_mem_nhdsWithin hclosed h0 hopen ht
  -- decay via the right-derivative Grönwall bound
  have hVcont : ContinuousOn V (Icc 0 T) := fun t ht => hVc t ht (hall t ht).1
  have hdecay := dissipation_bound (v' := fun t => 2 * inner ℝ (flat (ξ t)) (P (flat (F t))))
    hκ hVcont (fun t ht => hVd t ht (hall t ⟨ht.1, ht.2.le⟩).1)
    (fun t ht => by
      have h := hsupply t ht (hall t ⟨ht.1, ht.2.le⟩).1 (hall t ⟨ht.1, ht.2.le⟩).2
      change 2 * inner ℝ (flat (ξ t)) (P (flat (F t))) + κ * V t ≤ β at h
      change 2 * inner ℝ (flat (ξ t)) (P (flat (F t))) ≤ -κ * V t + β
      linarith)
  intro t ht
  exact ⟨(hall t ht).1, (hall t ht).2, hdecay t ht⟩

end Dynacert.Lie
