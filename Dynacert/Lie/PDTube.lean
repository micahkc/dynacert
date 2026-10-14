import Dynacert.Lie.PDControl
import Dynacert.Lie.Kepler
import Dynacert.Linear.Supply
import Dynacert.Lie.Link

/-!
# Tube for a PD-controlled spacecraft tracking a circular orbit

A vehicle `X` under the body-frame PD law (`pdAccel`, `pdRate`) tracks a coasting reference `Y`
(`ā = 0`, `ω̄ = 0`) on a circular orbit, both in the inverse-square field `-μ p/‖p‖³`. From
rational certificate data alone (an `LTICert` for the 9-state closed-loop linear part, a
coercivity witness, an operator-norm witness, and a budget inequality), the log error stays in
`{ξᵀPξ ≤ ρ}` for all time, and so the physical errors satisfy `m‖Δp‖² ≤ ρ`, `m‖Δv‖² ≤ ρ`,
`m θ² ≤ ρ` (attitude angle `θ`).

Nothing about the trajectory is assumed beyond the model:

* the reference radius stays `r₀` (`circular_radius_ge`, from conservation of energy and angular
  momentum);
* the error stays in the principal chart and in the region `‖ξ‖ ≤ D` where the residual
  sectors hold (first exit, `log_error_tube`);
* the residuals are the PD residual (`pdResidual_le`) and the gravity mismatch
  (`gravity_residual_inverse_square`).
-/

noncomputable section

namespace Dynacert.Lie

open GNC Set Real Matrix Dynacert.Linear GNC.PolytopicTube

/-- The closed-loop linear part in flat coordinates `(p, v, R)`. -/
def pdMatrix (kp kd kR : ℚ) : Matrix (Fin 9) (Fin 9) ℚ := fun i j =>
  if i.val < 3 then (if j.val = i.val + 3 then 1 else 0)
  else if i.val < 6 then (if j.val + 3 = i.val then -kp else if j.val = i.val then -kd else 0)
  else (if j.val = i.val then -kR else 0)

/-- The disturbance enters the velocity block. -/
def velMatrix : Matrix (Fin 9) (Fin 3) ℚ := fun i j => if i.val = j.val + 3 then 1 else 0

/-- The PD loop as an `LTIModel` (9 states, 3 disturbance channels). -/
def pdModel (kp kd kR : ℚ) : LTIModel 9 3 := ⟨pdMatrix kp kd kR, velMatrix⟩

theorem flat_pdLin (kp kd kR : ℚ) (ξ : LogState) (d : Vec3) :
    flat (pdLin kp kd kR ξ + velocityOnly d) =
      clm (pdMatrix kp kd kR) (flat ξ) + clm velMatrix (WithLp.toLp 2 d) := by
  ext k
  fin_cases k <;>
    simp [pdLin, velocityOnly, flatFun, pdMatrix, velMatrix, toReal, mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

/-- The gravity sector gain on `‖ξ‖ ≤ D` for a reference at radius `≥ r`. -/
def gravGain (μ r D : ℝ) : ℝ := (1 / (1 - D ^ 2 / 16)) * (2 * μ / (r * (r - D) ^ 2))

theorem gravGain_nonneg {μ r D : ℝ} (hμ : 0 ≤ μ) (hD0 : 0 ≤ D) (hD2 : D ≤ 2) (hDr : D < r) :
    0 ≤ gravGain μ r D := by
  unfold gravGain
  have : 0 < 1 - D ^ 2 / 16 := by nlinarith
  have : 0 < r - D := by linarith
  have : 0 < r := by linarith
  positivity

theorem pdGain_nonneg {kp kd kR D δ : ℝ} (hkp : 0 ≤ kp) (hkd : 0 ≤ kd) (hkR : 0 ≤ kR)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) : 0 ≤ pdGain kp kd kR D δ := by
  unfold pdGain; positivity

theorem error_self (Y : SE23) : SE23.error Y Y = groupExp 0 := by
  rw [SE23.error, inv_mul_cancel]
  symm
  apply SE23.ext
  · simp [groupExp, rotationExp, skew_zero']
  · simp [groupExp, Jacobian.leftAt]
  · simp [groupExp, Jacobian.leftAt]

/-- **PD spacecraft tube.** See the module docstring. -/
theorem pd_spacecraft_tube {X Y : ℝ → SE23} {a w g abar wbar gbar d : ℝ → Vec3}
    {T μ r0 D δ ρ : ℝ} {kp kd kR m pn : ℚ}
    (C : LTICert (pdModel kp kd kR))
    (Wm : PSDWitness (C.P - m • 1)) (Wn : PSDWitness (pn ^ 2 • 1 - C.Pᵀ * C.P))
    (hm : 0 < m) (hpn : 0 ≤ pn) (hkp : 0 ≤ kp) (hkd : 0 ≤ kd) (hkR : 0 ≤ kR)
    (hX : SpacecraftSolution X a w g T) (hY : SpacecraftSolution Y abar wbar gbar T)
    (ha : ∀ t ∈ Ico 0 T, a t = pdAccel kp kd (SE23.error (Y t) (X t)) (d t))
    (hw : ∀ t ∈ Ico 0 T, w t = pdRate kR (SE23.error (Y t) (X t)))
    (habar : ∀ t ∈ Ico 0 T, abar t = 0) (hwbar : ∀ t ∈ Ico 0 T, wbar t = 0)
    (hd : ∀ t ∈ Ico 0 T, GNC.enorm (d t) ≤ δ)
    (hg : ∀ t ∈ Ico 0 T, g t = Gravity.field3 μ (X t).pos)
    (hgbar : ∀ t ∈ Ico 0 T, gbar t = Gravity.field3 μ (Y t).pos)
    (hμ : 0 < μ) (hr0 : 0 < r0) (hp0 : GNC.enorm (Y 0).pos = r0)
    (hv0 : GNC.enorm (Y 0).vel ^ 2 = μ / r0) (ho0 : (Y 0).pos ⬝ᵥ (Y 0).vel = 0)
    (h00 : X 0 = Y 0)
    (hD0 : 0 ≤ D) (hD2 : D ≤ 2) (hDr : D < r0) (hδ : 0 ≤ δ) (hρ0 : 0 ≤ ρ)
    (hregion : ρ ≤ m * D ^ 2)
    (hbudget : (C.γ : ℝ) * δ ^ 2 <
      (C.α - 2 * pn * (pdGain kp kd kR D δ + gravGain μ r0 D) / m) * ρ)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : (C.γ : ℝ) * δ ^ 2 ≤ (C.α - 2 * pn * (pdGain kp kd kR D δ + gravGain μ r0 D) / m) * c) :
    ∀ t ∈ Icc 0 T, SE23.error (Y t) (X t) ∈ PrincipalLog.domain ∧
      (m : ℝ) * GNC.enorm ((X t).pos - (Y t).pos) ^ 2 ≤ c ∧
      (m : ℝ) * GNC.enorm ((X t).vel - (Y t).vel) ^ 2 ≤ c ∧
      (m : ℝ) * GNC.enorm (principalError X Y t 2) ^ 2 ≤ c := by
  -- the reference stays on its circle
  have hrad := circular_radius_ge hY habar hgbar hμ hr0 hp0 hv0 ho0
  -- certificate facts in gnc's form
  set P := clm C.P with hPdef
  have hP : ∀ u v, inner ℝ u (P v) = inner ℝ v (P u) := clm_symm C.P_symm
  have hcoer : ∀ x, (m : ℝ) * ‖x‖ ^ 2 ≤ storage P x := coercive_of_witness Wm
  have hPn : ‖P‖ ≤ (pn : ℝ) := opNorm_le_of_witness hpn Wn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hvertex : ∀ (_ : Unit) y u, 2 * inner ℝ y (P (clm (pdMatrix kp kd kR) y +
      clm velMatrix u)) + (C.α : ℝ) * storage P y ≤ (C.γ : ℝ) * ‖u‖ ^ 2 :=
    fun _ y u => C.supply y u
  set ℓ : Fin 2 → ℝ := ![pdGain kp kd kR D δ, gravGain μ r0 D] with hℓdef
  have hℓ : ∀ k, 0 ≤ ℓ k := by
    intro k; fin_cases k
    · exact pdGain_nonneg (by exact_mod_cast hkp) (by exact_mod_cast hkd)
        (by exact_mod_cast hkR) hD0 hδ
    · exact gravGain_nonneg hμ.le hD0 hD2 hDr
  have hℓsum : ∑ k, ℓ k = pdGain kp kd kR D δ + gravGain μ r0 D := by
    simp [ℓ, Fin.sum_univ_two]
  have hγ0 : (0 : ℝ) ≤ C.γ := by exact_mod_cast C.hγ
  have hκ : 0 < (C.α : ℝ) - 2 * pn * (∑ k, ℓ k) / m := by
    rw [hℓsum]
    by_contra hc
    push Not at hc
    have : ((C.α : ℝ) - 2 * pn * (pdGain kp kd kR D δ + gravGain μ r0 D) / m) * ρ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc hρ0
    nlinarith [mul_nonneg hγ0 (sq_nonneg δ)]
  have hbudget' : (C.γ : ℝ) * δ ^ 2 < ((C.α : ℝ) - 2 * pn * (∑ k, ℓ k) / m) * ρ := by
    rwa [hℓsum]
  have hRc : D < π := by linarith [pi_gt_three]
  have hchart := chart_of_coercive P hm' hD0 hcoer hregion
  -- the error starts at the identity
  have he0 : SE23.error (Y 0) (X 0) = groupExp 0 := by rw [h00]; exact error_self _
  have h0π : GNC.enorm ((0 : LogState) 2) < π := by
    simp [enorm_zero']; exact pi_pos
  have hdom0 : SE23.error (Y 0) (X 0) ∈ PrincipalLog.domain := by
    rw [he0]; exact PrincipalLog.exp_mem_domain 0 h0π
  have hξ0 : principalError X Y 0 = 0 := by
    simp only [principalError]; rw [he0]; exact PrincipalLog.log_exp 0 h0π
  have hinit : storage P (flat (principalError X Y 0)) ≤ ρ := by
    rw [hξ0, map_zero]; simp [storage, hρ0]
  -- the residuals
  let gterm : ℝ → LogState := fun t => Jacobian.blockRightInverse (principalError X Y t)
    (adjoint (X t)⁻¹ (velocityOnly (g t - gbar t)))
  let r : ℝ → Fin 2 → EuclideanSpace ℝ (Fin 9) := fun t =>
    ![flat (pdResidual kp kd kR (principalError X Y t)
        (pdAccel kp kd (groupExp (principalError X Y t)) (d t))
        (pdRate kR (groupExp (principalError X Y t)))), flat (gterm t)]
  have hE : ∀ t, SE23.error (Y t) (X t) ∈ PrincipalLog.domain →
      SE23.error (Y t) (X t) = groupExp (principalError X Y t) :=
    fun t hdm => (PrincipalLog.log_spec hdm).2.symm
  have hdecomp : ∀ t ∈ Ico 0 T, SE23.error (Y t) (X t) ∈ PrincipalLog.domain →
      storage P (flat (principalError X Y t)) ≤ ρ →
      flat (logErrorField X Y (a t) (w t) (abar t) (wbar t) (g t) (gbar t) t) =
        (∑ _i : Unit, (1 : ℝ) • clm (pdMatrix kp kd kR) (flat (principalError X Y t))) +
          clm velMatrix (WithLp.toLp 2 (d t)) + ∑ k, r t k := by
    intro t ht hdm _
    have hfield := pd_field kp kd kR (principalError X Y t) (d t)
    rw [ha t ht, hw t ht, habar t ht, hwbar t ht, hE t hdm]
    simp only [logErrorField]
    rw [hfield]
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, Fin.sum_univ_two, r, gterm,
      map_add, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← flat_pdLin]
    simp only [map_add]
    abel
  have hres : ∀ t ∈ Ico 0 T, SE23.error (Y t) (X t) ∈ PrincipalLog.domain →
      storage P (flat (principalError X Y t)) ≤ ρ →
      ∀ k, ‖r t k‖ ≤ ℓ k * ‖flat (principalError X Y t)‖ := by
    intro t ht hdm hst k
    have hN : ‖flat (principalError X Y t)‖ ≤ D :=
      GNC.PolytopicResidualTube.sublevel_norm P _ hm' hD0 (hcoer _) hst hregion
    fin_cases k
    · exact pdResidual_le (by exact_mod_cast hkp) (by exact_mod_cast hkd)
        (by exact_mod_cast hkR) hD2 _ (d t) hN (hd t ht)
    · show ‖flat (gterm t)‖ ≤ gravGain μ r0 D * ‖flat (principalError X Y t)‖
      simp only [gterm]
      rw [hg t ht, hgbar t ht]
      have hθ := (enorm_component_le_flat (principalError X Y t) 2).trans hN
      exact gravity_residual_inverse_square μ hμ.le (Y t) (X t) hdm hD0 hD2 hDr
        (hrad t ⟨ht.1, ht.2.le⟩) hN hθ
  have htube := log_tube_of_residuals P hP (fun _ : Unit => clm (pdMatrix kp kd kR))
    (clm velMatrix) (fun _ _ => (1 : ℝ)) (fun t => WithLp.toLp 2 (d t)) ℓ r hX hY hm' hcoer hℓ
    hPn hvertex hκ hbudget' hγ0 hRc hchart hdom0 hinit (fun _ _ _ => zero_le_one)
    (fun _ _ => by simp) (fun t ht => hd t ht) hdecomp hres
  intro t ht
  obtain ⟨hdm, -, hdec⟩ := htube t ht
  -- the decay bound: V ≤ max(V(0), γδ²/κ) = γδ²/κ ≤ c, since V(0) = 0
  have hV0 : storage P (flat (principalError X Y 0)) = 0 := by
    rw [hξ0, map_zero]; simp [storage]
  have hβκ : (C.γ : ℝ) * δ ^ 2 / ((C.α : ℝ) - 2 * pn * (∑ k, ℓ k) / m) ≤ c := by
    rw [div_le_iff₀ hκ, hℓsum]; linarith [hc]
  have hst : storage P (flat (principalError X Y t)) ≤ c := by
    rw [hV0] at hdec
    exact hdec.trans (max_le hc0 hβκ)
  obtain ⟨hp, hv, hR, -⟩ := physical_output_bounds P hm' hcoer hdm hst
  exact ⟨hdm, hp, hv, hR⟩

/-! ## The same theorem in the shape rumoca's `lean-dae` target emits -/

local notation "M3" => Matrix (Fin 3) (Fin 3) ℝ

theorem rot_inv_val (R : SO3) : ((R⁻¹ : SO3) : M3) = (R : M3)ᵀ := by
  ext i j; rfl

theorem rotate_inv (R : SO3) (v : Vec3) : rotate R⁻¹ v = (R : M3)ᵀ *ᵥ v := by
  rw [rotate, rot_inv_val]

/-- The group error of two `ofScalars` trajectories, componentwise. -/
theorem ofScalars_error {p v pb vb : ℝ → Vec3} {R Rb : ℝ → M3} {t : ℝ}
    (hR : R t ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hRb : Rb t ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    (SE23.error (ofScalars pb vb Rb t) (ofScalars p v R t)).pos = (Rb t)ᵀ *ᵥ (p t - pb t) ∧
    (SE23.error (ofScalars pb vb Rb t) (ofScalars p v R t)).vel = (Rb t)ᵀ *ᵥ (v t - vb t) ∧
    ((SE23.error (ofScalars pb vb Rb t) (ofScalars p v R t)).rot : M3) = (Rb t)ᵀ * R t := by
  have hX := ofScalars_rot (p := p) (v := v) hR
  have hY := ofScalars_rot (p := pb) (v := vb) hRb
  refine ⟨?_, ?_, ?_⟩
  · rw [SE23.error_pos, rotate_inv, hY]; rfl
  · rw [SE23.error_vel, rotate_inv, hY]; rfl
  · simp only [SE23.error, SE23.mul_rot, SE23.inv_rot]
    rw [Submonoid.coe_mul, rot_inv_val, hX, hY]

theorem rotation_of_components {R dR : ℝ → M3} {w : ℝ → Vec3} {T : ℝ}
    (hRc : ∀ i j, ContinuousOn (fun s => R s i j) (Icc 0 T))
    (hRd : ∀ t ∈ Ico 0 T, ∀ i j, HasDerivWithinAt (fun s => R s i j) (dR t i j) (Ici t) t)
    (hR : ∀ t ∈ Ico 0 T, dR t = R t * Rumoca.skew (w t))
    (hR0 : R 0 ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∀ t ∈ Icc 0 T, R t ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  rotation_mem_SO3 (continuousOn_mat hRc)
    (fun t ht => by rw [← rumoca_skew_eq, ← hR t ht]; exact hasDerivWithinAt_mat (hRd t ht)) hR0

/-- rumoca's `sqrt(v*v)` is the Euclidean norm. -/
theorem sqrt_dot_self (v : Vec3) : Real.sqrt (v ⬝ᵥ v) = GNC.enorm v := by
  rw [← Real.sqrt_sq (GNC.enorm_nonneg v), enorm_sq]
  simp [dotProduct, Fin.sum_univ_three, lengthSq, sq]

/-- A componentwise peak bound gives a Euclidean bound. -/
theorem enorm_le_of_abs_le {v : Vec3} {b δ : ℝ} (h : ∀ i, |v i| ≤ b) (hδ : 3 * b ^ 2 ≤ δ ^ 2)
    (hδ0 : 0 ≤ δ) : GNC.enorm v ≤ δ := by
  rw [← sqrt_dot_self]
  apply Real.sqrt_le_iff.mpr
  refine ⟨hδ0, ?_⟩
  have h0 := sq_le_sq' (abs_le.mp (h 0)).1 (abs_le.mp (h 0)).2
  have h1 := sq_le_sq' (abs_le.mp (h 1)).1 (abs_le.mp (h 1)).2
  have h2 := sq_le_sq' (abs_le.mp (h 2)).1 (abs_le.mp (h 2)).2
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith

/-- From `m e² ≤ c` and `c ≤ m b²` to `e ≤ b`. -/
theorem le_of_sq_bound {m e c b : ℝ} (hm : 0 < m) (he : 0 ≤ e) (hb : 0 ≤ b)
    (h : m * e ^ 2 ≤ c) (hc : c ≤ m * b ^ 2) : e ≤ b := by
  have : e ^ 2 ≤ b ^ 2 := le_of_mul_le_mul_left (h.trans hc) hm
  exact pow_le_pow_iff_left₀ he hb two_ne_zero |>.mp this

/-- **PD spacecraft tube, rumoca form.** The hypotheses are the shapes rumoca's `lean-dae`
target writes for a vehicle `(p, v, R)` and a coasting reference `(pb, vb, Rb)` in
inverse-square gravity, with body-frame errors `ep`, `ev`, `eR` and the PD law. -/
theorem pd_spacecraft_components {p v pb vb dp dv dpb dvb a w ab wb d ep ev eR : ℝ → Vec3}
    {R Rb dR dRb : ℝ → M3} {T μ μb r0 D δ ρ c : ℝ} {kp kd kR m pn : ℚ}
    (C : LTICert (pdModel kp kd kR))
    (Wm : PSDWitness (C.P - m • 1)) (Wn : PSDWitness (pn ^ 2 • 1 - C.Pᵀ * C.P))
    (hm : 0 < m) (hpn : 0 ≤ pn) (hkp : 0 ≤ kp) (hkd : 0 ≤ kd) (hkR : 0 ≤ kR)
    -- continuity and right derivatives (rumoca's `IsSolutionOn`)
    (hpc : ∀ i, ContinuousOn (fun s => p s i) (Icc 0 T))
    (hvc : ∀ i, ContinuousOn (fun s => v s i) (Icc 0 T))
    (hRc : ∀ i j, ContinuousOn (fun s => R s i j) (Icc 0 T))
    (hpbc : ∀ i, ContinuousOn (fun s => pb s i) (Icc 0 T))
    (hvbc : ∀ i, ContinuousOn (fun s => vb s i) (Icc 0 T))
    (hRbc : ∀ i j, ContinuousOn (fun s => Rb s i j) (Icc 0 T))
    (hpd : ∀ t ∈ Ico 0 T, ∀ i, HasDerivWithinAt (fun s => p s i) (dp t i) (Ici t) t)
    (hvd : ∀ t ∈ Ico 0 T, ∀ i, HasDerivWithinAt (fun s => v s i) (dv t i) (Ici t) t)
    (hRd : ∀ t ∈ Ico 0 T, ∀ i j, HasDerivWithinAt (fun s => R s i j) (dR t i j) (Ici t) t)
    (hpbd : ∀ t ∈ Ico 0 T, ∀ i, HasDerivWithinAt (fun s => pb s i) (dpb t i) (Ici t) t)
    (hvbd : ∀ t ∈ Ico 0 T, ∀ i, HasDerivWithinAt (fun s => vb s i) (dvb t i) (Ici t) t)
    (hRbd : ∀ t ∈ Ico 0 T, ∀ i j, HasDerivWithinAt (fun s => Rb s i j) (dRb t i j) (Ici t) t)
    -- the model's equations
    (ep_ : ∀ t ∈ Ico 0 T, dp t = v t)
    (ev_ : ∀ t ∈ Ico 0 T, dv t = R t *ᵥ a t - ((p t ⬝ᵥ p t) ^ (1.5 : ℝ))⁻¹ • μ • p t)
    (eR_ : ∀ t ∈ Ico 0 T, dR t = R t * Rumoca.skew (w t))
    (epb_ : ∀ t ∈ Ico 0 T, dpb t = vb t)
    (evb_ : ∀ t ∈ Ico 0 T, dvb t = Rb t *ᵥ ab t - ((pb t ⬝ᵥ pb t) ^ (1.5 : ℝ))⁻¹ • μb • pb t)
    (eRb_ : ∀ t ∈ Ico 0 T, dRb t = Rb t * Rumoca.skew (wb t))
    (hep : ∀ t ∈ Ico 0 T, ep t = (Rb t)ᵀ *ᵥ (p t - pb t))
    (hev : ∀ t ∈ Ico 0 T, ev t = (Rb t)ᵀ *ᵥ (v t - vb t))
    (heR : ∀ t ∈ Ico 0 T, eR t = attErr ((Rb t)ᵀ * R t))
    (ha : ∀ t ∈ Ico 0 T, a t = -((kp : ℝ) • ep t) - (kd : ℝ) • ev t + d t)
    (hw : ∀ t ∈ Ico 0 T, w t = -((kR : ℝ) • eR t))
    (hab : ∀ t ∈ Ico 0 T, ab t = 0) (hwb : ∀ t ∈ Ico 0 T, wb t = 0)
    (hd : ∀ t ∈ Ico 0 T, GNC.enorm (d t) ≤ δ)
    -- parameters and initial state
    (hμ : 0 < μ) (hμb : μb = μ) (hr0 : 0 < r0)
    (hp0 : p 0 = pb 0) (hv0 : v 0 = vb 0) (hR0 : R 0 = 1) (hRb0 : Rb 0 = 1)
    (hpb0 : GNC.enorm (pb 0) = r0) (hvb0 : GNC.enorm (vb 0) ^ 2 = μ / r0)
    (hob0 : pb 0 ⬝ᵥ vb 0 = 0)
    -- certificate numbers
    (hD0 : 0 ≤ D) (hD2 : D ≤ 2) (hDr : D < r0) (hδ : 0 ≤ δ) (hρ0 : 0 ≤ ρ)
    (hregion : ρ ≤ m * D ^ 2)
    (hbudget : (C.γ : ℝ) * δ ^ 2 <
      (C.α - 2 * pn * (pdGain kp kd kR D δ + gravGain μ r0 D) / m) * ρ)
    (hc0 : 0 ≤ c)
    (hc : (C.γ : ℝ) * δ ^ 2 ≤ (C.α - 2 * pn * (pdGain kp kd kR D δ + gravGain μ r0 D) / m) * c) :
    (∀ t ∈ Icc 0 T, (m : ℝ) * GNC.enorm (p t - pb t) ^ 2 ≤ c ∧
      (m : ℝ) * GNC.enorm (v t - vb t) ^ 2 ≤ c) ∧
    (∀ t ∈ Ico 0 T, (m : ℝ) * GNC.enorm (eR t) ^ 2 ≤ c) := by
  have hSO : (1 : M3) ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := Submonoid.one_mem _
  have hRs := rotation_of_components hRc hRd eR_ (hR0 ▸ hSO)
  have hRbs := rotation_of_components hRbc hRbd eRb_ (hRb0 ▸ hSO)
  set g : ℝ → Vec3 := fun t => -(((p t ⬝ᵥ p t) ^ (1.5 : ℝ))⁻¹ • μ • p t)
  set gb : ℝ → Vec3 := fun t => -(((pb t ⬝ᵥ pb t) ^ (1.5 : ℝ))⁻¹ • μb • pb t)
  have hX := spacecraft_of_components (a := a) (g := g) hpc hvc hRc hpd hvd hRd ep_
    (fun t ht => (ev_ t ht).trans (sub_eq_add_neg _ _)) eR_ (hR0 ▸ hSO)
  have hY := spacecraft_of_components (a := ab) (g := gb) hpbc hvbc hRbc hpbd hvbd hRbd epb_
    (fun t ht => (evb_ t ht).trans (sub_eq_add_neg _ _)) eRb_ (hRb0 ▸ hSO)
  set X := ofScalars p v R
  set Y := ofScalars pb vb Rb
  have herr : ∀ t ∈ Ico 0 T, (SE23.error (Y t) (X t)).pos = (Rb t)ᵀ *ᵥ (p t - pb t) ∧
      (SE23.error (Y t) (X t)).vel = (Rb t)ᵀ *ᵥ (v t - vb t) ∧
      ((SE23.error (Y t) (X t)).rot : M3) = (Rb t)ᵀ * R t := fun t ht =>
    ofScalars_error (hRs t ⟨ht.1, ht.2.le⟩) (hRbs t ⟨ht.1, ht.2.le⟩)
  have hXpos : ∀ t, (X t).pos = p t := fun t => rfl
  have hYpos : ∀ t, (Y t).pos = pb t := fun t => rfl
  have hXvel : ∀ t, (X t).vel = v t := fun t => rfl
  have hYvel : ∀ t, (Y t).vel = vb t := fun t => rfl
  have h00 : X 0 = Y 0 := by
    apply SE23.ext
    · apply Subtype.ext
      rw [ofScalars_rot (p := p) (v := v) (t := 0) (hR0 ▸ hSO),
        ofScalars_rot (p := pb) (v := vb) (t := 0) (hRb0 ▸ hSO), hR0, hRb0]
    · exact hv0
    · exact hp0
  have htube := pd_spacecraft_tube C Wm Wn hm hpn hkp hkd hkR hX hY
    (d := d) (μ := μ) (r0 := r0)
    (fun t ht => by
      obtain ⟨h1, h2, -⟩ := herr t ht
      rw [ha t ht, hep t ht, hev t ht, pdAccel, h1, h2, neg_smul])
    (fun t ht => by
      obtain ⟨-, -, h3⟩ := herr t ht
      rw [hw t ht, heR t ht, pdRate, h3, neg_smul])
    hab hwb hd
    (fun t _ => rumoca_inverse_square μ (p t))
    (fun t _ => by simp only [gb, hμb]; exact rumoca_inverse_square μ (pb t))
    hμ hr0 hpb0 hvb0 hob0 h00 hD0 hD2 hDr hδ hρ0 hregion hbudget hc0 hc
  refine ⟨fun t ht => ⟨(htube t ht).2.1, (htube t ht).2.2.1⟩, fun t ht => ?_⟩
  obtain ⟨hdm, -, -, hθ⟩ := htube t ⟨ht.1, ht.2.le⟩
  obtain ⟨-, -, h3⟩ := herr t ht
  have hE := (PrincipalLog.log_spec hdm).2
  have hrot : (Rb t)ᵀ * R t = (rotationExp (principalError X Y t 2) : M3) := by
    rw [← h3]
    have h := congrArg (fun E : SE23 => (E.rot : M3)) hE
    simp only [groupExp] at h
    exact h.symm
  rw [heR t ht, hrot]
  have hle := enorm_attErr_le (principalError X Y t 2)
  have hm' : (0 : ℝ) ≤ m := by exact_mod_cast hm.le
  calc (m : ℝ) * GNC.enorm (attErr (rotationExp (principalError X Y t 2)).val) ^ 2
      ≤ (m : ℝ) * GNC.enorm (principalError X Y t 2) ^ 2 := by
        have := GNC.enorm_nonneg (attErr (rotationExp (principalError X Y t 2)).val)
        gcongr
    _ ≤ c := hθ

end Dynacert.Lie
