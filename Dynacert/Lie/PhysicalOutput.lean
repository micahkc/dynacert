import Dynacert.Lie.LogTube
import Dynacert.Lie.SO3
import GNC.Dynamics.LieErrorReconstruction

/-!
# Physical outputs from the SE₂(3) log error, and nine-scalar trajectories

* Position and velocity: with `E = Y⁻¹X = Exp ξ`, `E.pos = R_Yᵀ (p_X - p_Y) = J_l(ξ_R) ξ_p`.
  Rotations preserve length and the left Jacobian is nonexpansive (gnc's
  `leftAt_nonexpansive`), so `‖p_X - p_Y‖ ≤ ‖ξ_p‖`, and likewise `‖v_X - v_Y‖ ≤ ‖ξ_v‖`.
* Attitude: `trace (R_Yᵀ R_X) = 1 + 2 cos ‖ξ_R‖`, and `‖ξ_R‖` is the rotation angle
  `arccos ((trace (R_Yᵀ R_X) - 1) / 2)`.
* A nine-scalar attitude state from a Modelica model is packaged as an `SE23` trajectory
  (`ofScalars`), and its `SpacecraftSolution` property follows from SO(3) invariance.
-/

noncomputable section

namespace Dynacert.Lie

open GNC Matrix Set Filter Real GNC.PolytopicTube
open scoped Matrix Matrix.Norms.Operator Topology

/-! ## Pointwise reconstruction bounds -/

theorem error_pos_enorm (y x : SE23) :
    GNC.enorm (SE23.error y x).pos = GNC.enorm (x.pos - y.pos) := by
  rw [SE23.error_pos, rotate_enorm]

theorem error_vel_enorm (y x : SE23) :
    GNC.enorm (SE23.error y x).vel = GNC.enorm (x.vel - y.vel) := by
  rw [SE23.error_vel, rotate_enorm]

/-- Position error is bounded by the position log coordinate. -/
theorem position_error_le_log {y x : SE23} (hd : SE23.error y x ∈ PrincipalLog.domain) :
    GNC.enorm (x.pos - y.pos) ≤ GNC.enorm (PrincipalLog.log (SE23.error y x) 0) := by
  obtain ⟨hπ, he⟩ := PrincipalLog.log_spec hd
  generalize PrincipalLog.log (SE23.error y x) = ξ at hπ he ⊢
  rw [← error_pos_enorm, ← he]
  exact leftAt_nonexpansive _ _ (by linarith [pi_pos])

/-- Velocity error is bounded by the velocity log coordinate. -/
theorem velocity_error_le_log {y x : SE23} (hd : SE23.error y x ∈ PrincipalLog.domain) :
    GNC.enorm (x.vel - y.vel) ≤ GNC.enorm (PrincipalLog.log (SE23.error y x) 1) := by
  obtain ⟨hπ, he⟩ := PrincipalLog.log_spec hd
  generalize PrincipalLog.log (SE23.error y x) = ξ at hπ he ⊢
  rw [← error_vel_enorm, ← he]
  exact leftAt_nonexpansive _ _ (by linarith [pi_pos])

/-- Attitude: the relative rotation `R_Yᵀ R_X` has trace `1 + 2 cos ‖ξ_R‖`. -/
theorem attitude_error_trace {y x : SE23} (hd : SE23.error y x ∈ PrincipalLog.domain) :
    ((y.rot⁻¹ * x.rot : SO3) : Matrix (Fin 3) (Fin 3) ℝ).trace =
      1 + 2 * cos (GNC.enorm (PrincipalLog.log (SE23.error y x) 2)) := by
  obtain ⟨_, he⟩ := PrincipalLog.log_spec hd
  generalize PrincipalLog.log (SE23.error y x) = ξ at he ⊢
  have hrot : (SE23.error y x).rot = y.rot⁻¹ * x.rot := rfl
  rw [← hrot, ← rotationExp_trace, ← he]
  rfl

/-- Attitude: `‖ξ_R‖` is the rotation angle of `R_Yᵀ R_X`. -/
theorem attitude_error_angle {y x : SE23} (hd : SE23.error y x ∈ PrincipalLog.domain) :
    GNC.enorm (PrincipalLog.log (SE23.error y x) 2) =
      arccos ((((y.rot⁻¹ * x.rot : SO3) : Matrix (Fin 3) (Fin 3) ℝ).trace - 1) / 2) := by
  rw [attitude_error_trace hd]
  have hπ := (PrincipalLog.log_spec hd).1
  rw [show (1 + 2 * cos (GNC.enorm (PrincipalLog.log (SE23.error y x) 2)) - 1) / 2 =
      cos (GNC.enorm (PrincipalLog.log (SE23.error y x) 2)) by ring]
  exact (arccos_cos (GNC.enorm_nonneg _) hπ.le).symm

/-- Each `Vec3` block of a log state is bounded by the flattened Euclidean norm. -/
theorem enorm_component_le_flat (ξ : LogState) (i : Fin 3) : GNC.enorm (ξ i) ≤ ‖flat ξ‖ := by
  have h := flat_norm_sq ξ
  have hi := GNC.enorm_nonneg (ξ i)
  have hn := norm_nonneg (flat ξ)
  have h0 := sq_nonneg (GNC.enorm (ξ 0))
  have h1 := sq_nonneg (GNC.enorm (ξ 1))
  have h2 := sq_nonneg (GNC.enorm (ξ 2))
  have hsq : GNC.enorm (ξ i) ^ 2 ≤ ‖flat ξ‖ ^ 2 := by
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith
  by_contra hc
  push Not at hc
  nlinarith [mul_lt_mul'' hc hc hn hn]

/-- **Physical output bounds from the tube.** Under a coercivity witness
`m‖x‖² ≤ storage P x`, a storage level `c` for the log error gives
`m ‖Δp‖² ≤ c`, `m ‖Δv‖² ≤ c`, and the attitude angle `‖ξ_R‖` with
`m ‖ξ_R‖² ≤ c` and `trace (R_Yᵀ R_X) = 1 + 2 cos ‖ξ_R‖`. -/
theorem physical_output_bounds (P : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9))
    {m c : ℝ} (hm : 0 < m) (hcoer : ∀ x, m * ‖x‖ ^ 2 ≤ storage P x)
    {y x : SE23} (hd : SE23.error y x ∈ PrincipalLog.domain)
    (hc : storage P (flat (PrincipalLog.log (SE23.error y x))) ≤ c) :
    m * GNC.enorm (x.pos - y.pos) ^ 2 ≤ c ∧
    m * GNC.enorm (x.vel - y.vel) ^ 2 ≤ c ∧
    m * GNC.enorm (PrincipalLog.log (SE23.error y x) 2) ^ 2 ≤ c ∧
    ((y.rot⁻¹ * x.rot : SO3) : Matrix (Fin 3) (Fin 3) ℝ).trace =
      1 + 2 * cos (GNC.enorm (PrincipalLog.log (SE23.error y x) 2)) := by
  set ξ := PrincipalLog.log (SE23.error y x)
  have hflat : m * ‖flat ξ‖ ^ 2 ≤ c := (hcoer _).trans hc
  have key : ∀ r : ℝ, 0 ≤ r → r ≤ ‖flat ξ‖ → m * r ^ 2 ≤ c := fun r hr hle =>
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hle 2) hm.le).trans hflat
  refine ⟨?_, ?_, ?_, attitude_error_trace hd⟩
  · exact key _ (GNC.enorm_nonneg _)
      ((position_error_le_log hd).trans (enorm_component_le_flat ξ 0))
  · exact key _ (GNC.enorm_nonneg _)
      ((velocity_error_le_log hd).trans (enorm_component_le_flat ξ 1))
  · exact key _ (GNC.enorm_nonneg _) (enorm_component_le_flat ξ 2)

/-! ## Nine-scalar trajectories -/

open scoped Classical in
/-- Package scalar position, velocity, and nine-scalar attitude as an `SE23` trajectory.
Off `SO(3)` (which never happens on `[0, T]` by `rotation_mem_SO3`) the attitude defaults
to the identity. -/
def ofScalars (p v : ℝ → Vec3) (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) : SE23 :=
  ⟨if h : R t ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ then ⟨R t, h⟩ else 1, v t, p t⟩

theorem ofScalars_rot {p v : ℝ → Vec3} {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (h : R t ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) : (ofScalars p v R t).rot.val = R t := by
  rw [ofScalars]
  simp only [dif_pos h]

/-- A nine-scalar model with `ṗ = v`, `v̇ = R a + g`, `Ṙ = R skew ω` (right derivatives,
continuous on `[0, T]`, `R 0 ∈ SO(3)`) is a `SpacecraftSolution` on `[0, T]`. -/
theorem ofScalars_solution {p v : ℝ → Vec3} {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {a w g : ℝ → Vec3} {T : ℝ}
    (hpc : ContinuousOn p (Icc 0 T)) (hvc : ContinuousOn v (Icc 0 T))
    (hRc : ContinuousOn R (Icc 0 T))
    (hpd : ∀ t ∈ Ico 0 T, HasDerivWithinAt p (v t) (Ici t) t)
    (hvd : ∀ t ∈ Ico 0 T, HasDerivWithinAt v (R t *ᵥ a t + g t) (Ici t) t)
    (hRd : ∀ t ∈ Ico 0 T, HasDerivWithinAt R (R t * skew (w t)) (Ici t) t)
    (hR0 : R 0 ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    SpacecraftSolution (ofScalars p v R) a w g T := by
  have hSO := rotation_mem_SO3 hRc hRd hR0
  have hrot : EqOn (fun s => (ofScalars p v R s).rot.val) R (Icc 0 T) :=
    fun s hs => ofScalars_rot (hSO s hs)
  refine ⟨hpc, hvc, hRc.congr hrot, ?_⟩
  intro t ht
  have htI : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
  have hnhds : Icc 0 T ∈ 𝓝[Ici t] t :=
    Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  have hrt : (ofScalars p v R t).rot.val = R t := hrot htI
  refine ⟨?_, ?_, ?_⟩
  · exact hpd t ht
  · have h := hvd t ht
    change HasDerivWithinAt v (rotate (ofScalars p v R t).rot (a t) + g t) (Ici t) t
    simpa only [rotate, hrt] using h
  · have h := hRd t ht
    rw [hrt]
    exact h.congr_of_eventuallyEq (Filter.mem_of_superset hnhds fun s hs => hrot hs) (hrot htI)

end Dynacert.Lie
