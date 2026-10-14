import Dynacert.Lie.LogTube
import Dynacert.Compose.AssumeGuarantee
import GNC.Dynamics.GravityLinearization

/-!
# A coasting circular Kepler orbit keeps its radius

A reference spacecraft on gnc's SE₂(3) trajectory type that coasts (zero thrust) in the
inverse-square field `Gravity.field3 μ` and starts on a circular orbit (`‖p₀‖ = r₀`,
`‖v₀‖² = μ/r₀`, `p₀ ⬝ v₀ = 0`) keeps `‖p(t)‖ = r₀` on the whole horizon. The proof uses the
conserved quantities `‖p‖²‖v‖² − (p⬝v)² = ‖p × v‖²` and `‖v‖²/2 − μ/‖p‖`; the singularity at
`p = 0` is excluded by a first-exit argument (`Dynacert.Compose.assume_guarantee`).
-/

noncomputable section

namespace Dynacert.Lie

open GNC Set Real Filter Topology

theorem kepler_field3_apply (μ : ℝ) (q : Vec3) (i : Fin 3) :
    Gravity.field3 μ q i = -μ / GNC.enorm q ^ 3 * q i := by
  simp [Gravity.field3, Gravity.field, GNC.enorm]

theorem kepler_field3_eq (μ : ℝ) (q : Vec3) :
    Gravity.field3 μ q = (-μ / GNC.enorm q ^ 3) • q := by
  funext i; rw [kepler_field3_apply]; rfl

theorem kepler_enorm_eq_sqrt (v : Vec3) : GNC.enorm v = √(v ⬝ᵥ v) := by
  rw [dot_self_lengthSq, ← enorm_sq, Real.sqrt_sq (enorm_nonneg v)]

theorem kepler_dot_self_nonneg (v : Vec3) : 0 ≤ v ⬝ᵥ v := by
  rw [dot_self_lengthSq]; exact lengthSq_nonneg v

theorem kepler_enorm_sq_dot (v : Vec3) : GNC.enorm v ^ 2 = v ⬝ᵥ v := by
  rw [dot_self_lengthSq, enorm_sq]

/-- Product rule for the dot product of two curves in `ℝ³`. -/
theorem kepler_dot_hasDerivWithinAt {f g : ℝ → Vec3} {f' g' : Vec3} {S : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' S t) (hg : HasDerivWithinAt g g' S t) :
    HasDerivWithinAt (fun s => f s ⬝ᵥ g s) (f' ⬝ᵥ g t + f t ⬝ᵥ g') S t := by
  have hf' := hasDerivWithinAt_pi.1 hf
  have hg' := hasDerivWithinAt_pi.1 hg
  simp only [dotProduct, Fin.sum_univ_three]
  convert ((((hf' 0).mul (hg' 0)).add ((hf' 1).mul (hg' 1))).add ((hf' 2).mul (hg' 2)))
    using 1
  ring

theorem kepler_dot_continuousOn {f g : ℝ → Vec3} {S : Set ℝ}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
    ContinuousOn (fun s => f s ⬝ᵥ g s) S := by
  have hf' := continuousOn_pi.1 hf
  have hg' := continuousOn_pi.1 hg
  simp only [dotProduct, Fin.sum_univ_three]
  exact (((hf' 0).mul (hg' 0)).add ((hf' 1).mul (hg' 1))).add ((hf' 2).mul (hg' 2))

/-- **Circular Kepler orbits keep their radius.** A coasting spacecraft in inverse-square
gravity started on a circular orbit of radius `r0` stays at radius `r0`. -/
theorem circular_radius_const {Y : ℝ → SE23} {abar wbar gbar : ℝ → Vec3} {T μ r0 : ℝ}
    (hY : SpacecraftSolution Y abar wbar gbar T)
    (ha : ∀ t ∈ Ico 0 T, abar t = 0)
    (hg : ∀ t ∈ Ico 0 T, gbar t = Gravity.field3 μ (Y t).pos)
    (hμ : 0 < μ) (hr0 : 0 < r0)
    (hp0 : GNC.enorm (Y 0).pos = r0) (hv0 : GNC.enorm (Y 0).vel ^ 2 = μ / r0)
    (ho0 : (Y 0).pos ⬝ᵥ (Y 0).vel = 0) :
    ∀ t ∈ Icc 0 T, GNC.enorm (Y t).pos = r0 := by
  set p : ℝ → Vec3 := fun s => (Y s).pos with hp
  set v : ℝ → Vec3 := fun s => (Y s).vel with hv
  have hpc : ContinuousOn p (Icc 0 T) := hY.pos_cont
  have hvc : ContinuousOn v (Icc 0 T) := hY.vel_cont
  -- the accelerations, as scalar multiples of the position
  set c : ℝ → ℝ := fun s => -μ / GNC.enorm (p s) ^ 3 with hc
  have hpd : ∀ t ∈ Ico 0 T, HasDerivWithinAt p (v t) (Ici t) t := fun t ht => (hY.ode t ht).1
  have hvd : ∀ t ∈ Ico 0 T, HasDerivWithinAt v (c t • p t) (Ici t) t := by
    intro t ht
    have h := (hY.ode t ht).2.1
    rw [ha t ht, hg t ht, rotate_zero, zero_add, kepler_field3_eq] at h
    exact h
  -- conserved quantities
  set H : ℝ → ℝ := fun s => (p s ⬝ᵥ p s) * (v s ⬝ᵥ v s) - (p s ⬝ᵥ v s) ^ 2 with hH
  set E : ℝ → ℝ := fun s => (v s ⬝ᵥ v s) / 2 - μ / √(p s ⬝ᵥ p s) with hE
  have hHd : ∀ t ∈ Ico 0 T, HasDerivWithinAt H 0 (Ici t) t := by
    intro t ht
    have hL := kepler_dot_hasDerivWithinAt (hpd t ht) (hpd t ht)
    have hV := kepler_dot_hasDerivWithinAt (hvd t ht) (hvd t ht)
    have hD := kepler_dot_hasDerivWithinAt (hpd t ht) (hvd t ht)
    convert (hL.mul hV).sub (hD.pow 2) using 1
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm (v t) (p t)]
    push_cast
    ring
  have hEd : ∀ t ∈ Ico 0 T, (p t ⬝ᵥ p t) ≠ 0 → HasDerivWithinAt E 0 (Ici t) t := by
    intro t ht hne
    have hL := kepler_dot_hasDerivWithinAt (hpd t ht) (hpd t ht)
    have hV := kepler_dot_hasDerivWithinAt (hvd t ht) (hvd t ht)
    have hr := hL.sqrt hne
    have hrpos : 0 < √(p t ⬝ᵥ p t) := by
      rw [Real.sqrt_pos]; exact lt_of_le_of_ne (kepler_dot_self_nonneg _) (Ne.symm hne)
    have hq := (hasDerivWithinAt_const t (Ici t) μ).div hr hrpos.ne'
    convert (hV.div_const 2).sub hq using 1
    have hct : c t = -μ / √(p t ⬝ᵥ p t) ^ 3 := by
      simp only [hc, kepler_enorm_eq_sqrt]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm (v t) (p t), hct]
    have hsq : √(p t ⬝ᵥ p t) ^ 2 = p t ⬝ᵥ p t := Real.sq_sqrt (kepler_dot_self_nonneg _)
    field_simp
    ring
  -- initial values
  have hpp0 : p 0 ⬝ᵥ p 0 = r0 ^ 2 := by rw [← kepler_enorm_sq_dot, hp, hp0]
  have hvv0 : v 0 ⬝ᵥ v 0 = μ / r0 := by rw [← kepler_enorm_sq_dot, hv, hv0]
  have hH0 : H 0 = μ * r0 := by
    simp only [hH, hpp0, hvv0, show p 0 ⬝ᵥ v 0 = 0 from ho0]
    field_simp
    ring
  have hE0 : E 0 = -μ / (2 * r0) := by
    simp only [hE, hpp0, hvv0, Real.sqrt_sq hr0.le]
    field_simp
    ring
  -- first exit on the radial deviation
  set s : Unit → ℝ → ℝ := fun _ t => |GNC.enorm (p t) - r0| with hs
  have hncont : ContinuousOn (fun t => GNC.enorm (p t)) (Icc 0 T) := by
    have : (fun t => GNC.enorm (p t)) = fun t => √(p t ⬝ᵥ p t) := by
      funext t; exact kepler_enorm_eq_sqrt _
    rw [this]
    exact (kepler_dot_continuousOn hpc hpc).sqrt
  have hscont : ∀ i, ContinuousOn (s i) (Icc 0 T) := fun _ =>
    (hncont.sub continuousOn_const).abs
  have key := Dynacert.Compose.assume_guarantee (s := s) (b := fun _ => r0 / 2)
    (c := fun _ => 0) hscont (fun _ => by simp only; linarith) ?_
  · intro t ht
    have h := key () t ht
    simp only [hs] at h
    have := abs_nonneg (GNC.enorm (p t) - r0)
    have h0 : |GNC.enorm (p t) - r0| = 0 := le_antisymm h this
    rw [abs_eq_zero, sub_eq_zero] at h0
    exact h0
  intro τ hτ hass _ t ht
  have hτT : Icc 0 τ ⊆ Icc 0 T := Icc_subset_Icc_right hτ.2
  have hIco : Ico 0 τ ⊆ Ico 0 T := Ico_subset_Ico_right hτ.2
  -- the assumption extends to the closed prefix
  have hassC : ∀ t ∈ Icc 0 τ, |GNC.enorm (p t) - r0| ≤ r0 / 2 := by
    intro t ht
    rcases ht.2.lt_or_eq with hlt | heq
    · exact hass () t ⟨ht.1, hlt⟩
    subst heq
    rcases ht.1.lt_or_eq with hpos | h0
    · have hcw : ContinuousWithinAt (s ()) (Ico 0 t) t :=
        ((hscont ()) t (hτT ht)).mono (Ico_subset_Icc_self.trans hτT)
      have hcl : t ∈ closure (Ico 0 t) := by
        rw [closure_Ico hpos.ne]; exact ⟨hpos.le, le_rfl⟩
      haveI : (𝓝[Ico 0 t] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
      exact le_of_tendsto hcw.tendsto
        (eventually_nhdsWithin_of_forall fun u hu => hass () u hu)
    · subst h0
      rw [show p 0 = (Y 0).pos from rfl, hp0, sub_self, abs_zero]
      linarith
  have hrlow : ∀ t ∈ Icc 0 τ, r0 / 2 ≤ GNC.enorm (p t) := by
    intro t ht
    have := (abs_le.mp (hassC t ht)).1
    linarith
  have hLne : ∀ t ∈ Icc 0 τ, p t ⬝ᵥ p t ≠ 0 := by
    intro t ht h
    have := hrlow t ht
    rw [kepler_enorm_eq_sqrt, h, Real.sqrt_zero] at this
    linarith
  -- both quantities are constant on the prefix
  have hHconst := constant_of_has_deriv_right_zero (f := H)
    (((kepler_dot_continuousOn hpc hpc).mul (kepler_dot_continuousOn hvc hvc)).sub
      ((kepler_dot_continuousOn hpc hvc).pow 2) |>.mono hτT)
    (fun t ht => hHd t (hIco ht))
  have hpcτ := hpc.mono hτT
  have hvcτ := hvc.mono hτT
  have hEconst := constant_of_has_deriv_right_zero (f := E)
    (((kepler_dot_continuousOn hvcτ hvcτ).div_const 2).sub
      (continuousOn_const.div (kepler_dot_continuousOn hpcτ hpcτ).sqrt fun t ht => by
        rw [Real.sqrt_ne_zero']
        exact lt_of_le_of_ne (kepler_dot_self_nonneg _) (Ne.symm (hLne t ht))))
    (fun t ht => hEd t (hIco ht) (hLne t (Ico_subset_Icc_self ht)))
  -- algebra: the radius equals `r0`
  set r := GNC.enorm (p t) with hrdef
  have hrpos : 0 < r := by have := hrlow t ht; linarith
  have hLt : p t ⬝ᵥ p t = r ^ 2 := (kepler_enorm_sq_dot _).symm
  have hHt : H t = μ * r0 := (hHconst t ht).trans hH0
  have hEt : E t = -μ / (2 * r0) := (hEconst t ht).trans hE0
  simp only [hE, hLt, Real.sqrt_sq hrpos.le] at hEt
  simp only [hH, hLt] at hHt
  have hVt : v t ⬝ᵥ v t = -μ / r0 + 2 * μ / r := by
    field_simp at hEt ⊢
    linarith
  rw [hVt] at hHt
  have hineq : μ * r0 ≤ r ^ 2 * (-μ / r0 + 2 * μ / r) := by
    nlinarith [sq_nonneg (p t ⬝ᵥ v t)]
  have h2 : μ * r0 ^ 2 ≤ μ * (2 * r * r0 - r ^ 2) := by
    have e : r ^ 2 * (-μ / r0 + 2 * μ / r) = μ * (2 * r * r0 - r ^ 2) / r0 := by
      field_simp
      ring
    rw [e, le_div_iff₀ hr0] at hineq
    nlinarith
  have h3 : μ * (r - r0) ^ 2 ≤ 0 := by nlinarith
  have h4 : (r - r0) ^ 2 = 0 :=
    le_antisymm (by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_pos hμ hcon]) (sq_nonneg _)
  have h5 : r = r0 := by nlinarith [sq_eq_zero_iff.mp h4]
  change |GNC.enorm (p t) - r0| ≤ 0
  rw [← hrdef, h5, sub_self, abs_zero]

/-- Certificate form: the radius never drops below the initial circular radius. -/
theorem circular_radius_ge {Y : ℝ → SE23} {abar wbar gbar : ℝ → Vec3} {T μ r0 : ℝ}
    (hY : SpacecraftSolution Y abar wbar gbar T)
    (ha : ∀ t ∈ Ico 0 T, abar t = 0)
    (hg : ∀ t ∈ Ico 0 T, gbar t = Gravity.field3 μ (Y t).pos)
    (hμ : 0 < μ) (hr0 : 0 < r0)
    (hp0 : GNC.enorm (Y 0).pos = r0) (hv0 : GNC.enorm (Y 0).vel ^ 2 = μ / r0)
    (ho0 : (Y 0).pos ⬝ᵥ (Y 0).vel = 0) :
    ∀ t ∈ Icc 0 T, r0 ≤ GNC.enorm (Y t).pos := fun t ht =>
  (circular_radius_const hY ha hg hμ hr0 hp0 hv0 ho0 t ht).ge

end Dynacert.Lie
