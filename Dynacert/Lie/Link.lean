import Dynacert.Lie.PhysicalOutput
import Rumoca.Prelude
import GNC.Dynamics.GravityLinearization

/-!
# Link: rumoca's array states to an SE₂(3) trajectory

rumoca's `lean-dae` target keeps Modelica arrays: a 3-vector state is `Fin 3 → ℝ` (gnc's
`Vec3`), a 3×3 state is `Matrix (Fin 3) (Fin 3) ℝ`, and `IsSolutionOn` gives continuity and right
derivatives componentwise. This file assembles those into `SpacecraftSolution`, given the three
kinematic identities `ṗ = v`, `v̇ = R a + g`, `Ṙ = R · skew ω` (which a generated per-model proof
derives from the model's `Equations`, with `a`, `ω`, `g` found by `structure.py`).
-/

noncomputable section

namespace Dynacert.Lie

open GNC Matrix Set

local notation "M3" => Matrix (Fin 3) (Fin 3) ℝ

/-- Modelica's `skew` (rumoca prelude) is gnc's `skew`. -/
theorem rumoca_skew_eq (w : Vec3) : Rumoca.skew w = GNC.skew w := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Rumoca.skew, GNC.skew]

theorem continuousOn_vec {p : ℝ → Vec3} {s : Set ℝ}
    (h : ∀ i, ContinuousOn (fun t => p t i) s) : ContinuousOn p s :=
  continuousOn_pi.mpr h

theorem continuousOn_mat {R : ℝ → M3} {s : Set ℝ}
    (h : ∀ i j, ContinuousOn (fun t => R t i j) s) : ContinuousOn R s :=
  continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => h i j

theorem hasDerivWithinAt_vec {p : ℝ → Vec3} {dp : Vec3} {s : Set ℝ} {t : ℝ}
    (h : ∀ i, HasDerivWithinAt (fun u => p u i) (dp i) s t) : HasDerivWithinAt p dp s t :=
  hasDerivWithinAt_pi.mpr h

theorem hasDerivWithinAt_mat {R : ℝ → M3} {dR : M3} {s : Set ℝ} {t : ℝ}
    (h : ∀ i j, HasDerivWithinAt (fun u => R u i j) (dR i j) s t) :
    HasDerivWithinAt R dR s t :=
  hasDerivWithinAt_pi.mpr fun i => hasDerivWithinAt_pi.mpr fun j => h i j

/-- **Componentwise link.** Componentwise continuity and right derivatives (rumoca's
`IsSolutionOn`), the three kinematic identities on `[0, T)`, and `R 0 ∈ SO(3)` give an SE₂(3)
trajectory. `R` stays in `SO(3)` by `rotation_mem_SO3`; nothing about `ω` is assumed. -/
theorem spacecraft_of_components {p v dp dv : ℝ → Vec3} {R dR : ℝ → M3} {a w g : ℝ → Vec3}
    {T : ℝ}
    (hpc : ∀ i, ContinuousOn (fun s => p s i) (Icc 0 T))
    (hvc : ∀ i, ContinuousOn (fun s => v s i) (Icc 0 T))
    (hRc : ∀ i j, ContinuousOn (fun s => R s i j) (Icc 0 T))
    (hpd : ∀ t ∈ Ico 0 T, ∀ i, HasDerivWithinAt (fun s => p s i) (dp t i) (Ici t) t)
    (hvd : ∀ t ∈ Ico 0 T, ∀ i, HasDerivWithinAt (fun s => v s i) (dv t i) (Ici t) t)
    (hRd : ∀ t ∈ Ico 0 T, ∀ i j, HasDerivWithinAt (fun s => R s i j) (dR t i j) (Ici t) t)
    (hp : ∀ t ∈ Ico 0 T, dp t = v t)
    (hv : ∀ t ∈ Ico 0 T, dv t = R t *ᵥ a t + g t)
    (hR : ∀ t ∈ Ico 0 T, dR t = R t * Rumoca.skew (w t))
    (hR0 : R 0 ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    SpacecraftSolution (ofScalars p v R) a w g T := by
  refine ofScalars_solution (continuousOn_vec hpc) (continuousOn_vec hvc) (continuousOn_mat hRc)
    (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) hR0
  · rw [← hp t ht]; exact hasDerivWithinAt_vec (hpd t ht)
  · rw [← hv t ht]; exact hasDerivWithinAt_vec (hvd t ht)
  · rw [← rumoca_skew_eq, ← hR t ht]; exact hasDerivWithinAt_mat (hRd t ht)

/-- The identity start value that rumoca writes for `R(start = identity(3))`. -/
theorem identity_mem_SO3 :
    (Matrix.of ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] : M3) ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have h : (Matrix.of ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] : M3) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [h]; exact Submonoid.one_mem _

/-- rumoca's transcription of Modelica's `-mu*p/(p*p)^1.5` is gnc's inverse-square field. -/
theorem rumoca_inverse_square (μ : ℝ) (q : Vec3) :
    -(((q ⬝ᵥ q) ^ (1.5 : ℝ))⁻¹ • μ • q) = Gravity.field3 μ q := by
  set n := ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin 3))‖ with hn
  have hsq : q ⬝ᵥ q = n ^ 2 := by
    rw [hn, EuclideanSpace.norm_sq_eq]
    simp [dotProduct, Fin.sum_univ_three, Real.norm_eq_abs, sq]
  have hpow : (n ^ 2) ^ (1.5 : ℝ) = n ^ 3 := by
    have h0 : 0 ≤ n := norm_nonneg _
    rw [← Real.rpow_natCast n 2, ← Real.rpow_mul h0, ← Real.rpow_natCast n 3]
    norm_num
  rw [hsq, hpow]
  funext i
  simp only [Gravity.field3, Gravity.field, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    WithLp.ofLp_smul, ← hn]
  rw [neg_div, div_eq_inv_mul]
  ring

end Dynacert.Lie
