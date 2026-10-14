import GNC.Lie.Euclidean
import Mathlib

/-!
# SO(3) invariance for a nine-scalar attitude state

A Modelica model integrates the attitude as nine independent scalars `R : ℝ → ℝ³ˣ³` with
`Ṙ = R · skew ω`. This file proves that `R` stays in `SO(3)` if it starts there, using only
continuity on `[0, T]` and right derivatives on `[0, T)`. No bound on `ω` is needed.

Proof: put `D = RᵀR - 1`. Then `trace (D D)` has right derivative
`trace (Ḋ D + D Ḋ)` with `Ḋ = -S(D+1) + (D+1)S`, `S = skew ω`, which is zero by cyclicity of
the trace. So `trace (D D)` is constant, hence `0`. Since `D` is symmetric,
`trace (Dᵀ D) = 0` forces `D = 0`. Then `det R = ±1`, and continuity keeps it at `1`.
-/

noncomputable section

namespace Dynacert.Lie

open GNC Matrix Set
open scoped Matrix Matrix.Norms.Operator

local notation "M3" => Matrix (Fin 3) (Fin 3) ℝ

theorem skew_transpose (w : Vec3) : (skew w)ᵀ = -skew w := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [skew]

theorem hasDerivWithinAt_transpose3 {R : ℝ → M3} {R' : M3} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt R R' s t) : HasDerivWithinAt (fun u => (R u)ᵀ) R'ᵀ s t := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  apply hasDerivWithinAt_pi.mpr
  intro j
  exact hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp h j) i

theorem hasDerivWithinAt_trace3 {A : ℝ → M3} {A' : M3} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt A A' s t) : HasDerivWithinAt (fun u => (A u).trace) A'.trace s t := by
  have hl := (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap.hasFDerivAt
    (x := A t)
  exact hl.comp_hasDerivWithinAt t h

/-- The algebraic core: along `Ṙ = R S` with `S` skew, `trace ((RᵀR-1)²)` is stationary. -/
theorem orthogonality_defect_stationary (R S : M3) (hS : Sᵀ = -S) :
    (((R * S)ᵀ * R + Rᵀ * (R * S)) * (Rᵀ * R - 1) +
      (Rᵀ * R - 1) * ((R * S)ᵀ * R + Rᵀ * (R * S))).trace = 0 := by
  rw [transpose_mul, hS]
  set Q := Rᵀ * R with hQ
  have e1 : -S * Rᵀ * R = -(S * Q) := by rw [hQ, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc]
  have e2 : Rᵀ * (R * S) = Q * S := by rw [hQ, Matrix.mul_assoc]
  rw [e1, e2]
  have t1 : (S * (Q * Q)).trace = (Q * (Q * S)).trace := by
    rw [trace_mul_comm, Matrix.mul_assoc]
  have t2 : (S * Q).trace = (Q * S).trace := trace_mul_comm _ _
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, trace_add, trace_sub,
    trace_neg]
  linarith

/-- **SO(3) invariance.** A nine-scalar attitude `R` that is continuous on `[0, T]`, has right
derivative `R t * skew (w t)` on `[0, T)`, and starts in `SO(3)` stays in `SO(3)` on
`[0, T]`. -/
theorem rotation_mem_SO3 {R : ℝ → M3} {w : ℝ → Vec3} {T : ℝ}
    (hc : ContinuousOn R (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt R (R t * skew (w t)) (Ici t) t)
    (h0 : R 0 ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∀ t ∈ Icc 0 T, R t ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  set D : ℝ → M3 := fun t => (R t)ᵀ * R t - 1 with hD
  set v : ℝ → ℝ := fun t => (D t * D t).trace with hv
  -- continuity of v
  have hDc : ContinuousOn D (Icc 0 T) :=
    (((continuous_id.matrix_transpose).comp_continuousOn hc).mul hc).sub continuousOn_const
  have hvc : ContinuousOn v (Icc 0 T) :=
    (continuous_id.matrix_trace).comp_continuousOn (hDc.mul hDc)
  -- v has zero right derivative
  have hvd : ∀ t ∈ Ico 0 T, HasDerivWithinAt v 0 (Ici t) t := by
    intro t ht
    have hR := hd t ht
    have hQ := (hasDerivWithinAt_transpose3 hR).mul hR
    have hDd : HasDerivWithinAt D ((R t * skew (w t))ᵀ * R t + (R t)ᵀ * (R t * skew (w t)))
        (Ici t) t := hQ.sub_const 1
    have hv' := hasDerivWithinAt_trace3 (hDd.mul hDd)
    convert hv' using 1
    exact (orthogonality_defect_stationary (R t) (skew (w t)) (skew_transpose _)).symm
  have hconst := constant_of_has_deriv_right_zero hvc hvd
  have hR0 : (R 0)ᵀ * R 0 = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp
    (mem_specialOrthogonalGroup_iff.mp h0).1
  have horth : ∀ t ∈ Icc 0 T, (R t)ᵀ * R t = 1 := by
    intro t ht
    have h := hconst t ht
    have hv0 : v 0 = 0 := by simp [hv, hD, hR0]
    rw [hv0] at h
    have hsym : (D t)ᵀ = D t := by
      simp [hD, transpose_sub, transpose_mul, transpose_transpose]
    have hz : ((D t)ᴴ * D t).trace = 0 := by
      rw [conjTranspose_eq_transpose_of_trivial, hsym]
      exact h
    have := trace_conjTranspose_mul_self_eq_zero_iff.mp hz
    exact sub_eq_zero.mp this
  -- determinant
  have hdet2 : ∀ t ∈ Icc 0 T, (R t).det * (R t).det = 1 := by
    intro t ht
    have h := congrArg Matrix.det (horth t ht)
    rwa [det_mul, det_transpose, det_one] at h
  have hdetc : ContinuousOn (fun t => (R t).det) (Icc 0 T) :=
    (continuous_id.matrix_det).comp_continuousOn hc
  have hdet0 : (R 0).det = 1 := (mem_specialOrthogonalGroup_iff.mp h0).2
  intro t ht
  have hdet : (R t).det = 1 := by
    rcases mul_self_eq_one_iff.mp (hdet2 t ht) with h | h
    · exact h
    · exfalso
      have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
      have hivt := intermediate_value_Icc' ht.1 (hdetc.mono hsub)
      rw [hdet0, h] at hivt
      obtain ⟨s, hs, hs0⟩ := hivt (show (0 : ℝ) ∈ Icc (-1) 1 by norm_num)
      have := hdet2 s (hsub hs)
      simp only at hs0
      rw [hs0] at this
      norm_num at this
  exact mem_specialOrthogonalGroup_iff.mpr
    ⟨(mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr (horth t ht), hdet⟩

end Dynacert.Lie
