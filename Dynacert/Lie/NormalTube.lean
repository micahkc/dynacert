import Dynacert.Normal.QC
import Dynacert.Lie.Supply
import Dynacert.Linear.Supply

/-!
# SE₂(3) log-error tube from a normal-form certificate

`log_error_tube` proves invariance of a sublevel of the log error from a supply inequality for
the exact log-error field. This file discharges that inequality from a `QCCert`, so the tube
holds for **any** controller and any gravity model whose closed-loop log-error field, on the
certified sublevel, has the normal form

  `flat ξ̇ = (Σᵢ λᵢ Aᵢ) flat ξ + B w`,   `D.Holds (flat ξ) w`,   `Σ γⱼ wⱼ² ≤ budget`.

Nothing here mentions a control law. A controller enters a certificate only through the
per-model link that establishes this decomposition (algebra on the model's equations) and the
constraint facts (atom lemmas: Jacobian bounds, gravity mismatch, attitude-error maps). The
reference enters through the polytope: the drift `-ad(n̄)` depends on `ā, ω̄`, and an envelope
on them is a set of vertices.
-/

noncomputable section

namespace Dynacert.Lie

open GNC Set Real Matrix WithLp GNC.PolytopicTube Dynacert Dynacert.Linear Dynacert.Normal

theorem quadDeriv_symm {n : ℕ} {P : Matrix (Fin n) (Fin n) ℚ} (hP : P.transpose = P)
    (x h : Fin n → ℝ) :
    quadDeriv (toReal P) x h = 2 * (x ⬝ᵥ toReal P *ᵥ h) := by
  have hR : (toReal P).transpose = toReal P := by rw [toReal, ← Matrix.transpose_map, hP]
  have hs : h ⬝ᵥ toReal P *ᵥ x = x ⬝ᵥ toReal P *ᵥ h := by
    conv_lhs => rw [← hR]
    rw [Dynacert.dotProduct_transpose_mulVec]
  rw [quadDeriv, hs]; ring

/-- **Log-error tube, any controller.** If, on the certified sublevel and in the principal
domain, the exact log-error field has the normal form of a checked `QCCert`, the error stays in
the principal domain and in the sublevel, and the storage decays to `budget / α`. -/
theorem log_tube_qc {m v c : ℕ} {D : QCData 9 m v c 0} (C : QCCert D)
    {X Y : ℝ → SE23} {a w abar wbar g gbar : ℝ → Vec3} {T budget ρ Rc : ℝ}
    (sig : ℝ → Fin m → ℝ)
    (hX : SpacecraftSolution X a w g T) (hY : SpacecraftSolution Y abar wbar gbar T)
    (hbudget : budget < D.α * ρ) (hRc : Rc < π)
    (hchart : ∀ ξ : LogState, storage (clm D.P) (flat ξ) ≤ ρ → GNC.enorm (ξ 2) ≤ Rc)
    (hdom0 : SE23.error (Y 0) (X 0) ∈ PrincipalLog.domain)
    (hinit : storage (clm D.P) (flat (principalError X Y 0)) ≤ ρ)
    (hnormal : ∀ t ∈ Ico 0 T, SE23.error (Y t) (X t) ∈ PrincipalLog.domain →
      storage (clm D.P) (flat (principalError X Y t)) ≤ ρ →
      ∃ wt : Fin v → ℝ, (∀ i, 0 ≤ wt i) ∧ ∑ i, wt i = 1 ∧
        ofLp (flat (logErrorField X Y (a t) (w t) (abar t) (wbar t) (g t) (gbar t) t)) =
          (∑ i, wt i • toReal (D.A i)) *ᵥ ofLp (flat (principalError X Y t)) +
            toReal D.B *ᵥ sig t ∧
        D.Holds (ofLp (flat (principalError X Y t))) (sig t) ∧ D.energy (sig t) ≤ budget) :
    ∀ t ∈ Icc 0 T, SE23.error (Y t) (X t) ∈ PrincipalLog.domain ∧
      storage (clm D.P) (flat (principalError X Y t)) ≤ ρ ∧
      storage (clm D.P) (flat (principalError X Y t)) ≤
        max (storage (clm D.P) (flat (principalError X Y 0))) (budget / D.α) := by
  have hα : (0 : ℝ) < D.α := by exact_mod_cast C.hα
  refine log_error_tube (clm D.P) (clm_symm C.P_symm) hX hY hα hbudget hRc hchart hdom0
    hinit ?_
  intro t ht hd hρ
  obtain ⟨wt, hwt, hs, hF, hH, hE⟩ := hnormal t ht hd hρ
  have hsup := C.supply wt hwt hs _ _ hH
  rw [← hF, QCCert.coupling_zero, quadDeriv_symm C.P_symm] at hsup
  rw [Dynacert.Linear.inner_eq, ofLp_clm, storage_clm]
  linarith

end Dynacert.Lie
