import Dynacert.Linear.LTI
import GNC.Control.PolytopicTube

/-!
# From exact rational LMIs to gnc_lean supply inequalities

gnc_lean states its tube theorems over an abstract real inner product space, with the
storage `⟪x, P x⟫` and the vertex condition
`2 ⟪y, P (A y + B u)⟫ + α ⟪y, P y⟫ ≤ μ ‖u‖²` taken as hypotheses. This file discharges
those hypotheses from dynacert's exact certificates: rational matrices act on
`EuclideanSpace ℝ (Fin n)` through `clm`, and every inequality reduces to a
`PSDWitness` checked by the kernel.
-/

namespace Dynacert.Linear

open Matrix WithLp GNC.PolytopicTube

/-- The Euclidean state space `ℝⁿ` with its inner product. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A rational matrix as a continuous linear map between Euclidean spaces. -/
noncomputable def clm {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) : E n →L[ℝ] E m :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (toReal M))

@[simp] theorem ofLp_clm {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) (v : E n) :
    ofLp (clm M v) = toReal M *ᵥ ofLp v := rfl

theorem inner_eq {n : ℕ} (x y : E n) : inner ℝ x y = ofLp x ⬝ᵥ ofLp y := by
  change ofLp y ⬝ᵥ star (ofLp x) = _
  rw [star_trivial, dotProduct_comm]

theorem norm_sq_eq {n : ℕ} (u : E n) : ‖u‖ ^ 2 = ofLp u ⬝ᵥ ofLp u := by
  rw [← real_inner_self_eq_norm_sq, inner_eq]

theorem storage_clm {n : ℕ} (P : Matrix (Fin n) (Fin n) ℚ) (x : E n) :
    storage (clm P) x = quad (toReal P) (ofLp x) := by
  rw [storage, inner_eq, ofLp_clm, quad]

/-- A symmetric rational matrix gives a self-adjoint map, in the form gnc_lean uses. -/
theorem clm_symm {n : ℕ} {P : Matrix (Fin n) (Fin n) ℚ} (hP : Pᵀ = P) (u v : E n) :
    inner ℝ u (clm P v) = inner ℝ v (clm P u) := by
  have hR : (toReal P)ᵀ = toReal P := by rw [toReal, ← transpose_map, hP]
  rw [inner_eq, inner_eq, ofLp_clm, ofLp_clm]
  conv_lhs => rw [← hR]
  rw [dotProduct_transpose_mulVec]

/-! ### Quadratic-form facts from PSD witnesses -/

theorem toReal_sub {m n : ℕ} (M N : Matrix (Fin m) (Fin n) ℚ) :
    toReal (M - N) = toReal M - toReal N := by
  ext i j; simp [toReal]

theorem toReal_smul_one {n : ℕ} (c : ℚ) :
    toReal (c • (1 : Matrix (Fin n) (Fin n) ℚ)) = (c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j; by_cases h : i = j <;> simp [toReal, h]

theorem quad_smul_one {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    quad ((c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) x = c * (x ⬝ᵥ x) := by
  simp [quad, smul_mulVec, one_mulVec, dotProduct_smul]

theorem quad_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quad (M - N) x = quad M x - quad N x := by
  simp [quad, sub_mulVec, dotProduct_sub]

/-- Coercivity `m ‖x‖² ≤ ⟪x, P x⟫` from a witness for `P - m I ⪰ 0`. -/
theorem coercive_of_witness {n : ℕ} {P : Matrix (Fin n) (Fin n) ℚ} {m : ℚ}
    (W : PSDWitness (P - m • 1)) (x : E n) : (m : ℝ) * ‖x‖ ^ 2 ≤ storage (clm P) x := by
  have h := W.quad_nonneg (ofLp x)
  rw [toReal_sub, toReal_smul_one, quad_sub, quad_smul_one] at h
  rw [storage_clm, norm_sq_eq]
  linarith

/-- An operator-norm bound `‖M‖ ≤ c` from a witness for `c² I - Mᵀ M ⪰ 0`. -/
theorem opNorm_le_of_witness {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℚ} {c : ℚ} (hc : 0 ≤ c)
    (W : PSDWitness (c ^ 2 • 1 - Mᵀ * M)) : ‖clm M‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by exact_mod_cast hc) fun x => ?_
  have h := W.quad_nonneg (ofLp x)
  rw [toReal_sub, toReal_smul_one, quad_sub, quad_smul_one] at h
  have hMM : quad (toReal (Mᵀ * M)) (ofLp x) = ‖clm M x‖ ^ 2 := by
    rw [norm_sq_eq, ofLp_clm, quad, toReal, Matrix.map_mul, transpose_map, ← mulVec_mulVec,
      dotProduct_transpose_mulVec, dotProduct_comm]
  rw [hMM, ← norm_sq_eq] at h
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have hsq : ‖clm M x‖ ^ 2 ≤ ((c : ℝ) * ‖x‖) ^ 2 := by push_cast at h; nlinarith
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero |>.mp hsq

/-! ### The LTI dissipation LMI as a gnc_lean vertex supply -/

/-- An `LTICert` discharges gnc_lean's vertex hypothesis
`2 ⟪y, P (A y + B u)⟫ + α ⟪y, P y⟫ ≤ γ ‖u‖²` for the model's matrices. -/
theorem LTICert.supply {n m : ℕ} {M : LTIModel n m} (C : LTICert M) (y : E n) (u : E m) :
    2 * inner ℝ y (clm C.P (clm M.A y + clm M.B u)) + (C.α : ℝ) * storage (clm C.P) y ≤
      (C.γ : ℝ) * ‖u‖ ^ 2 := by
  have h := C.lmi.quad_nonneg (Sum.elim (ofLp y) (ofLp u))
  rw [toReal_lmiMatrix, quad_lmiMatrix _ _ _ C.toReal_P_symm] at h
  have hv : ofLp (clm M.A y + clm M.B u) = toReal M.A *ᵥ ofLp y + toReal M.B *ᵥ ofLp u := by
    simp
  have hs : ∀ v : Fin n → ℝ, v ⬝ᵥ toReal C.P *ᵥ ofLp y = ofLp y ⬝ᵥ toReal C.P *ᵥ v := by
    intro v
    conv_lhs => rw [← C.toReal_P_symm]
    rw [dotProduct_transpose_mulVec]
  rw [storage_clm, norm_sq_eq, inner_eq, ofLp_clm, hv]
  rw [hs] at h
  linarith

end Dynacert.Linear
