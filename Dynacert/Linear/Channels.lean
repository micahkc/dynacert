import Dynacert.Linear.LTI

/-!
# Multi-channel disturbances and linear outputs

`LTICert` uses one rate `γ` for the whole disturbance vector (`V̇ ≤ -αV + γ wᵀw`).
`ChannelCert` gives each channel its own rate: `V̇ ≤ -αV + Σⱼ γⱼ wⱼ²`. With componentwise
peak bounds `|wⱼ| ≤ δⱼ` this gives the budget `Σⱼ γⱼ δⱼ²`, which is how cp_reach's
multi-channel LMI bounds disturbances.

`LinearBoxCert` bounds a linear output `vᵀx` on an ellipsoid, generalizing `BoxCert` from
coordinates to arbitrary rows `v`.
-/

namespace Dynacert.Linear

open Matrix Set Dynacert

variable {n m : ℕ}

/-- The negated per-channel dissipation LMI:
`-[[AᵀP + PA + αP, PB], [BᵀP, -diag γ]]`. -/
def channelLmi {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin n) (Fin m) R) (P : Matrix (Fin n) (Fin n) R) (α : R) (γ : Fin m → R) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) R :=
  fromBlocks (-(Aᵀ * P + P * A + α • P)) (-(P * B)) (-(Bᵀ * P)) (diagonal γ)

theorem quad_channelLmi {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin n) (Fin m) R) (P : Matrix (Fin n) (Fin n) R) (hP : Pᵀ = P) (α : R)
    (γ : Fin m → R) (x : Fin n → R) (w : Fin m → R) :
    quad (channelLmi A B P α γ) (Sum.elim x w) =
      -((A *ᵥ x + B *ᵥ w) ⬝ᵥ P *ᵥ x + x ⬝ᵥ P *ᵥ (A *ᵥ x + B *ᵥ w)) - α * quad P x
        + ∑ j, γ j * (w j * w j) := by
  have hT : ∀ {k : ℕ} (M : Matrix (Fin n) (Fin k) R) (u : Fin k → R) (v : Fin n → R),
      u ⬝ᵥ (Mᵀ * P) *ᵥ v = (M *ᵥ u) ⬝ᵥ P *ᵥ v := by
    intro k M u v
    rw [← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]
  have hS : x ⬝ᵥ P *ᵥ (B *ᵥ w) = (B *ᵥ w) ⬝ᵥ P *ᵥ x := by
    conv_lhs => rw [← hP]
    rw [dotProduct_transpose_mulVec]
  have hD : w ⬝ᵥ diagonal γ *ᵥ w = ∑ j, γ j * (w j * w j) := by
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [quad, channelLmi, fromBlocks_mulVec, sumElim_dotProduct_sumElim, Sum.elim_comp_inl,
    Sum.elim_comp_inr, neg_mulVec, add_mulVec, smul_mulVec, dotProduct_neg,
    dotProduct_add, dotProduct_smul, add_dotProduct, mulVec_add, smul_eq_mul, hT, hD]
  rw [← mulVec_mulVec, ← mulVec_mulVec, hS]
  ring

theorem toReal_channelLmi (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin m) ℚ)
    (P : Matrix (Fin n) (Fin n) ℚ) (α : ℚ) (γ : Fin m → ℚ) :
    toReal (channelLmi A B P α γ) =
      channelLmi (toReal A) (toReal B) (toReal P) (α : ℝ) (fun j => (γ j : ℝ)) := by
  ext (i | i) (j | j) <;> simp [channelLmi, toReal, Matrix.mul_apply, diagonal_apply,
    apply_ite]
  split_ifs <;> simp_all

/-- A per-channel quadratic dissipation certificate for `ẋ = A x + B w`. -/
structure ChannelCert (M : LTIModel n m) where
  P : Matrix (Fin n) (Fin n) ℚ
  α : ℚ
  γ : Fin m → ℚ
  hα : 0 < α
  hγ : ∀ j, 0 ≤ γ j
  P_symm : Pᵀ = P
  lmi : PSDWitness (channelLmi M.A M.B P α γ)

namespace ChannelCert

variable {M : LTIModel n m}

/-- The weighted disturbance energy `Σⱼ γⱼ wⱼ²`. -/
noncomputable def energy (C : ChannelCert M) (w : Fin m → ℝ) : ℝ := ∑ j, (C.γ j : ℝ) * (w j * w j)

/-- Componentwise peak bounds give the budget `Σⱼ γⱼ δⱼ²`. -/
theorem energy_le_of_abs_le (C : ChannelCert M) {w : Fin m → ℝ} {δ : Fin m → ℚ}
    (hw : ∀ j, |w j| ≤ δ j) : C.energy w ≤ ∑ j, (C.γ j : ℝ) * ((δ j : ℝ) * (δ j : ℝ)) := by
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast C.hγ j)
  have h := hw j
  have h0 : 0 ≤ |w j| := abs_nonneg _
  have hsq : w j * w j = |w j| * |w j| := (abs_mul_abs_self (w j)).symm
  rw [hsq]
  exact mul_le_mul h h h0 (h0.trans h)

/-- Every channel certificate is a dissipation certificate for any energy budget. -/
noncomputable def toDissipationCert (C : ChannelCert M) (budget : ℝ) :
    DissipationCert M.toSystem {w | C.energy w ≤ budget} where
  V := quad (toReal C.P)
  DV := quadDeriv (toReal C.P)
  α := C.α
  γ := budget
  hα := by exact_mod_cast C.hα
  V_cont := quad_continuous _
  hDV := quad_hasDirDeriv _
  dissipation := by
    intro x w hw
    have hPs : (toReal C.P)ᵀ = toReal C.P := by rw [toReal, ← transpose_map, C.P_symm]
    have h := C.lmi.quad_nonneg (Sum.elim x w)
    rw [toReal_channelLmi, quad_channelLmi _ _ _ hPs] at h
    simp only [Set.mem_setOf_eq, energy] at hw
    simp only [quadDeriv, LTIModel.toSystem]
    linarith

/-- Invariance of `{xᵀPx ≤ c}` under disturbances of bounded weighted energy. -/
theorem invariant (C : ChannelCert M) {x : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ} {T budget c : ℝ}
    (hx : M.toSystem.IsSolution x w T) (hw : ∀ t ∈ Ico 0 T, C.energy (w t) ≤ budget)
    (h0 : quad (toReal C.P) (x 0) ≤ c) (hc : budget / C.α ≤ c) :
    ∀ t ∈ Icc 0 T, quad (toReal C.P) (x t) ≤ c :=
  (C.toDissipationCert budget).invariant hx hw h0 hc

end ChannelCert

/-! ### Linear outputs on an ellipsoid -/

theorem toReal_sub_smul {k : ℕ} (P : Matrix (Fin n) (Fin n) ℚ) (C : Matrix (Fin k) (Fin n) ℚ)
    (b c : ℚ) : toReal (b ^ 2 • P - c • (Cᵀ * C)) =
      ((b : ℝ) ^ 2) • toReal P - (c : ℝ) • ((toReal C)ᵀ * toReal C) := by
  ext i j
  simp [toReal, Matrix.mul_apply]

/-- Certifies `|vᵀx| ≤ b` on `{xᵀPx ≤ c}` via `b² P - c vvᵀ ⪰ 0`. -/
structure LinearBoxCert (P : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (v : Fin n → ℚ) (b : ℚ) where
  hc : 0 < c
  hb : 0 ≤ b
  psd : PSDWitness (b ^ 2 • P - c • vecMulVec v v)

theorem LinearBoxCert.abs_le {P : Matrix (Fin n) (Fin n) ℚ} {c b : ℚ} {v : Fin n → ℚ}
    (B : LinearBoxCert P c v b) {x : Fin n → ℝ} (hx : quad (toReal P) x ≤ c) :
    |(fun i => (v i : ℝ)) ⬝ᵥ x| ≤ b := by
  have h := B.psd.quad_nonneg x
  set vr : Fin n → ℝ := fun i => (v i : ℝ)
  have hM : toReal (b ^ 2 • P - c • vecMulVec v v) =
      ((b : ℝ) ^ 2) • toReal P - (c : ℝ) • vecMulVec vr vr := by
    ext j k; simp [toReal, vecMulVec_apply, vr]
  have hq : quad (vecMulVec vr vr) x = (vr ⬝ᵥ x) * (vr ⬝ᵥ x) := by
    simp only [quad, vecMulVec_mulVec, dotProduct_smul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    rw [dotProduct_comm x vr]
  rw [hM, quad, sub_mulVec, smul_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    dotProduct_smul, ← quad, ← quad, hq, smul_eq_mul, smul_eq_mul] at h
  have hc : (0 : ℝ) < c := by exact_mod_cast B.hc
  have hb : (0 : ℝ) ≤ b := by exact_mod_cast B.hb
  have hsq : (vr ⬝ᵥ x) * (vr ⬝ᵥ x) ≤ b * b := by
    have := mul_le_mul_of_nonneg_left hx (sq_nonneg (b : ℝ))
    nlinarith
  exact _root_.abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-! ### Block norms on an ellipsoid -/

/-- Certifies `‖C x‖ ≤ b` (Euclidean norm of a block of outputs) on `{xᵀPx ≤ c}` via
`b² P - c CᵀC ⪰ 0`. -/
structure NormBoxCert {k : ℕ} (P : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (C : Matrix (Fin k) (Fin n) ℚ)
    (b : ℚ) where
  hc : 0 < c
  hb : 0 ≤ b
  psd : PSDWitness (b ^ 2 • P - c • (Cᵀ * C))

theorem NormBoxCert.sq_le {k : ℕ} {P : Matrix (Fin n) (Fin n) ℚ} {c b : ℚ}
    {C : Matrix (Fin k) (Fin n) ℚ} (B : NormBoxCert P c C b) {x : Fin n → ℝ}
    (hx : quad (toReal P) x ≤ c) : (toReal C *ᵥ x) ⬝ᵥ (toReal C *ᵥ x) ≤ (b : ℝ) ^ 2 := by
  have h := B.psd.quad_nonneg x
  have hM : toReal (b ^ 2 • P - c • (Cᵀ * C)) =
      ((b : ℝ) ^ 2) • toReal P - (c : ℝ) • ((toReal C)ᵀ * toReal C) := by
    rw [toReal_sub_smul]
  have hq : quad ((toReal C)ᵀ * toReal C) x = (toReal C *ᵥ x) ⬝ᵥ (toReal C *ᵥ x) := by
    rw [quad, ← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]
  rw [hM, quad, sub_mulVec, smul_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    dotProduct_smul, ← quad, ← quad, hq, smul_eq_mul, smul_eq_mul] at h
  have hc : (0 : ℝ) < c := by exact_mod_cast B.hc
  have := mul_le_mul_of_nonneg_left hx (sq_nonneg (b : ℝ))
  have hcq : (c : ℝ) * ((toReal C *ᵥ x) ⬝ᵥ (toReal C *ᵥ x)) ≤ (c : ℝ) * (b : ℝ) ^ 2 := by
    nlinarith
  exact le_of_mul_le_mul_left hcq hc

end Dynacert.Linear
