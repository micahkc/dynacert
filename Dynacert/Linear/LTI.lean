import Dynacert.Core.QuadForm
import Dynacert.Core.System

/-!
# Linear time-invariant systems

Quadratic storage functions `V x = xᵀ P x` for `ẋ = A x + B w`. The dissipation condition
`V̇ ≤ -α V + γ wᵀw` is the block LMI `lmiMatrix A B P α γ ⪰ 0`, checked exactly over `ℚ`
via a `PSDWitness`. `BoxCert` turns the resulting invariant ellipsoid into per-state bounds.
-/

namespace Dynacert.Linear

open Matrix Set

variable {n m : ℕ}

/-! ### Calculus of quadratic forms -/

theorem quad_continuous (P : Matrix (Fin n) (Fin n) ℝ) : Continuous (quad P) := by
  unfold quad dotProduct mulVec dotProduct
  fun_prop

/-- Derivative of `xᵀ P x` in direction `h`. -/
def quadDeriv (P : Matrix (Fin n) (Fin n) ℝ) (x h : Fin n → ℝ) : ℝ :=
  h ⬝ᵥ P *ᵥ x + x ⬝ᵥ P *ᵥ h

theorem quad_hasDirDeriv (P : Matrix (Fin n) (Fin n) ℝ) : HasDirDeriv (quad P) (quadDeriv P) := by
  intro c c' s t hc
  have hci := hasDerivWithinAt_pi.1 hc
  have h : HasDerivWithinAt (fun τ => ∑ i, c τ i * ∑ j, P i j * c τ j)
      (∑ i, (c' i * ∑ j, P i j * c t j + c t i * ∑ j, P i j * c' j)) s t :=
    HasDerivWithinAt.fun_sum fun i _ => (hci i).mul
      (HasDerivWithinAt.fun_sum fun j _ => (hci j).const_mul (P i j))
  rw [quadDeriv, Finset.sum_add_distrib] at *
  exact h

/-! ### The dissipation LMI -/

/-- The negated dissipation LMI. Over any commutative ring,
`lmiMatrix A B P α γ = -[[AᵀP + PA + αP, PB], [BᵀP, -γI]]`; the certificate asserts it is PSD. -/
def lmiMatrix {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin n) (Fin m) R) (P : Matrix (Fin n) (Fin n) R) (α γ : R) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) R :=
  fromBlocks (-(Aᵀ * P + P * A + α • P)) (-(P * B)) (-(Bᵀ * P)) (γ • 1)

/-- The quadratic form of the LMI matrix at `(x, w)` is
`-V̇(x, w) - α V(x) + γ wᵀw`, where `V̇` is the derivative of `xᵀPx` along `Ax + Bw`. -/
theorem quad_lmiMatrix {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin n) (Fin m) R) (P : Matrix (Fin n) (Fin n) R) (hP : Pᵀ = P) (α γ : R)
    (x : Fin n → R) (w : Fin m → R) :
    quad (lmiMatrix A B P α γ) (Sum.elim x w) =
      -((A *ᵥ x + B *ᵥ w) ⬝ᵥ P *ᵥ x + x ⬝ᵥ P *ᵥ (A *ᵥ x + B *ᵥ w)) - α * quad P x
        + γ * (w ⬝ᵥ w) := by
  -- `u ⬝ᵥ (Mᵀ * P) *ᵥ v = (M *ᵥ u) ⬝ᵥ P *ᵥ v`
  have hT : ∀ {k : ℕ} (M : Matrix (Fin n) (Fin k) R) (u : Fin k → R) (v : Fin n → R),
      u ⬝ᵥ (Mᵀ * P) *ᵥ v = (M *ᵥ u) ⬝ᵥ P *ᵥ v := by
    intro k M u v
    rw [← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]
  -- symmetry of `P`
  have hS : x ⬝ᵥ P *ᵥ (B *ᵥ w) = (B *ᵥ w) ⬝ᵥ P *ᵥ x := by
    conv_lhs => rw [← hP]
    rw [dotProduct_transpose_mulVec]
  simp only [quad, lmiMatrix, fromBlocks_mulVec, sumElim_dotProduct_sumElim, Sum.elim_comp_inl,
    Sum.elim_comp_inr, neg_mulVec, add_mulVec, smul_mulVec, one_mulVec, dotProduct_neg,
    dotProduct_add, dotProduct_smul, add_dotProduct, mulVec_add, smul_eq_mul, hT]
  rw [← mulVec_mulVec, ← mulVec_mulVec, hS]
  ring

theorem toReal_lmiMatrix (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin m) ℚ)
    (P : Matrix (Fin n) (Fin n) ℚ) (α γ : ℚ) :
    toReal (lmiMatrix A B P α γ) =
      lmiMatrix (toReal A) (toReal B) (toReal P) (α : ℝ) (γ : ℝ) := by
  ext (i | i) (j | j) <;> simp [lmiMatrix, toReal, Matrix.mul_apply, Matrix.one_apply, apply_ite]
  split_ifs <;> simp_all

/-! ### LTI models and certificates -/

/-- An LTI model `ẋ = A x + B w` with exact rational coefficients. -/
structure LTIModel (n m : ℕ) where
  A : Matrix (Fin n) (Fin n) ℚ
  B : Matrix (Fin n) (Fin m) ℚ

noncomputable def LTIModel.toSystem (M : LTIModel n m) : System n m :=
  ⟨fun x w => toReal M.A *ᵥ x + toReal M.B *ᵥ w⟩

/-- Disturbances with `wᵀw ≤ μ`. -/
def energyBall (μ : ℝ) : Set (Fin m → ℝ) := {w | w ⬝ᵥ w ≤ μ}

/-- A quadratic dissipation certificate for an LTI model: a symmetric `P` and rates `α > 0`,
`γ ≥ 0` such that `[[AᵀP + PA + αP, PB], [BᵀP, -γI]] ⪯ 0`, witnessed exactly. -/
structure LTICert (M : LTIModel n m) where
  P : Matrix (Fin n) (Fin n) ℚ
  α : ℚ
  γ : ℚ
  hα : 0 < α
  hγ : 0 ≤ γ
  P_symm : Pᵀ = P
  lmi : PSDWitness (lmiMatrix M.A M.B P α γ)

namespace LTICert

variable {M : LTIModel n m}

theorem toReal_P_symm (C : LTICert M) : (toReal C.P)ᵀ = toReal C.P := by
  rw [toReal, ← transpose_map, C.P_symm]

/-- Every LTI certificate is a dissipation certificate with `V x = xᵀPx` and rate `γ μ`. -/
noncomputable def toDissipationCert (C : LTICert M) (μ : ℝ) :
    DissipationCert M.toSystem (energyBall μ) where
  V := quad (toReal C.P)
  DV := quadDeriv (toReal C.P)
  α := C.α
  γ := C.γ * μ
  hα := by exact_mod_cast C.hα
  V_cont := quad_continuous _
  hDV := quad_hasDirDeriv _
  dissipation := by
    intro x w hw
    have h := C.lmi.quad_nonneg (Sum.elim x w)
    rw [toReal_lmiMatrix, quad_lmiMatrix _ _ _ C.toReal_P_symm] at h
    have hγ : (0 : ℝ) ≤ C.γ := by exact_mod_cast C.hγ
    have hw' : (C.γ : ℝ) * (w ⬝ᵥ w) ≤ C.γ * μ := mul_le_mul_of_nonneg_left hw hγ
    simp only [quadDeriv, LTIModel.toSystem]
    linarith

/-- Reach-set soundness for LTI certificates: started in `{xᵀPx ≤ c}` with `γ μ / α ≤ c`,
every solution under disturbances `wᵀw ≤ μ` stays in `{xᵀPx ≤ c}`. -/
theorem invariant (C : LTICert M) {x : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ} {T μ c : ℝ}
    (hx : M.toSystem.IsSolution x w T) (hw : ∀ t ∈ Ico 0 T, w t ⬝ᵥ w t ≤ μ)
    (h0 : quad (toReal C.P) (x 0) ≤ c) (hc : C.γ * μ / C.α ≤ c) :
    ∀ t ∈ Icc 0 T, quad (toReal C.P) (x t) ≤ c :=
  (C.toDissipationCert μ).invariant hx hw h0 hc

end LTICert

/-! ### From ellipsoids to per-state bounds -/

/-- Certifies `|xᵢ| ≤ b` on the ellipsoid `{xᵀPx ≤ c}`, via `b² P - c eᵢeᵢᵀ ⪰ 0`. -/
structure BoxCert (P : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (i : Fin n) (b : ℚ) where
  hc : 0 < c
  hb : 0 ≤ b
  psd : PSDWitness (b ^ 2 • P - c • diagonal (Pi.single i 1))

theorem BoxCert.abs_le {P : Matrix (Fin n) (Fin n) ℚ} {c b : ℚ} {i : Fin n}
    (B : BoxCert P c i b) {x : Fin n → ℝ} (hx : quad (toReal P) x ≤ c) : |x i| ≤ b := by
  have h := B.psd.quad_nonneg x
  have hM : toReal (b ^ 2 • P - c • diagonal (Pi.single i 1)) =
      ((b : ℝ) ^ 2) • toReal P - (c : ℝ) • diagonal (Pi.single i 1) := by
    ext j k
    by_cases hjk : j = k
    · subst hjk
      by_cases hij : j = i <;> simp [toReal, hij]
    · simp [toReal, hjk]
  have hq : quad (diagonal (Pi.single i (1 : ℝ))) x = x i * x i := by
    simp [quad, dotProduct, mulVec_diagonal, Pi.single_apply]
  rw [hM, quad, sub_mulVec, smul_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    dotProduct_smul, ← quad, ← quad, hq, smul_eq_mul, smul_eq_mul] at h
  have hc : (0 : ℝ) < c := by exact_mod_cast B.hc
  have hb : (0 : ℝ) ≤ b := by exact_mod_cast B.hb
  have hsq : x i * x i ≤ b * b := by
    have := mul_le_mul_of_nonneg_left hx (sq_nonneg (b : ℝ))
    nlinarith
  exact _root_.abs_le.mpr ⟨by nlinarith, by nlinarith⟩

end Dynacert.Linear
