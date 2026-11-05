import Dynacert.Sector.Invariance

/-!
# Sector-multiplier certificates (paper Theorem 1 and the subsystem LMI (9))

A `SectorData n m s k` describes one LMI over `ζ = (x, w) ∈ ℝⁿ × ℝᵐ`:

* dynamics `ẋ = A x + B w`, where `w` collects every non-state signal: sector channels,
  bounded channels, disturbances and (for a subsystem) interface inputs;
* `s` sector constraints: channel `w (ch i)` against the linear form `qᵢ ⬝ ζ`, with
  `(w_{ch i} - ℓᵢ qᵢζ)(uᵢ qᵢζ - w_{ch i}) ≥ 0`, weighted by multipliers `τᵢ ≥ 0`;
* energy weights `γⱼ ≥ 0` on the bounded components of `w` (the paper's `α μⱼ / δⱼ²`);
* `k` supply-rate terms `σₖ (rₖ ⬝ ζ)²` for the interconnection (Proposition 1; none for the
  joint certificate).

`SectorCert D` is the checked LMI: `-[[AᵀP + PA + αP, PB], [BᵀP, 0]] + S ⪰ 0` with
`S = diag(0, γ) - Σ τᵢ Θᵢ + Σ σₖ rₖ rₖᵀ`, by a `DomWitness`. `SectorCert.supply` is LMI (8)/(9)
read as a pointwise inequality: wherever the sector constraints hold,

  `V̇ ≤ -α V + Σⱼ γⱼ wⱼ² + Σₖ σₖ (rₖ ⬝ ζ)²`.

Invariance then follows by `region_invariant` (Lemma 1) and output bounds by `LinearBoxDom`.
-/

namespace Dynacert.Sector

open Matrix Set Dynacert Dynacert.Linear

variable {n m s k : ℕ}

/-- Unit row on signal `j`. -/
def eW (j : Fin m) : Fin n ⊕ Fin m → ℚ := Sum.elim 0 (Pi.single j 1)

/-- Rows of the sector form `(w_j - ℓ q ζ)(u q ζ - w_j)`. -/
def secU (q : Fin n ⊕ Fin m → ℚ) (j : Fin m) (lo : ℚ) : Fin n ⊕ Fin m → ℚ :=
  eW j - lo • q

def secV (q : Fin n ⊕ Fin m → ℚ) (j : Fin m) (hi : ℚ) : Fin n ⊕ Fin m → ℚ :=
  hi • q - eW j

/-- The data of one sector LMI. -/
structure SectorData (n m s k : ℕ) where
  A : Matrix (Fin n) (Fin n) ℚ
  B : Matrix (Fin n) (Fin m) ℚ
  q : Fin s → Fin n ⊕ Fin m → ℚ
  ch : Fin s → Fin m
  lo : Fin s → ℚ
  hi : Fin s → ℚ
  γ : Fin m → ℚ
  σ : Fin k → ℚ
  r : Fin k → Fin n ⊕ Fin m → ℚ
  P : Matrix (Fin n) (Fin n) ℚ
  α : ℚ
  τ : Fin s → ℚ

namespace SectorData

/-- The supply form `S`. -/
def supply (D : SectorData n m s k) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ :=
  diagonal (Sum.elim 0 D.γ)
    + form (fun i => -D.τ i) (fun i => secU (D.q i) (D.ch i) (D.lo i))
        (fun i => secV (D.q i) (D.ch i) (D.hi i))
    + form D.σ D.r D.r

/-- The LMI matrix. -/
def lmi (D : SectorData n m s k) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ :=
  supplyLmi D.A D.B D.P D.α D.supply

end SectorData

/-- A checked sector LMI. Every field is decided by the kernel. -/
structure SectorCert (D : SectorData n m s k) where
  hα : 0 < D.α
  hτ : ∀ i, 0 ≤ D.τ i
  hγ : ∀ j, 0 ≤ D.γ j
  P_symm : D.Pᵀ = D.P
  lmi : DomWitness D.lmi

theorem dot_eW (j : Fin m) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    rv (eW j) ⬝ᵥ Sum.elim x w = w j := by
  simp [rv, eW, dotProduct, Pi.single_apply, apply_ite]

theorem dot_secU (q : Fin n ⊕ Fin m → ℚ) (j : Fin m) (lo : ℚ) (ζ : Fin n ⊕ Fin m → ℝ) :
    rv (secU q j lo) ⬝ᵥ ζ = rv (eW j) ⬝ᵥ ζ - (lo : ℝ) * (rv q ⬝ᵥ ζ) := by
  simp only [rv, secU, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_sub,
    Rat.cast_mul, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

theorem dot_secV (q : Fin n ⊕ Fin m → ℚ) (j : Fin m) (hi : ℚ) (ζ : Fin n ⊕ Fin m → ℝ) :
    rv (secV q j hi) ⬝ᵥ ζ = (hi : ℝ) * (rv q ⬝ᵥ ζ) - rv (eW j) ⬝ᵥ ζ := by
  simp only [rv, secV, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_sub,
    Rat.cast_mul, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

theorem quad_diag_energy (γ : Fin m → ℚ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    quad (toReal (diagonal (Sum.elim (0 : Fin n → ℚ) γ))) (Sum.elim x w) =
      ∑ j, (γ j : ℝ) * (w j * w j) := by
  have : toReal (diagonal (Sum.elim (0 : Fin n → ℚ) γ)) =
      diagonal (Sum.elim (0 : Fin n → ℝ) (fun j => (γ j : ℝ))) := by
    ext (a | a) (b | b) <;> simp [toReal, diagonal_apply]; split_ifs <;> simp
  rw [this]
  simp only [quad, dotProduct, mulVec_diagonal, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Pi.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, zero_add]
  exact Finset.sum_congr rfl fun j _ => by ring

namespace SectorCert

variable {D : SectorData n m s k}

/-- **Theorem 1 / LMI (9), pointwise.** Wherever the sector constraints hold,
`V̇ ≤ -α V + Σⱼ γⱼ wⱼ² + Σₖ σₖ (rₖ ⬝ ζ)²` along `ẋ = A x + B w`. -/
theorem supply (C : SectorCert D) (x : Fin n → ℝ) (w : Fin m → ℝ)
    (hsec : ∀ i, 0 ≤ (w (D.ch i) - (D.lo i : ℝ) * (rv (D.q i) ⬝ᵥ Sum.elim x w)) *
      ((D.hi i : ℝ) * (rv (D.q i) ⬝ᵥ Sum.elim x w) - w (D.ch i))) :
    quadDeriv (toReal D.P) x (toReal D.A *ᵥ x + toReal D.B *ᵥ w) ≤
      -(D.α : ℝ) * quad (toReal D.P) x + ∑ j, (D.γ j : ℝ) * (w j * w j) +
        ∑ i, (D.σ i : ℝ) * ((rv (D.r i) ⬝ᵥ Sum.elim x w) * (rv (D.r i) ⬝ᵥ Sum.elim x w)) := by
  have h := supply_le C.P_symm C.lmi x w
  have hS : quad (toReal D.supply) (Sum.elim x w) =
      ∑ j, (D.γ j : ℝ) * (w j * w j) +
      ∑ i, ((-D.τ i : ℚ) : ℝ) * ((rv (secU (D.q i) (D.ch i) (D.lo i)) ⬝ᵥ Sum.elim x w) *
        (rv (secV (D.q i) (D.ch i) (D.hi i)) ⬝ᵥ Sum.elim x w)) +
      ∑ i, (D.σ i : ℝ) * ((rv (D.r i) ⬝ᵥ Sum.elim x w) * (rv (D.r i) ⬝ᵥ Sum.elim x w)) := by
    rw [SectorData.supply, toReal, Matrix.map_add (Rat.castHom ℝ) (map_add _),
      Matrix.map_add (Rat.castHom ℝ) (map_add _), quad_add, quad_add, ← toReal, ← toReal,
      ← toReal, quad_diag_energy, quad_form, quad_form]
  have hneg : ∑ i, ((-D.τ i : ℚ) : ℝ) * ((rv (secU (D.q i) (D.ch i) (D.lo i)) ⬝ᵥ Sum.elim x w) *
      (rv (secV (D.q i) (D.ch i) (D.hi i)) ⬝ᵥ Sum.elim x w)) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    rw [dot_secU, dot_secV, dot_eW]
    refine sector_term_le ?_ (hsec i)
    have := C.hτ i
    push_cast; linarith [(by exact_mod_cast this : (0 : ℝ) ≤ D.τ i)]
  unfold SectorData.lmi at *
  linarith

end SectorCert

/-- Componentwise bounds give the energy budget (components with zero weight need no bound). -/
theorem energy_le {γ : Fin m → ℚ} {δ : Fin m → ℚ} (hγ : ∀ j, 0 ≤ γ j) {w : Fin m → ℝ}
    (hw : ∀ j, γ j ≠ 0 → |w j| ≤ δ j) :
    ∑ j, (γ j : ℝ) * (w j * w j) ≤ ((∑ j, γ j * (δ j * δ j) : ℚ) : ℝ) := by
  push_cast
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases h : γ j = 0
  · simp [h]
  · exact energy_term_le (by exact_mod_cast hγ j) (hw j h)

/-! ### Output bounds on an ellipsoid, by a dominance witness -/

/-- Certifies `|vᵀx| ≤ b` on `{xᵀPx ≤ c}` via `b² P - c vvᵀ ⪰ 0` (a `DomWitness`). -/
structure LinearBoxDom (P : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (v : Fin n → ℚ) (b : ℚ) where
  hc : 0 < c
  hb : 0 ≤ b
  psd : DomWitness (b ^ 2 • P - c • vecMulVec v v)

theorem LinearBoxDom.abs_le {P : Matrix (Fin n) (Fin n) ℚ} {c b : ℚ} {v : Fin n → ℚ}
    (B : LinearBoxDom P c v b) {x : Fin n → ℝ} (hx : quad (toReal P) x ≤ c) :
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

/-! ### Storage of a block-diagonal composition -/

/-- The block of `z` selected by an index map. -/
def sel {N : ℕ} (idx : Fin n → Fin N) (z : Fin N → ℝ) : Fin n → ℝ := fun i => z (idx i)

@[simp] theorem sel_zero {N : ℕ} (idx : Fin n → Fin N) : sel idx 0 = 0 := rfl

@[simp] theorem quad_zero' (P : Matrix (Fin n) (Fin n) ℝ) : quad P 0 = 0 := by simp [quad]

theorem sel_hasDerivWithinAt {N : ℕ} (idx : Fin n → Fin N) {z : ℝ → Fin N → ℝ}
    {z' : Fin N → ℝ} {S : Set ℝ} {t : ℝ} (h : HasDerivWithinAt z z' S t) :
    HasDerivWithinAt (fun τ => sel idx (z τ)) (sel idx z') S t := by
  rw [hasDerivWithinAt_pi] at h ⊢
  exact fun i => h (idx i)

theorem sel_continuousOn {N : ℕ} (idx : Fin n → Fin N) {z : ℝ → Fin N → ℝ} {S : Set ℝ}
    (h : ContinuousOn z S) : ContinuousOn (fun τ => sel idx (z τ)) S :=
  continuousOn_pi.mpr fun i => (continuousOn_pi.mp h) (idx i)

end Dynacert.Sector
