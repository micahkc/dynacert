import Dynacert.Nonlinear.UnivariateSOS
import Dynacert.Linear.Polytopic

/-!
# Certified funnels with a time-varying quadratic storage

One segment `[a, a + h]` of the continuous-time funnel of Condie, Woodbury, Pant and Goppert
(*Continuous-time certified invariant funnels for nonlinear tracking systems via polytopic
embeddings and univariate sum-of-squares*, Theorem 1), for the finite-horizon level
`v(t) = v₀ + β (t - a)` (the paper's decay rate `α = 0`, Corollary 2), which is rational and so
checkable exactly.

The storage is `V(t) = x(t)ᵀ P(s) x(t)` with `s = (t - a)/h` and `P(s) = Σ_r s^r P_r`. On the
segment the error is embedded, while it stays in the band `|c_kᵀ x| < ρ_k`, in a polytope of
linear systems with vertices `A_j` (`ẋ = A x + B w`, `A ∈ conv {A_j}`). Two families of
matrix polynomials in `s` are certified nonnegative on `[0, 1]` by univariate SOS
(`SOSCert`):

* dissipation, at every vertex: `-[[Ṗ + A_jᵀP + PA_j, PB], [BᵀP, -diag γ]] ⪰ 0`
  (`dissCoeff`), so `V̇ ≤ Σⱼ γⱼ wⱼ²`;
* band, for every row: `[[P, c_k], [c_kᵀ, q_k]] ⪰ 0` (`bandCoeff`), so `(c_kᵀ x)² ≤ q_k V`.

With the margin `q_k (v₀ + β h) < ρ_k²`, the error cannot leave the band before the end of the
segment (first exit), and `V(t) ≤ v(t)` on the whole segment (`SegmentCert.funnel`). Segments
chain through `P_i(1) = P_{i+1}(0)`, which the generated certificate checks.
-/

namespace Dynacert.Nonlinear

open Matrix Finset Set Dynacert Dynacert.Linear

variable {n m : ℕ}

/-- Coefficients `P_r` from a finite list, zero from `K` on. -/
def coeffs {K : ℕ} (P : Fin K → Matrix (Fin n) (Fin n) ℚ) (r : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  if h : r < K then P ⟨r, h⟩ else 0

theorem coeffs_eq_zero {K : ℕ} (P : Fin K → Matrix (Fin n) (Fin n) ℚ) {r : ℕ} (hr : K ≤ r) :
    coeffs P r = 0 := by
  simp [coeffs, show ¬ r < K by omega]

theorem coeffs_symm {K : ℕ} {P : Fin K → Matrix (Fin n) (Fin n) ℚ} (hP : ∀ r, (P r)ᵀ = P r)
    (r : ℕ) : (coeffs P r)ᵀ = coeffs P r := by
  unfold coeffs; split_ifs <;> simp [hP]

/-- Disturbance rates, only on the constant coefficient. -/
def rateAt (γ : Fin m → ℚ) (ℓ : ℕ) : Fin m → ℚ := fun j => if ℓ = 0 then γ j else 0

/-- Coefficient `ℓ` (in `s`) of the negated dissipation matrix
`-[[Ṗ + AᵀP + PA, PB], [BᵀP, -diag γ]]`, with `Ṗ = h⁻¹ dP/ds`. -/
def dissCoeff (P : ℕ → Matrix (Fin n) (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin m) ℚ) (h : ℚ) (γ : Fin m → ℚ) (ℓ : ℕ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℚ :=
  channelLmi A B (P ℓ) 0 (rateAt γ ℓ) + fromBlocks (-((((ℓ : ℚ) + 1) / h) • P (ℓ + 1))) 0 0 0

/-- Coefficient `ℓ` of the band matrix `[[P, c], [cᵀ, q]]`. -/
def bandCoeff (P : ℕ → Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (q : ℚ) (ℓ : ℕ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℚ :=
  if ℓ = 0 then fromBlocks (P 0) (replicateCol (Fin 1) c) (replicateRow (Fin 1) c) (fun _ _ => q)
  else fromBlocks (P ℓ) 0 0 0

/-- `P(s) = Σ_{r < N} s^r P_r` over the reals. -/
noncomputable def pEval (P : ℕ → Matrix (Fin n) (Fin n) ℚ) (N : ℕ) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ r ∈ range N, s ^ r • toReal (P r)

/-- `dP/dt = h⁻¹ Σ_{ℓ < N} (ℓ+1) s^ℓ P_{ℓ+1}`. -/
noncomputable def pDot (P : ℕ → Matrix (Fin n) (Fin n) ℚ) (N : ℕ) (h : ℚ) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ ℓ ∈ range N, (s ^ ℓ * (((ℓ : ℝ) + 1) / h)) • toReal (P (ℓ + 1))

theorem quad_sum_smul {κ : Type*} [Fintype κ] (S : Finset ℕ) (c : ℕ → ℝ)
    (M : ℕ → Matrix κ κ ℝ) (x : κ → ℝ) :
    quad (∑ r ∈ S, c r • M r) x = ∑ r ∈ S, c r * quad (M r) x := by
  simp only [quad, Matrix.sum_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem quadDeriv_sum_smul (S : Finset ℕ) (c : ℕ → ℝ) (M : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x v : Fin n → ℝ) :
    quadDeriv (∑ r ∈ S, c r • M r) x v = ∑ r ∈ S, c r * quadDeriv (M r) x v := by
  simp only [quadDeriv, Matrix.sum_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul,
    smul_eq_mul, ← Finset.sum_add_distrib, mul_add]

/-- The quadratic form of one dissipation coefficient. -/
theorem quad_dissCoeff (P : ℕ → Matrix (Fin n) (Fin n) ℚ) (hP : ∀ r, (P r)ᵀ = P r)
    (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin m) ℚ) (h : ℚ) (γ : Fin m → ℚ)
    (ℓ : ℕ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    quad (toReal (dissCoeff P A B h γ ℓ)) (Sum.elim x w) =
      -quadDeriv (toReal (P ℓ)) x (toReal A *ᵥ x + toReal B *ᵥ w)
        + ∑ j, ((rateAt γ ℓ j : ℚ) : ℝ) * (w j * w j)
        - (((ℓ : ℝ) + 1) / h) * quad (toReal (P (ℓ + 1))) x := by
  have hPs : (toReal (P ℓ))ᵀ = toReal (P ℓ) := by rw [toReal, ← transpose_map, hP]
  have hsplit : toReal (dissCoeff P A B h γ ℓ) =
      channelLmi (toReal A) (toReal B) (toReal (P ℓ)) 0 (fun j => (rateAt γ ℓ j : ℝ))
        + fromBlocks (-((((ℓ : ℝ) + 1) / h) • toReal (P (ℓ + 1)))) 0 0 0 := by
    rw [dissCoeff, toReal, Matrix.map_add _ (map_add _), ← toReal, ← toReal, toReal_channelLmi]
    congr 1
    · simp
    · ext (i | i) (j | j) <;> simp [toReal, fromBlocks]
  rw [hsplit, quad, add_mulVec, dotProduct_add, ← quad, quad_channelLmi _ _ _ hPs]
  simp only [fromBlocks_mulVec, sumElim_dotProduct_sumElim, Sum.elim_comp_inl,
    Sum.elim_comp_inr, zero_mulVec, add_zero, dotProduct_zero, neg_mulVec, smul_mulVec,
    dotProduct_neg, dotProduct_smul, smul_eq_mul, quadDeriv]
  simp only [quad]
  ring

theorem sum_rateAt (γ : Fin m → ℚ) (N : ℕ) (s : ℝ) (w : Fin m → ℝ) :
    ∑ ℓ ∈ range (N + 1), s ^ ℓ * ∑ j, ((rateAt γ ℓ j : ℚ) : ℝ) * (w j * w j) =
      ∑ j, (γ j : ℝ) * (w j * w j) := by
  rw [Finset.sum_range_succ']
  simp [rateAt]

/-- **Vertex supply.** A checked dissipation SOS certificate gives, for `s ∈ [0, 1]`,
`xᵀṖx + d/dt (xᵀPx)` along the vertex dynamics at most the disturbance energy. -/
theorem vertex_supply {d : ℕ} {P : ℕ → Matrix (Fin n) (Fin n) ℚ} (hP : ∀ r, (P r)ᵀ = P r)
    {A : Matrix (Fin n) (Fin n) ℚ} {B : Matrix (Fin n) (Fin m) ℚ} {h : ℚ} {γ : Fin m → ℚ}
    (C : SOSCert d finSumFinEquiv (dissCoeff P A B h γ)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    quad (pDot P (2 * d + 1) h s) x
        + quadDeriv (pEval P (2 * d + 1) s) x (toReal A *ᵥ x + toReal B *ᵥ w) ≤
      ∑ j, (γ j : ℝ) * (w j * w j) := by
  have h0 := C.nonneg hs (Sum.elim x w)
  simp only [quad_dissCoeff P hP, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib] at h0
  rw [sum_rateAt] at h0
  rw [pDot, pEval, quad_sum_smul, quadDeriv_sum_smul]
  have e : ∑ ℓ ∈ range (2 * d + 1), s ^ ℓ * ((((ℓ : ℝ) + 1) / h) * quad (toReal (P (ℓ + 1))) x)
      = ∑ ℓ ∈ range (2 * d + 1), s ^ ℓ * (((ℓ : ℝ) + 1) / h) * quad (toReal (P (ℓ + 1))) x :=
    Finset.sum_congr rfl fun _ _ => by ring
  simp only [mul_neg, Finset.sum_neg_distrib] at h0
  linarith

/-- **Supply on the polytope.** Linear in the vertex, so it holds for every convex
combination. -/
theorem supply {d k : ℕ} {P : ℕ → Matrix (Fin n) (Fin n) ℚ} (hP : ∀ r, (P r)ᵀ = P r)
    {As : Fin k → Matrix (Fin n) (Fin n) ℚ} {B : Matrix (Fin n) (Fin m) ℚ} {h : ℚ}
    {γ : Fin m → ℚ} (C : ∀ j, SOSCert d finSumFinEquiv (dissCoeff P (As j) B h γ)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (wt : Fin k → ℝ) (hwt : ∀ j, 0 ≤ wt j) (hsum : ∑ j, wt j = 1)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    quad (pDot P (2 * d + 1) h s) x
        + quadDeriv (pEval P (2 * d + 1) s) x
            ((∑ j, wt j • toReal (As j)) *ᵥ x + toReal B *ᵥ w) ≤
      ∑ j, (γ j : ℝ) * (w j * w j) := by
  set Pe := pEval P (2 * d + 1) s
  have hcomb : (∑ j, wt j • toReal (As j)) *ᵥ x + toReal B *ᵥ w =
      ∑ j, wt j • (toReal (As j) *ᵥ x + toReal B *ᵥ w) := by
    rw [Matrix.sum_mulVec]
    simp only [smul_mulVec, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul]
  have hlin : ∀ S : Finset (Fin k), quadDeriv Pe x
      (∑ j ∈ S, wt j • (toReal (As j) *ᵥ x + toReal B *ᵥ w)) =
      ∑ j ∈ S, wt j * quadDeriv Pe x (toReal (As j) *ᵥ x + toReal B *ᵥ w) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [quadDeriv]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, PolytopicCert.quadDeriv_add,
        PolytopicCert.quadDeriv_smul, ih]
  rw [hcomb, hlin]
  have hb := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
    mul_le_mul_of_nonneg_left (vertex_supply hP (C j) hs x w) (hwt j)
  have hr : ∑ j, wt j * (∑ i, (γ i : ℝ) * (w i * w i)) = ∑ i, (γ i : ℝ) * (w i * w i) := by
    rw [← Finset.sum_mul, hsum, one_mul]
  have hq : ∑ j, wt j * quad (pDot P (2 * d + 1) h s) x = quad (pDot P (2 * d + 1) h s) x := by
    rw [← Finset.sum_mul, hsum, one_mul]
  simp only [mul_add, Finset.sum_add_distrib] at hb
  linarith

/-- The storage along a trajectory, `V(t) = x(t)ᵀ P((t - a)/h) x(t)`, has right derivative
`xᵀṖx + quadDeriv P x ẋ` (the top coefficient `P_N` must vanish). -/
theorem hasDerivWithinAt_storage {P : ℕ → Matrix (Fin n) (Fin n) ℚ} {N : ℕ} (hN : P N = 0)
    {h : ℚ} {a t : ℝ} {x : ℝ → Fin n → ℝ} {x' : Fin n → ℝ}
    (hx : HasDerivWithinAt x x' (Ici t) t) :
    HasDerivWithinAt (fun τ => quad (pEval P N ((τ - a) / h)) (x τ))
      (quad (pDot P N h ((t - a) / h)) (x t)
        + quadDeriv (pEval P N ((t - a) / h)) (x t) x') (Ici t) t := by
  set s := (t - a) / h
  have hterm : ∀ r ∈ range N, HasDerivWithinAt
      (fun τ => ((τ - a) / h) ^ r * quad (toReal (P r)) (x τ))
      ((r : ℝ) * s ^ (r - 1) * (1 / h) * quad (toReal (P r)) (x t)
        + s ^ r * quadDeriv (toReal (P r)) (x t) x') (Ici t) t := by
    intro r _
    have hs : HasDerivAt (fun τ : ℝ => ((τ - a) / h) ^ r) ((r : ℝ) * s ^ (r - 1) * (1 / h)) t :=
      by simpa using (((hasDerivAt_id t).sub_const a).div_const (h : ℝ)).pow r
    exact hs.hasDerivWithinAt.mul (quad_hasDirDeriv _ _ _ _ _ hx)
  have hsum := HasDerivWithinAt.fun_sum hterm
  have hf : (fun τ => quad (pEval P N ((τ - a) / h)) (x τ)) =
      fun τ => ∑ r ∈ range N, ((τ - a) / h) ^ r * quad (toReal (P r)) (x τ) := by
    funext τ; rw [pEval, quad_sum_smul]
  rw [hf]
  refine hsum.congr_deriv ?_
  rw [Finset.sum_add_distrib, pDot, pEval, quad_sum_smul, quadDeriv_sum_smul]
  congr 1
  set f : ℕ → ℝ := fun r => (r : ℝ) * s ^ (r - 1) * (1 / h) * quad (toReal (P r)) (x t)
  have hfN : f N = 0 := by simp [f, hN, quad, toReal]
  have h1 := Finset.sum_range_succ' f N
  rw [Finset.sum_range_succ, hfN, add_zero] at h1
  simp only [f, Nat.cast_zero, zero_mul, add_zero] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  ring

theorem quad_bandBlock (P0 : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (q a : ℝ)
    (x : Fin n → ℝ) :
    quad (fromBlocks P0 (replicateCol (Fin 1) c) (replicateRow (Fin 1) c) (fun _ _ => q))
        (Sum.elim x (fun _ => a)) = quad P0 x + 2 * a * (c ⬝ᵥ x) + q * a ^ 2 := by
  simp only [quad, fromBlocks_mulVec, sumElim_dotProduct_sumElim, Sum.elim_comp_inl,
    Sum.elim_comp_inr, dotProduct_add]
  have h1 : x ⬝ᵥ (replicateCol (Fin 1) c *ᵥ fun _ => a) = a * (c ⬝ᵥ x) := by
    simp [dotProduct, mulVec, replicateCol, Finset.mul_sum]; exact Finset.sum_congr rfl
      fun i _ => by ring
  have h2 : (fun _ : Fin 1 => a) ⬝ᵥ (replicateRow (Fin 1) c *ᵥ x) = a * (c ⬝ᵥ x) := by
    simp [dotProduct, mulVec, replicateRow]
  have h3 : (fun _ : Fin 1 => a) ⬝ᵥ ((fun _ _ => q : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun _ => a) =
      q * a ^ 2 := by
    simp [dotProduct, mulVec]; ring
  rw [h1, h2, h3]; ring

theorem toReal_bandCoeff (P : ℕ → Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (q : ℚ) (ℓ : ℕ) :
    toReal (bandCoeff P c q ℓ) =
      if ℓ = 0 then fromBlocks (toReal (P 0)) (replicateCol (Fin 1) (fun i => (c i : ℝ)))
        (replicateRow (Fin 1) (fun i => (c i : ℝ))) (fun _ _ => (q : ℝ))
      else fromBlocks (toReal (P ℓ)) 0 0 0 := by
  by_cases hℓ : ℓ = 0
  · subst hℓ
    simp only [bandCoeff, if_true, toReal]
    ext (i | i) (j | j) <;> simp [fromBlocks, replicateCol, replicateRow]
  · simp only [bandCoeff, hℓ, if_false, toReal]
    ext (i | i) (j | j) <;> simp [fromBlocks]

/-- **Band.** A checked SOS certificate of `[[P, c], [cᵀ, q]] ⪰ 0` on `[0, 1]` with `q > 0`
gives `(cᵀx)² ≤ q · xᵀP(s)x`. -/
theorem band_sq_le {d : ℕ} {P : ℕ → Matrix (Fin n) (Fin n) ℚ} {c : Fin n → ℚ} {q : ℚ}
    (C : SOSCert d finSumFinEquiv (bandCoeff P c q)) (hq : 0 < q) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (x : Fin n → ℝ) :
    ((fun i => (c i : ℝ)) ⬝ᵥ x) ^ 2 ≤ q * quad (pEval P (2 * d + 1) s) x := by
  set cr : Fin n → ℝ := fun i => (c i : ℝ)
  set y := cr ⬝ᵥ x
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set a : ℝ := -y / q
  have h0 := C.nonneg hs (Sum.elim x (fun _ => a))
  have hcoef : ∀ ℓ, quad (toReal (bandCoeff P c q ℓ)) (Sum.elim x (fun _ => a)) =
      quad (toReal (P ℓ)) x + if ℓ = 0 then 2 * a * y + q * a ^ 2 else 0 := by
    intro ℓ
    rw [toReal_bandCoeff]
    by_cases hℓ : ℓ = 0
    · subst hℓ; simp only [if_true]; rw [quad_bandBlock]; ring
    · simp only [hℓ, if_false, add_zero]
      simp [quad, fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [hcoef, mul_add, Finset.sum_add_distrib] at h0
  rw [Finset.sum_range_succ' (fun ℓ => s ^ ℓ * if ℓ = 0 then _ else _)] at h0
  simp only [Nat.succ_ne_zero, if_false, mul_zero, Finset.sum_const_zero, zero_add, pow_zero,
    one_mul, if_true] at h0
  rw [pEval, quad_sum_smul]
  have ha : 2 * a * y + q * a ^ 2 = -(y ^ 2) / q := by
    simp only [a]; field_simp; ring
  rw [ha] at h0
  have := mul_le_mul_of_nonneg_left h0 hq'.le
  rw [mul_zero, mul_add, mul_div_assoc', mul_neg, neg_div, mul_div_cancel_left₀ _ hq'.ne'] at this
  linarith

theorem continuousOn_storage {P : ℕ → Matrix (Fin n) (Fin n) ℚ} {N : ℕ} {h : ℚ} {a b : ℝ}
    {x : ℝ → Fin n → ℝ} (hcont : ContinuousOn x (Icc a b)) :
    ContinuousOn (fun τ => quad (pEval P N ((τ - a) / h)) (x τ)) (Icc a b) := by
  have hf : (fun τ => quad (pEval P N ((τ - a) / h)) (x τ)) =
      fun τ => ∑ r ∈ range N, ((τ - a) / h) ^ r * quad (toReal (P r)) (x τ) := by
    funext τ; rw [pEval, quad_sum_smul]
  rw [hf]
  exact continuousOn_finset_sum _ fun r _ =>
    (((continuous_id.sub continuous_const).div_const _).pow r).continuousOn.mul
      ((quad_continuous _).comp_continuousOn hcont)

/-- **Funnel on one segment** (Theorem 1 of the paper with `α = 0`). Let the error `x` have
right derivative `x'` on `[a, b) ⊆ [a, a + h)`, with `ẋ ∈ conv{A_j} x + B w` whenever it is
in the band `|c_iᵀ x| < ρ_i`, and disturbance energy `Σⱼ γⱼ wⱼ² ≤ budget ≤ β`. If the
dissipation and band SOS certificates check, `V(a) ≤ v₀` and `q_i (v₀ + β h) < ρ_i²`, then
`V(t) = x(t)ᵀ P((t - a)/h) x(t) ≤ v₀ + β (t - a)` on `[a, b]`: the error never reaches the edge
of the band, so the embedding is never used outside its domain. -/
theorem segment_funnel {d k p : ℕ} {P : ℕ → Matrix (Fin n) (Fin n) ℚ} (hP : ∀ r, (P r)ᵀ = P r)
    (hPN : P (2 * d + 1) = 0) {As : Fin k → Matrix (Fin n) (Fin n) ℚ}
    {B : Matrix (Fin n) (Fin m) ℚ} {h : ℚ} (hh : 0 < h) {γ : Fin m → ℚ}
    (Cd : ∀ j, SOSCert d finSumFinEquiv (dissCoeff P (As j) B h γ))
    {cs : Fin p → Fin n → ℚ} {q : Fin p → ℚ} (hq : ∀ i, 0 < q i)
    (Cb : ∀ i, SOSCert d finSumFinEquiv (bandCoeff P (cs i) (q i)))
    {x x' : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ} {a b v0 β budget : ℝ} {ρ : Fin p → ℝ}
    (hb : b ≤ a + h) (hcont : ContinuousOn x (Icc a b))
    (hx : ∀ t ∈ Ico a b, HasDerivWithinAt x (x' t) (Ici t) t)
    (hemb : ∀ t ∈ Ico a b, (∀ i, |(fun j => (cs i j : ℝ)) ⬝ᵥ x t| < ρ i) →
      ∃ wt : Fin k → ℝ, (∀ j, 0 ≤ wt j) ∧ ∑ j, wt j = 1 ∧
        x' t = (∑ j, wt j • toReal (As j)) *ᵥ x t + toReal B *ᵥ w t)
    (hw : ∀ t ∈ Ico a b, ∑ j, (γ j : ℝ) * (w t j * w t j) ≤ budget) (hβ : budget ≤ β)
    (hβ0 : 0 ≤ β) (hρ : ∀ i, 0 ≤ ρ i)
    (h0 : quad (pEval P (2 * d + 1) 0) (x a) ≤ v0)
    (hmargin : ∀ i, (q i : ℝ) * (v0 + β * h) < ρ i ^ 2) :
    ∀ t ∈ Icc a b, quad (pEval P (2 * d + 1) ((t - a) / h)) (x t) ≤ v0 + β * (t - a) := by
  set N := 2 * d + 1
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  set V : ℝ → ℝ := fun τ => quad (pEval P N ((τ - a) / h)) (x τ)
  set V' : ℝ → ℝ := fun τ => quad (pDot P N h ((τ - a) / h)) (x τ)
    + quadDeriv (pEval P N ((τ - a) / h)) (x τ) (x' τ)
  have hVc : ContinuousOn V (Icc a b) := continuousOn_storage hcont
  have hV' : ∀ t ∈ Ico a b, HasDerivWithinAt V (V' t) (Ici t) t :=
    fun t ht => hasDerivWithinAt_storage hPN (hx t ht)
  have hs : ∀ t ∈ Icc a b, (t - a) / (h : ℝ) ∈ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨div_nonneg (by linarith [ht.1]) hh'.le, (div_le_one hh').mpr (by linarith [ht.2])⟩
  -- for every small slack ε, `V ≤ v + ε (1 + (t - a))` by first exit
  have hslack : ∀ ε : ℝ, 0 < ε → (∀ i, (q i : ℝ) * (v0 + β * h + ε * (1 + h)) < ρ i ^ 2) →
      ∀ t ∈ Icc a b, V t ≤ v0 + β * (t - a) + ε * (1 + (t - a)) := by
    intro ε hε hεm
    have hB : ∀ τ, HasDerivAt (fun τ => v0 + β * (τ - a) + ε * (1 + (τ - a))) (β + ε) τ := by
      intro τ
      have := (((hasDerivAt_id τ).sub_const a).const_mul β).const_add v0 |>.add
        ((((hasDerivAt_id τ).sub_const a).const_add 1).const_mul ε)
      simpa using this
    refine image_le_of_deriv_right_lt_deriv_boundary hVc hV' ?_ hB ?_
    · have : V a = quad (pEval P N 0) (x a) := by simp [V]
      rw [this]; simp only [sub_self, mul_zero, add_zero, mul_one]; linarith
    · intro t ht hVB
      have hst := hs t (Ico_subset_Icc_self ht)
      have hband : ∀ i, |(fun j => (cs i j : ℝ)) ⬝ᵥ x t| < ρ i := by
        intro i
        have hsq := band_sq_le (Cb i) (hq i) hst (x t)
        have hVle : V t ≤ v0 + β * h + ε * (1 + h) := by
          rw [hVB]
          have h1 : t - a ≤ h := by linarith [ht.2]
          nlinarith [ht.1]
        have hqi : (0 : ℝ) < q i := by exact_mod_cast hq i
        have : ((fun j => (cs i j : ℝ)) ⬝ᵥ x t) ^ 2 < ρ i ^ 2 :=
          lt_of_le_of_lt hsq (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hVle hqi.le) (hεm i))
        exact abs_lt_of_sq_lt_sq this (hρ i)
      obtain ⟨wt, hwt, hsum, hrep⟩ := hemb t ht hband
      have hsup := supply hP Cd hst wt hwt hsum (x t) (w t)
      rw [← hrep] at hsup
      have := hw t ht
      show V' t < β + ε
      linarith
  -- let the slack go to zero
  intro t ht
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), 0 < ε ∧
      ∀ i, (q i : ℝ) * (v0 + β * h + ε * (1 + h)) < ρ i ^ 2 := by
    refine (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)).and ?_
    refine Filter.eventually_all.mpr fun i => ?_
    have hc : Filter.Tendsto (fun ε : ℝ => (q i : ℝ) * (v0 + β * h + ε * (1 + h)))
        (nhdsWithin 0 (Ioi 0)) (nhds ((q i : ℝ) * (v0 + β * h + 0 * (1 + h)))) :=
      ((continuous_const.mul (continuous_const.add
        (continuous_id.mul continuous_const))).tendsto 0).mono_left nhdsWithin_le_nhds
    simp only [zero_mul, add_zero] at hc
    exact hc.eventually_lt_const (hmargin i)
  have hlim : Filter.Tendsto (fun ε : ℝ => v0 + β * (t - a) + ε * (1 + (t - a)))
      (nhdsWithin 0 (Ioi 0)) (nhds (v0 + β * (t - a) + 0 * (1 + (t - a)))) :=
    ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  simp only [zero_mul, add_zero] at hlim
  exact ge_of_tendsto hlim (hev.mono fun ε hε => hslack ε hε.1 hε.2 t ht)

theorem pEval_zero {P : ℕ → Matrix (Fin n) (Fin n) ℚ} {N : ℕ} (hN : 0 < N) :
    pEval P N 0 = toReal (P 0) := by
  rw [pEval, Finset.sum_eq_single 0 (fun r _ hr => by simp [hr]) (fun h => absurd
    (Finset.mem_range.mpr hN) h)]
  simp

theorem pEval_one (P : ℕ → Matrix (Fin n) (Fin n) ℚ) (N : ℕ) :
    pEval P N 1 = toReal (∑ r ∈ range N, P r) := by
  ext i j
  simp [pEval, toReal, Matrix.sum_apply]

/-- A funnel certificate over `S` segments of length `h` starting at `T₀`: per segment `i`,
storage coefficients `P i`, polytope vertices `As i`, band data `q i`, `ρ i`, and the SOS
certificates; continuity `P_i(1) = P_{i+1}(0)`; the level `v(t) = v₀ + β (t - T₀)` with the
band margins. Every field is checked by the kernel. -/
structure FunnelCert (n m k p d S : ℕ) where
  h : ℚ
  hh : 0 < h
  As : Fin S → Fin k → Matrix (Fin n) (Fin n) ℚ
  B : Matrix (Fin n) (Fin m) ℚ
  γ : Fin m → ℚ
  P : Fin S → Fin (2 * d + 1) → Matrix (Fin n) (Fin n) ℚ
  P_symm : ∀ i r, (P i r)ᵀ = P i r
  cs : Fin p → Fin n → ℚ
  q : Fin S → Fin p → ℚ
  hq : ∀ i l, 0 < q i l
  ρ : Fin S → Fin p → ℚ
  hρ : ∀ i l, 0 ≤ ρ i l
  v0 : ℚ
  β : ℚ
  hβ : 0 ≤ β
  dissG : Fin S → Fin k → GramData ((d + 1) * (n + m)) (d * (n + m))
  dissOK : ∀ i j, (dissG i j).Valid d finSumFinEquiv (dissCoeff (coeffs (P i)) (As i j) B h γ)
  bandG : Fin S → Fin p → GramData ((d + 1) * (n + 1)) (d * (n + 1))
  bandOK : ∀ i l, (bandG i l).Valid d finSumFinEquiv (bandCoeff (coeffs (P i)) (cs l) (q i l))
  cont : ∀ i : Fin S, ∀ hi : (i : ℕ) + 1 < S,
    ∑ r : Fin (2 * d + 1), P i r = P ⟨i + 1, hi⟩ ⟨0, by omega⟩
  margin : ∀ i l, q i l * (v0 + β * h * ((i : ℕ) + 1)) < ρ i l ^ 2

namespace FunnelCert

variable {k p d S : ℕ}

/-- The dissipation SOS certificate of segment `i`, vertex `j`. -/
def diss (C : FunnelCert n m k p d S) (i : Fin S) (j : Fin k) :
    SOSCert d finSumFinEquiv (dissCoeff (coeffs (C.P i)) (C.As i j) C.B C.h C.γ) :=
  GramData.toCert (C.dissOK i j)

/-- The band SOS certificate of segment `i`, row `l`. -/
def band (C : FunnelCert n m k p d S) (i : Fin S) (l : Fin p) :
    SOSCert d finSumFinEquiv (bandCoeff (coeffs (C.P i)) (C.cs l) (C.q i l)) :=
  GramData.toCert (C.bandOK i l)

/-- The storage matrix of segment `i` at local time `s`. -/
noncomputable def Pm (C : FunnelCert n m k p d S) (i : Fin S) (s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  pEval (coeffs (C.P i)) (2 * d + 1) s

theorem coeffs_sum (C : FunnelCert n m k p d S) (i : Fin S) :
    ∑ r ∈ range (2 * d + 1), coeffs (C.P i) r = ∑ r : Fin (2 * d + 1), C.P i r := by
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun r _ => by simp [coeffs, r.isLt]

theorem Pm_cont (C : FunnelCert n m k p d S) (i : Fin S) (hi : (i : ℕ) + 1 < S) :
    C.Pm i 1 = C.Pm ⟨i + 1, hi⟩ 0 := by
  rw [Pm, Pm, pEval_one, pEval_zero (by omega), coeffs_sum, C.cont i hi]
  simp [coeffs]

/-- One segment of `funnel`: a bound at the segment's start propagates over the segment. -/
theorem segment_step (C : FunnelCert n m k p d S) {T0 b : ℝ}
    {x x' : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ}
    (hcont : ContinuousOn x (Icc T0 b))
    (hx : ∀ t ∈ Ico T0 b, HasDerivWithinAt x (x' t) (Ici t) t)
    (i : ℕ) (hi : i < S)
    (hemb : ∀ t ∈ Ico T0 b, T0 + i * C.h ≤ t → t < T0 + (i + 1) * C.h →
      (∀ l, |(fun j => (C.cs l j : ℝ)) ⬝ᵥ x t| < C.ρ ⟨i, hi⟩ l) →
      ∃ wt : Fin k → ℝ, (∀ j, 0 ≤ wt j) ∧ ∑ j, wt j = 1 ∧
        x' t = (∑ j, wt j • toReal (C.As ⟨i, hi⟩ j)) *ᵥ x t + toReal C.B *ᵥ w t)
    (hw : ∀ t ∈ Ico T0 b, ∑ j, (C.γ j : ℝ) * (w t j * w t j) ≤ C.β)
    (hbase : T0 + i * C.h ≤ b →
      quad (C.Pm ⟨i, hi⟩ 0) (x (T0 + i * C.h)) ≤ C.v0 + C.β * (i * C.h)) :
    ∀ t ∈ Icc T0 b, T0 + i * C.h ≤ t → t ≤ T0 + (i + 1) * C.h →
      quad (C.Pm ⟨i, hi⟩ ((t - (T0 + i * C.h)) / C.h)) (x t) ≤ C.v0 + C.β * (t - T0) := by
  have hh : (0 : ℝ) < C.h := by exact_mod_cast C.hh
  intro t ht hat htb
  set a := T0 + i * C.h
  set b' := min b (T0 + (i + 1) * C.h)
  have hTa : T0 ≤ a := by have : (0 : ℝ) ≤ i * C.h := by positivity
                          linarith
  have hab : a ≤ b := hat.trans ht.2
  have hsub : Icc a b' ⊆ Icc T0 b := fun τ hτ => ⟨hTa.trans hτ.1, hτ.2.trans (min_le_left _ _)⟩
  have hsubo : Ico a b' ⊆ Ico T0 b := fun τ hτ =>
    ⟨hTa.trans hτ.1, lt_of_lt_of_le hτ.2 (min_le_left _ _)⟩
  have hseg := segment_funnel (P := coeffs (C.P ⟨i, hi⟩)) (coeffs_symm (C.P_symm ⟨i, hi⟩))
    (coeffs_eq_zero _ le_rfl) C.hh (C.diss ⟨i, hi⟩) (C.hq ⟨i, hi⟩) (C.band ⟨i, hi⟩)
    (x := x) (x' := x') (w := w) (a := a) (b := b') (v0 := C.v0 + C.β * (i * C.h))
    (β := C.β) (budget := C.β) (ρ := fun l => (C.ρ ⟨i, hi⟩ l : ℝ))
    (by simp only [b']; have := min_le_right b (T0 + (i + 1) * C.h); simp only [a]; linarith)
    (hcont.mono hsub) (fun τ hτ => hx τ (hsubo hτ))
    (fun τ hτ hband => hemb τ (hsubo hτ) hτ.1 (lt_of_lt_of_le hτ.2 (min_le_right _ _)) hband)
    (fun τ hτ => hw τ (hsubo hτ)) le_rfl (by exact_mod_cast C.hβ)
    (fun l => by simp only; exact_mod_cast C.hρ ⟨i, hi⟩ l)
    (by have := hbase hab; rwa [Pm] at this)
    (fun l => by
      have hm := C.margin ⟨i, hi⟩ l
      have : ((C.q ⟨i, hi⟩ l * (C.v0 + C.β * C.h * ((i : ℕ) + 1)) : ℚ) : ℝ) <
          ((C.ρ ⟨i, hi⟩ l ^ 2 : ℚ) : ℝ) := by exact_mod_cast hm
      push_cast at this
      simp only at this ⊢
      nlinarith [this])
  have := hseg t ⟨hat, le_min ht.2 htb⟩
  rw [Pm]
  simp only [a] at this
  nlinarith [this]

/-- **Certified funnel** (Theorem 1 with `α = 0`, chained over the segments). If the error
`x` starts with `V(T₀) ≤ v₀`, its derivative lies in segment `i`'s polytope while it is in
segment `i`'s band, and the disturbance energy is at most `β`, then on every segment
`V(t) ≤ v₀ + β (t - T₀)`. -/
theorem funnel (C : FunnelCert n m k p d S) (hS : 0 < S) {T0 b : ℝ}
    {x x' : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ}
    (hcont : ContinuousOn x (Icc T0 b))
    (hx : ∀ t ∈ Ico T0 b, HasDerivWithinAt x (x' t) (Ici t) t)
    (hemb : ∀ i : Fin S, ∀ t ∈ Ico T0 b, T0 + (i : ℕ) * C.h ≤ t → t < T0 + ((i : ℕ) + 1) * C.h →
      (∀ l, |(fun j => (C.cs l j : ℝ)) ⬝ᵥ x t| < C.ρ i l) →
      ∃ wt : Fin k → ℝ, (∀ j, 0 ≤ wt j) ∧ ∑ j, wt j = 1 ∧
        x' t = (∑ j, wt j • toReal (C.As i j)) *ᵥ x t + toReal C.B *ᵥ w t)
    (hw : ∀ t ∈ Ico T0 b, ∑ j, (C.γ j : ℝ) * (w t j * w t j) ≤ C.β)
    (h0 : quad (toReal (C.P ⟨0, hS⟩ ⟨0, by omega⟩)) (x T0) ≤ C.v0) :
    ∀ i : Fin S, ∀ t ∈ Icc T0 b, T0 + (i : ℕ) * C.h ≤ t → t ≤ T0 + ((i : ℕ) + 1) * C.h →
      quad (C.Pm i ((t - (T0 + (i : ℕ) * C.h)) / C.h)) (x t) ≤ C.v0 + C.β * (t - T0) := by
  have hh : (0 : ℝ) < C.h := by exact_mod_cast C.hh
  suffices H : ∀ (i : ℕ) (hi : i < S), ∀ t ∈ Icc T0 b, T0 + i * C.h ≤ t →
      t ≤ T0 + (i + 1) * C.h →
      quad (C.Pm ⟨i, hi⟩ ((t - (T0 + i * C.h)) / C.h)) (x t) ≤ C.v0 + C.β * (t - T0) from
    fun i => H i i.2
  intro i
  induction i with
  | zero =>
    intro hi
    refine C.segment_step hcont hx 0 hi (fun t ht h1 h2 hb => hemb ⟨0, hi⟩ t ht h1 h2 hb) hw ?_
    intro _
    rw [Pm, pEval_zero (by omega)]
    simpa [coeffs] using h0
  | succ i ih =>
    intro hi
    refine C.segment_step hcont hx (i + 1) hi
      (fun t ht h1 h2 hb => hemb ⟨i + 1, hi⟩ t ht (by exact_mod_cast h1) (by exact_mod_cast h2) hb)
      hw ?_
    intro hb
    have hi' : i < S := by omega
    have hT0 : T0 ≤ T0 + ((i + 1 : ℕ) : ℝ) * C.h := by
      have : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) * C.h := by positivity
      linarith
    have hprev := ih hi' (T0 + ((i + 1 : ℕ) : ℝ) * C.h) ⟨hT0, hb⟩ (by push_cast; nlinarith)
      (by push_cast; linarith)
    have hs : (T0 + ((i + 1 : ℕ) : ℝ) * C.h - (T0 + (i : ℝ) * C.h)) / C.h = 1 := by
      push_cast; field_simp; ring
    rw [hs, C.Pm_cont ⟨i, hi'⟩ hi] at hprev
    push_cast at hprev ⊢
    linarith


end FunnelCert

end Dynacert.Nonlinear
