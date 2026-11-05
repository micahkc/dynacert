import Dynacert.Linear.LTI

/-!
# Polyhedral invariant sets for LTI models

A polytope `S = {z | H z ≤ h}` is robustly invariant for `ż = A z + B w`, `|wⱼ| ≤ δⱼ`, when
there is a Metzler matrix `M` (nonnegative off the diagonal) with

```
H A = M H      and      M h + |H B| δ < 0   (componentwise, strict).
```

On a face (`Hᵢ z = hᵢ`, `Hⱼ z ≤ hⱼ`) the derivative of `Hᵢ z` is
`(M H z)ᵢ + (H B w)ᵢ ≤ (M h)ᵢ + (|H B| δ)ᵢ < 0`, where the Metzler condition handles the
off-diagonal terms. The strict margin closes a first-exit argument for right derivatives
(`finite_first_exit`), so no comparison lemma for `e^{Mt}` is needed. Output bounds
`|c ⬝ᵥ z| ≤ b` on `S` follow from LP duality (`PolyOutputCert`).

Every field of the certificates is a statement about rational data, meant to be proved by
`decide +kernel`.
-/

namespace Dynacert.Linear

open Matrix Set Filter Topology

/-! ### First exit for finitely many constraints -/

/-- **First exit, finitely many constraints, right derivatives.** If every `gᵢ` starts
`≤ 0`, and whenever all constraints hold and constraint `i` is active its right derivative is
negative, then all constraints hold on `[0, T]`. Proof: apply Mathlib's boundary comparison
to `φ = maxᵢ gᵢ`, whose right upper slope is bounded by the active derivatives. -/
theorem finite_first_exit {ι : Type*} [Finite ι] {g g' : ι → ℝ → ℝ} {T : ℝ}
    (hc : ∀ i, ContinuousOn (g i) (Icc 0 T))
    (hd : ∀ i, ∀ t ∈ Ico 0 T, HasDerivWithinAt (g i) (g' i t) (Ici t) t)
    (h0 : ∀ i, g i 0 ≤ 0)
    (hface : ∀ t ∈ Ico 0 T, (∀ j, g j t ≤ 0) → ∀ i, g i t = 0 → g' i t < 0) :
    ∀ t ∈ Icc 0 T, ∀ i, g i t ≤ 0 := by
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · intro t _ i; exact isEmptyElim i
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  set φ : ℝ → ℝ := fun t => Finset.univ.sup' hne (fun i => g i t) with hφ
  set f' : ℝ → ℝ := fun t =>
    Finset.univ.sup' hne (fun i => if g i t = φ t then g' i t else -1) with hf'
  have hle : ∀ t i, g i t ≤ φ t := fun t i => Finset.le_sup' (fun i => g i t) (Finset.mem_univ i)
  have hφc : ContinuousOn φ (Icc 0 T) :=
    ContinuousOn.finset_sup'_apply hne fun i _ => hc i
  have key : ∀ ⦃t⦄, t ∈ Icc 0 T → φ t ≤ (fun _ => (0 : ℝ)) t := by
    refine image_le_of_liminf_slope_right_lt_deriv_boundary' (f' := f') hφc ?_ ?_ continuousOn_const
      (fun _ _ => hasDerivWithinAt_const _ _ _) ?_
    · intro x hx r hr
      have hev : ∀ i, ∀ᶠ z in 𝓝[>] x, g i z < φ x + r * (z - x) := by
        intro i
        by_cases hi : g i x = φ x
        · have hgi : g' i x ≤ f' x := by
            have := Finset.le_sup' (fun i => if g i x = φ x then g' i x else -1)
              (Finset.mem_univ i)
            simpa [hf', hi] using this
          have hs := (hd i x hx).Ioi_of_Ici.limsup_slope_le' (lt_irrefl x) (hgi.trans_lt hr)
          filter_upwards [hs, self_mem_nhdsWithin] with z hz hzx
          have hpos : 0 < z - x := sub_pos.mpr hzx
          rw [slope_def_field, div_lt_iff₀ hpos] at hz
          linarith
        · have hlt : g i x < φ x := lt_of_le_of_ne (hle x i) hi
          have hcw : ContinuousWithinAt (fun z => g i z - r * (z - x)) (Ioi x) x :=
            ((hd i x hx).continuousWithinAt.mono Ioi_subset_Ici_self).sub
              (continuousWithinAt_const.mul (continuousWithinAt_id.sub continuousWithinAt_const))
          have hev := hcw.eventually_lt continuousWithinAt_const (by simpa using hlt)
          filter_upwards [hev] with z hz
          linarith
      have hall : ∀ᶠ z in 𝓝[>] x, ∀ i, g i z < φ x + r * (z - x) := eventually_all.2 hev
      refine (hall.and self_mem_nhdsWithin).frequently.mono ?_
      rintro z ⟨hz, hzx⟩
      have hpos : 0 < z - x := sub_pos.mpr hzx
      have hφz : φ z < φ x + r * (z - x) :=
        (Finset.sup'_lt_iff hne).2 fun i _ => hz i
      rw [slope_def_field, div_lt_iff₀ hpos]
      linarith
    · change φ 0 ≤ 0
      exact Finset.sup'_le hne _ fun i _ => h0 i
    · intro x hx hx0
      change φ x = 0 at hx0
      change f' x < 0
      refine (Finset.sup'_lt_iff hne).2 fun i _ => ?_
      split_ifs with hi
      · exact hface x hx (fun j => (hle x j).trans hx0.le) i (hi.trans hx0)
      · norm_num
  intro t ht i
  exact (hle t i).trans (key ht)

/-! ### Polyhedral RPI certificates -/

variable {n m k : ℕ}

/-- `|H B|`, entrywise. -/
def absMat {p q : ℕ} (X : Matrix (Fin p) (Fin q) ℚ) : Matrix (Fin p) (Fin q) ℚ :=
  X.map fun a => |a|

/-- The polytope `{z | H z ≤ h}` over `ℝ`. -/
def polytope (H : Matrix (Fin k) (Fin n) ℚ) (h : Fin k → ℚ) : Set (Fin n → ℝ) :=
  {z | ∀ i, (toReal H *ᵥ z) i ≤ (h i : ℝ)}

/-- A robust positively invariant polytope `{z | H z ≤ h}` for `ż = A z + B w`, `|wⱼ| ≤ δⱼ`:
a Metzler `M` with `H A = M H` and the strict margin `M h + |H B| δ < 0`. -/
structure PolyCert (Mdl : LTIModel n m) (k : ℕ) where
  H : Matrix (Fin k) (Fin n) ℚ
  h : Fin k → ℚ
  M : Matrix (Fin k) (Fin k) ℚ
  δ : Fin m → ℚ
  metzler : ∀ i j, i ≠ j → 0 ≤ M i j
  intertwine : H * Mdl.A = M * H
  margin : ∀ i, (M *ᵥ h) i + (absMat (H * Mdl.B) *ᵥ δ) i < 0

namespace PolyCert

variable {Mdl : LTIModel n m}

theorem toReal_mul {p q r : ℕ} (X : Matrix (Fin p) (Fin q) ℚ) (Y : Matrix (Fin q) (Fin r) ℚ) :
    toReal (X * Y) = toReal X * toReal Y := by
  rw [toReal, toReal, toReal, Matrix.map_mul]

/-- The face inequality: with all constraints satisfied, an active face has negative
derivative along every admissible disturbance. -/
theorem face_deriv_neg (C : PolyCert Mdl k) (z : Fin n → ℝ) (w : Fin m → ℝ)
    (hw : ∀ j, |w j| ≤ (C.δ j : ℝ)) (hz : z ∈ polytope C.H C.h) (i : Fin k)
    (hi : (toReal C.H *ᵥ z) i = (C.h i : ℝ)) :
    (toReal C.H *ᵥ Mdl.toSystem.f z w) i < 0 := by
  simp only [LTIModel.toSystem]
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, ← toReal_mul, ← toReal_mul, C.intertwine,
    toReal_mul, ← mulVec_mulVec]
  have hmarg : (((C.M *ᵥ C.h) i + (absMat (C.H * Mdl.B) *ᵥ C.δ) i : ℚ) : ℝ) < 0 := by
    exact_mod_cast C.margin i
  -- `(M (H z))ᵢ ≤ (M h)ᵢ`
  have h1 : (toReal C.M *ᵥ (toReal C.H *ᵥ z)) i ≤ ((C.M *ᵥ C.h) i : ℝ) := by
    simp only [mulVec, dotProduct, Rat.cast_sum, Rat.cast_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [toReal, map_apply, Rat.coe_castHom]
    by_cases hij : i = j
    · subst hij
      have := hi
      simp only [mulVec, dotProduct, toReal, map_apply, Rat.coe_castHom] at this
      rw [this]
    · have hM : (0 : ℝ) ≤ C.M i j := by exact_mod_cast C.metzler i j hij
      have hzj := hz j
      simp only [mulVec, dotProduct, toReal, map_apply, Rat.coe_castHom] at hzj
      exact mul_le_mul_of_nonneg_left hzj hM
  -- `(H B w)ᵢ ≤ (|H B| δ)ᵢ`
  have h2 : (toReal (C.H * Mdl.B) *ᵥ w) i ≤ ((absMat (C.H * Mdl.B) *ᵥ C.δ) i : ℝ) := by
    simp only [mulVec, dotProduct, Rat.cast_sum, Rat.cast_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [toReal, absMat, map_apply, Rat.coe_castHom, Rat.cast_abs]
    set a : ℝ := ((C.H * Mdl.B) i j : ℝ)
    calc a * w j ≤ |a * w j| := le_abs_self _
      _ = |a| * |w j| := abs_mul _ _
      _ ≤ |a| * C.δ j := mul_le_mul_of_nonneg_left (hw j) (abs_nonneg _)
  rw [Pi.add_apply]
  push_cast at hmarg
  linarith

/-- **Soundness.** Every solution with `|wⱼ| ≤ δⱼ` on `[0, T)` that starts in the polytope
stays in it on `[0, T]`. -/
theorem invariant (C : PolyCert Mdl k) {x : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ} {T : ℝ}
    (hx : Mdl.toSystem.IsSolution x w T) (hw : ∀ t ∈ Ico 0 T, ∀ j, |w t j| ≤ (C.δ j : ℝ))
    (h0 : x 0 ∈ polytope C.H C.h) : ∀ t ∈ Icc 0 T, x t ∈ polytope C.H C.h := by
  set g : Fin k → ℝ → ℝ := fun i t => (toReal C.H *ᵥ x t) i - C.h i
  set g' : Fin k → ℝ → ℝ := fun i t => (toReal C.H *ᵥ Mdl.toSystem.f (x t) (w t)) i
  have hcomp : ∀ i, ∀ t ∈ Ico 0 T, HasDerivWithinAt (g i) (g' i t) (Ici t) t := by
    intro i t ht
    have hci := hasDerivWithinAt_pi.1 (hx.deriv t ht)
    have hs : HasDerivWithinAt (fun τ => ∑ j, toReal C.H i j * x τ j)
        (∑ j, toReal C.H i j * Mdl.toSystem.f (x t) (w t) j) (Ici t) t :=
      HasDerivWithinAt.fun_sum fun j _ => (hci j).const_mul _
    exact hs.sub_const _
  have hcont : ∀ i, ContinuousOn (g i) (Icc 0 T) := by
    intro i
    have hxi := continuousOn_pi.1 hx.cont
    refine ContinuousOn.sub ?_ continuousOn_const
    simp only [mulVec, dotProduct]
    exact continuousOn_finset_sum _ fun j _ => continuousOn_const.mul (hxi j)
  have key := finite_first_exit (g := g) (g' := g') hcont hcomp
    (fun i => sub_nonpos.mpr (h0 i)) (by
      intro t ht hall i hi
      exact C.face_deriv_neg (x t) (w t) (hw t ht) (fun j => sub_nonpos.mp (hall j)) i
        (sub_eq_zero.mp hi))
  intro t ht i
  exact sub_nonpos.mp (key t ht i)

end PolyCert

/-! ### Sparse Metzler matrices

For many facets, a dense `M` makes the kernel check of `H A = M H` cubic in the facet count.
`SparsePolyCert` stores each row of `M` as a list of `(column, value)` entries and checks the
three conditions row by row; `toPolyCert` turns it into a `PolyCert`. -/

/-- The dense row of a sparse row: entries with the same column add up. -/
def spRow {k : ℕ} (l : List (Fin k × ℚ)) (j : Fin k) : ℚ :=
  (l.map fun e => if e.1 = j then e.2 else 0).sum

/-- `∑ⱼ (spRow l)ⱼ vⱼ` is the sparse sum over the entries. -/
theorem sum_spRow_mul {k : ℕ} (l : List (Fin k × ℚ)) (v : Fin k → ℚ) :
    ∑ j, spRow l j * v j = (l.map fun e => e.2 * v e.1).sum := by
  induction l with
  | nil => simp [spRow]
  | cons e l ih =>
    simp only [spRow, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]

theorem spRow_nonneg {k : ℕ} {l : List (Fin k × ℚ)} {i j : Fin k} (hij : i ≠ j)
    (h : ∀ e ∈ l, e.1 ≠ i → 0 ≤ e.2) : 0 ≤ spRow l j := by
  unfold spRow
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  split_ifs with hej
  · exact h e he (hej ▸ Ne.symm hij)
  · exact le_rfl

/-- A `PolyCert` with a sparse Metzler matrix, checked row by row. -/
structure SparsePolyCert (Mdl : LTIModel n m) (k : ℕ) where
  H : Matrix (Fin k) (Fin n) ℚ
  h : Fin k → ℚ
  Msp : Fin k → List (Fin k × ℚ)
  δ : Fin m → ℚ
  metzler : ∀ i, ∀ e ∈ Msp i, e.1 ≠ i → 0 ≤ e.2
  intertwine : ∀ i c, ((Msp i).map fun e => e.2 * H e.1 c).sum = (H * Mdl.A) i c
  margin : ∀ i, ((Msp i).map fun e => e.2 * h e.1).sum + (absMat (H * Mdl.B) *ᵥ δ) i < 0

namespace SparsePolyCert

variable {Mdl : LTIModel n m}

/-- The dense Metzler matrix. -/
def M (C : SparsePolyCert Mdl k) : Matrix (Fin k) (Fin k) ℚ := Matrix.of fun i => spRow (C.Msp i)

def toPolyCert (C : SparsePolyCert Mdl k) : PolyCert Mdl k where
  H := C.H
  h := C.h
  M := C.M
  δ := C.δ
  metzler i j hij := spRow_nonneg hij (C.metzler i)
  intertwine := by
    ext i c
    rw [C.intertwine i c |>.symm, Matrix.mul_apply]
    exact (sum_spRow_mul (C.Msp i) fun j => C.H j c).symm
  margin i := by
    have h := C.margin i
    rwa [← sum_spRow_mul] at h

end SparsePolyCert

/-! ### Output bounds by LP duality -/

/-- Certifies `|c ⬝ᵥ z| ≤ b` on `{z | H z ≤ h}`: multipliers `λ⁺, λ⁻ ≥ 0` with
`λ⁺ᵀ H = c`, `λ⁻ᵀ H = -c`, `λ⁺ᵀ h ≤ b`, `λ⁻ᵀ h ≤ b`. -/
structure PolyOutputCert (H : Matrix (Fin k) (Fin n) ℚ) (h : Fin k → ℚ) (c : Fin n → ℚ)
    (b : ℚ) where
  lp : Fin k → ℚ
  lm : Fin k → ℚ
  lp_nonneg : ∀ i, 0 ≤ lp i
  lm_nonneg : ∀ i, 0 ≤ lm i
  lp_eq : lp ᵥ* H = c
  lm_eq : lm ᵥ* H = -c
  lp_le : lp ⬝ᵥ h ≤ b
  lm_le : lm ⬝ᵥ h ≤ b

namespace PolyOutputCert

variable {H : Matrix (Fin k) (Fin n) ℚ} {h : Fin k → ℚ} {c : Fin n → ℚ} {b : ℚ}

theorem dual_le {l : Fin k → ℚ} {c' : Fin n → ℚ} (hl : ∀ i, 0 ≤ l i) (heq : l ᵥ* H = c')
    {z : Fin n → ℝ} (hz : z ∈ polytope H h) :
    (fun i => (c' i : ℝ)) ⬝ᵥ z ≤ ((l ⬝ᵥ h : ℚ) : ℝ) := by
  have hc : (fun i => (c' i : ℝ)) = (fun i => (l i : ℝ)) ᵥ* toReal H := by
    rw [← heq]; funext j; simp [vecMul, dotProduct, toReal]
  rw [hc, ← dotProduct_mulVec]
  simp only [dotProduct, Rat.cast_sum, Rat.cast_mul]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hz i) (by exact_mod_cast hl i)

theorem abs_le (B : PolyOutputCert H h c b) {z : Fin n → ℝ} (hz : z ∈ polytope H h) :
    |(fun i => (c i : ℝ)) ⬝ᵥ z| ≤ b := by
  have h1 := dual_le B.lp_nonneg B.lp_eq hz
  have h2 := dual_le B.lm_nonneg B.lm_eq hz
  have hb1 : ((B.lp ⬝ᵥ h : ℚ) : ℝ) ≤ b := by exact_mod_cast B.lp_le
  have hb2 : ((B.lm ⬝ᵥ h : ℚ) : ℝ) ≤ b := by exact_mod_cast B.lm_le
  have hneg : (fun i => ((-c) i : ℝ)) ⬝ᵥ z = -((fun i => (c i : ℝ)) ⬝ᵥ z) := by
    simp [dotProduct]
  rw [hneg] at h2
  exact _root_.abs_le.mpr ⟨by linarith, by linarith⟩

end PolyOutputCert

/-- Initial containment at a rational point reduces to a rational check. -/
theorem mem_polytope_cast {H : Matrix (Fin k) (Fin n) ℚ} {h : Fin k → ℚ} {v : Fin n → ℚ}
    (hv : ∀ i, (H *ᵥ v) i ≤ h i) : (fun i => (v i : ℝ)) ∈ polytope H h := by
  intro i
  have : (toReal H *ᵥ fun i => (v i : ℝ)) i = (((H *ᵥ v) i : ℚ) : ℝ) := by
    simp [mulVec, dotProduct, toReal]
  rw [this]
  exact_mod_cast hv i

end Dynacert.Linear
