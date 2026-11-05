import Dynacert.Nonlinear.SOSFunnel
import Dynacert.Nonlinear.TrigBounds
import Dynacert.Linear.Scalar
import GNC.Analysis.BernsteinPolynomial

/-!
# Pieces for generated funnel links

A generated funnel certificate (`emit_funnel.py`) proves that a model's tracking error
`z = x - x*(t)` satisfies the hypotheses of `FunnelCert.funnel`, where the reference `x*` is a
polynomial in time (`GNC.PolynomialOrder.value`). It needs, per segment:

* the range of the reference polynomial on the segment, from exact Bernstein coefficients
  (`value_mem_of_bernstein`, via gnc's `BernsteinPolynomial.valid_sound`);
* a rational enclosure of `cos` on the band around that range (`cos_enclosure_rat`, a `Bool`
  check the kernel evaluates);

and at the end the output bound on the whole horizon (`FunnelCert.output_bound`).
-/

namespace Dynacert.Nonlinear

open Set Real Matrix Finset Dynacert Dynacert.Linear

/-! ### Reference range by Bernstein coefficients -/

/-- If the Bernstein coefficients `bc` of `cs - c` on `[a, b]` reconstruct it exactly and are at
most `r` in absolute value, the polynomial stays in `[c - r, c + r]` on `[a, b]`. -/
theorem value_mem_of_bernstein {cs : List ℚ} {a b c r : ℚ} {n : ℕ} {bc : Fin (n + 1) → ℚ}
    (hab : a < b)
    (hv : GNC.BernsteinPolynomial.valid (GNC.PolynomialBounds.subtract cs [c]) a b n bc)
    (hr : GNC.BernsteinPolynomial.bound n bc ≤ r) {t : ℝ} (ht : t ∈ Icc (a : ℝ) b) :
    GNC.PolynomialOrder.value cs t ∈ Icc ((c : ℝ) - r) ((c : ℝ) + r) := by
  have h := GNC.BernsteinPolynomial.valid_sound _ hab n bc hv ht
  rw [GNC.PolynomialOrder.value_subtract] at h
  have hc : GNC.PolynomialOrder.value [c] t = c := by
    simp [GNC.PolynomialOrder.value, GNC.Planning.PolynomialKernel.evaluate]
  rw [hc] at h
  have hr' : (GNC.BernsteinPolynomial.bound n bc : ℝ) ≤ r := by exact_mod_cast hr
  constructor <;> linarith [abs_le.mp (h.trans hr')]

/-! ### Rational `cos` enclosure -/

/-- The quartic upper bound of `cos_mem_Icc`, over `ℚ`. -/
def cosUpper (u v : ℚ) : ℚ :=
  if 0 < u then 1 - u ^ 2 / 2 + u ^ 4 / 24 else if v < 0 then 1 - v ^ 2 / 2 + v ^ 4 / 24 else 1

/-- The kernel's check that `[lo, hi]` encloses `cos` on `[u, v]`. -/
def cosEncOK (u v lo hi : ℚ) : Bool :=
  decide (max |u| |v| ≤ 3) && decide (lo ≤ 1 - (max |u| |v|) ^ 2 / 2) &&
    decide (cosUpper u v ≤ hi) && decide (u ≤ v) && decide (lo ≤ hi)

theorem cos_enclosure_rat {u v lo hi : ℚ} (h : cosEncOK u v lo hi = true) :
    ∀ ξ ∈ Icc (u : ℝ) v, (lo : ℝ) ≤ cos ξ ∧ cos ξ ≤ hi := by
  simp only [cosEncOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hM, hlo⟩, hhi⟩, -⟩, -⟩ := h
  intro ξ hξ
  have hMr : max |(u : ℝ)| |(v : ℝ)| = ((max |u| |v| : ℚ) : ℝ) := by push_cast; rfl
  have hπ : max |(u : ℝ)| |(v : ℝ)| ≤ π := by
    rw [hMr]; exact (show ((max |u| |v| : ℚ) : ℝ) ≤ 3 by exact_mod_cast hM).trans
      Real.pi_gt_three.le
  obtain ⟨h1, h2⟩ := cos_mem_Icc hξ hπ
  constructor
  · refine le_trans ?_ h1
    rw [hMr]; exact_mod_cast hlo
  · refine h2.trans ?_
    have : ((cosUpper u v : ℚ) : ℝ) ≤ hi := by exact_mod_cast hhi
    refine le_trans (le_of_eq ?_) this
    unfold cosUpper
    by_cases hu : 0 < u
    · have : (0 : ℝ) < u := by exact_mod_cast hu
      simp [hu, this]
    · have : ¬ (0 : ℝ) < u := by exact_mod_cast hu
      by_cases hv : v < 0
      · have : (v : ℝ) < 0 := by exact_mod_cast hv
        simp [*]
      · have : ¬ (v : ℝ) < 0 := by exact_mod_cast hv
        simp [*]

/-! ### Output bound over the horizon -/

namespace FunnelCert

variable {n m k p d S : ℕ}

/-- Every `t ∈ [T₀, T₀ + S h]` lies in some segment. -/
theorem exists_segment (C : FunnelCert n m k p d S) (hS : 0 < S) {T0 t : ℝ}
    (ht0 : T0 ≤ t) (ht1 : t ≤ T0 + S * C.h) :
    ∃ i : Fin S, T0 + (i : ℕ) * C.h ≤ t ∧ t ≤ T0 + ((i : ℕ) + 1) * C.h := by
  have hh : (0 : ℝ) < C.h := by exact_mod_cast C.hh
  set j := min (⌊(t - T0) / C.h⌋₊) (S - 1)
  have hj : j < S := by omega
  refine ⟨⟨j, hj⟩, ?_, ?_⟩
  · have h1 : (j : ℝ) ≤ (t - T0) / C.h :=
      (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le (div_nonneg (by linarith) hh.le))
    have := (le_div_iff₀ hh).mp h1
    simp only; linarith
  · simp only
    rcases lt_or_ge (⌊(t - T0) / C.h⌋₊) (S - 1) with hlt | hge
    · have hjv : j = ⌊(t - T0) / C.h⌋₊ := min_eq_left hlt.le
      have h2 := Nat.lt_floor_add_one ((t - T0) / C.h)
      rw [← hjv] at h2
      have := (div_lt_iff₀ hh).mp h2
      linarith
    · have hjv : j = S - 1 := min_eq_right hge
      have : ((j : ℕ) : ℝ) + 1 = S := by
        rw [hjv]; norm_cast; omega
      rw [this]; linarith

/-- **Output bound.** Under the hypotheses of `funnel`, a band row `l` is bounded by `bnd` on
`[T₀, min b (T₀ + S h)]` whenever `q_{i,l} (v₀ + β h (i+1)) ≤ bnd²` on every segment. -/
theorem output_bound (C : FunnelCert n m k p d S) (hS : 0 < S) {T0 b : ℝ}
    {x x' : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ}
    (hcont : ContinuousOn x (Icc T0 b))
    (hx : ∀ t ∈ Ico T0 b, HasDerivWithinAt x (x' t) (Ici t) t)
    (hemb : ∀ i : Fin S, ∀ t ∈ Ico T0 b, T0 + (i : ℕ) * C.h ≤ t → t < T0 + ((i : ℕ) + 1) * C.h →
      (∀ l, |(fun j => (C.cs l j : ℝ)) ⬝ᵥ x t| < C.ρ i l) →
      ∃ wt : Fin k → ℝ, (∀ j, 0 ≤ wt j) ∧ ∑ j, wt j = 1 ∧
        x' t = (∑ j, wt j • toReal (C.As i j)) *ᵥ x t + toReal C.B *ᵥ w t)
    (hw : ∀ t ∈ Ico T0 b, ∑ j, (C.γ j : ℝ) * (w t j * w t j) ≤ C.β)
    (h0 : quad (toReal (C.P ⟨0, hS⟩ ⟨0, by omega⟩)) (x T0) ≤ C.v0)
    (l : Fin p) {bnd : ℚ} (hbnd : 0 ≤ bnd)
    (hcheck : ∀ i : Fin S, C.q i l * (C.v0 + C.β * C.h * ((i : ℕ) + 1)) ≤ bnd ^ 2) :
    ∀ t ∈ Icc T0 b, t ≤ T0 + S * C.h → |(fun j => (C.cs l j : ℝ)) ⬝ᵥ x t| ≤ bnd := by
  intro t ht htS
  have hh : (0 : ℝ) < C.h := by exact_mod_cast C.hh
  obtain ⟨i, hi1, hi2⟩ := C.exists_segment hS ht.1 htS
  have hV := C.funnel hS hcont hx hemb hw h0 i t ht hi1 hi2
  have hs : (t - (T0 + (i : ℕ) * C.h)) / C.h ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hh.le, (div_le_one hh).mpr (by linarith)⟩
  have hsq := band_sq_le (C.band i l) (C.hq i l) hs (x t)
  have hq : (0 : ℝ) ≤ C.q i l := by exact_mod_cast (C.hq i l).le
  have hβ : (0 : ℝ) ≤ C.β := by exact_mod_cast C.hβ
  have hv : (C.v0 : ℝ) + C.β * (t - T0) ≤ C.v0 + C.β * C.h * ((i : ℕ) + 1) := by
    have : t - T0 ≤ C.h * ((i : ℕ) + 1) := by linarith
    nlinarith
  have hc : ((C.q i l * (C.v0 + C.β * C.h * ((i : ℕ) + 1)) : ℚ) : ℝ) ≤ ((bnd ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast hcheck i
  push_cast at hc
  have hfin : ((fun j => (C.cs l j : ℝ)) ⬝ᵥ x t) ^ 2 ≤ (bnd : ℝ) ^ 2 := by
    refine hsq.trans ?_
    calc (C.q i l : ℝ) * quad (pEval (coeffs (C.P i)) (2 * d + 1)
          ((t - (T0 + (i : ℕ) * C.h)) / C.h)) (x t)
        ≤ C.q i l * (C.v0 + C.β * (t - T0)) := mul_le_mul_of_nonneg_left (by simpa [Pm] using hV) hq
      _ ≤ C.q i l * (C.v0 + C.β * C.h * ((i : ℕ) + 1)) := mul_le_mul_of_nonneg_left hv hq
      _ ≤ (bnd : ℝ) ^ 2 := hc
  exact abs_le_of_sq_le_sq' hfin (by exact_mod_cast hbnd) |> fun h => abs_le.mpr h

end FunnelCert

end Dynacert.Nonlinear
