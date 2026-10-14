import Dynacert.Core.System

/-!
# Layered certificates: mutual assume–guarantee by first exit

A model split into layers is certified layer by layer. Each layer treats the signals it reads
from the other layers as bounded disturbances (the *assumption* `s j ≤ b j`) and proves a strictly
smaller bound on the signals it owns (the *guarantee* `s i ≤ c i < b i`). The layers may depend
on each other in a loop; the circularity is closed by a first-exit argument: at the first time
any assumption could fail, every guarantee still holds strictly, and continuity extends the
assumptions a little further.

Only causality is required of a layer certificate: assumptions on `[0, τ)` give guarantees on
`[0, τ]`. dynacert's certificates have this form because their claims hold for every horizon
`T` (`System.IsSolution.mono` restricts a solution to a prefix).
-/

noncomputable section

namespace Dynacert.Compose

open Set Filter Topology

/-- **Assume–guarantee composition.** Finitely many continuous signals `s i` on `[0, T]`. If,
for every prefix `[0, τ]`, the bounds `s j ≤ b j` on `[0, τ)` imply the strictly tighter bounds
`s i ≤ c i` on `[0, τ]`, then `s i ≤ c i` holds on all of `[0, T]`. -/
theorem assume_guarantee {ι : Type*} [Finite ι] {s : ι → ℝ → ℝ} {b c : ι → ℝ} {T : ℝ}
    (hcont : ∀ i, ContinuousOn (s i) (Icc 0 T)) (hcb : ∀ i, c i < b i)
    (hguar : ∀ τ ∈ Icc 0 T, (∀ j, ∀ t ∈ Ico 0 τ, s j t ≤ b j) →
      ∀ i, ∀ t ∈ Icc 0 τ, s i t ≤ c i) :
    ∀ i, ∀ t ∈ Icc 0 T, s i t ≤ c i := by
  rcases lt_or_ge T 0 with hT | hT
  · intro i t ht
    exact absurd (ht.1.trans ht.2) (not_le.mpr hT)
  -- prefixes on which every assumption holds
  set S : Set ℝ := {τ | τ ∈ Icc 0 T ∧ ∀ j, ∀ t ∈ Ico 0 τ, s j t ≤ b j} with hS
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hT⟩, fun j t ht => absurd ht.2 (not_lt.mpr ht.1)⟩
  have hbdd : BddAbove S := ⟨T, fun τ hτ => hτ.1.2⟩
  set σ := sSup S with hσ
  have hσ0 : 0 ≤ σ := le_csSup hbdd h0S
  have hσT : σ ≤ T := csSup_le ⟨0, h0S⟩ fun τ hτ => hτ.1.2
  -- below σ the guarantees hold
  have hbelow : ∀ j, ∀ t ∈ Ico 0 σ, s j t ≤ c j := by
    intro j t ht
    obtain ⟨τ, hτS, htτ⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ ht.2
    exact hguar τ hτS.1 hτS.2 j t ⟨ht.1, htτ.le⟩
  have hσS : σ ∈ S := ⟨⟨hσ0, hσT⟩, fun j t ht => (hbelow j t ht).trans (hcb j).le⟩
  have hatσ := hguar σ hσS.1 hσS.2
  rcases hσT.lt_or_eq with hlt | heq
  · -- σ < T: the assumptions extend beyond σ, contradicting maximality
    exfalso
    have hev : ∀ᶠ t in 𝓝[Icc 0 T] σ, ∀ j, s j t < b j := by
      refine eventually_all.mpr fun j => ?_
      have hj := hcont j σ ⟨hσ0, hσT⟩
      exact hj.eventually (gt_mem_nhds ((hatσ j σ ⟨hσ0, le_rfl⟩).trans_lt (hcb j)))
    have hmem : Icc 0 T ∈ 𝓝[≥] σ :=
      mem_of_superset (Icc_mem_nhdsGE hlt) (Icc_subset_Icc_left hσ0)
    have hev' : ∀ᶠ t in 𝓝[≥] σ, ∀ j, s j t < b j := nhdsWithin_le_of_mem hmem hev
    obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset' hlt).mp hev'
    have hu : σ < u := hu
    set τ := min ((σ + u) / 2) T with hτ
    have hστ : σ < τ := lt_min (by linarith [hu]) hlt
    have hτS : τ ∈ S := by
      refine ⟨⟨hσ0.trans hστ.le, min_le_right _ _⟩, fun j t ht => ?_⟩
      rcases lt_or_ge t σ with h | h
      · exact (hbelow j t ⟨ht.1, h⟩).trans (hcb j).le
      · have htu : t < u := ht.2.trans_le ((min_le_left _ _).trans (by linarith [hu]))
        exact (hsub ⟨h, htu⟩ j).le
    exact absurd (le_csSup hbdd hτS) (not_le.mpr hστ)
  · intro i t ht
    exact hatσ i t ⟨ht.1, heq ▸ ht.2⟩

/-- A solution on `[0, T]` is a solution on every prefix `[0, τ]`. -/
theorem _root_.Dynacert.System.IsSolution.mono {n m : ℕ} {S : System n m}
    {x : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ} {T τ : ℝ} (h : S.IsSolution x w T) (hτ : τ ≤ T) :
    S.IsSolution x w τ :=
  ⟨h.cont.mono (Icc_subset_Icc_right hτ),
    fun t ht => h.deriv t ⟨ht.1, ht.2.trans_le hτ⟩⟩

end Dynacert.Compose
