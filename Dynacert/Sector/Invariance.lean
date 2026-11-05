import Dynacert.Sector.LMI
import Dynacert.Compose.AssumeGuarantee

/-!
# Invariant ellipsoids from sector multipliers (paper Theorem 1, Lemma 1, Proposition 1)

* `region_invariant` (**Lemma 1**). Several storages `vᵢ` dissipate, `v̇ᵢ ≤ -αᵢ (vᵢ - cᵢ)`,
  only while the state is in a region, and the region contains the intersection of the larger
  sublevel sets `{vⱼ ≤ bⱼ}` with `cⱼ < bⱼ`. Then every `vᵢ ≤ cᵢ` for all time: the
  certified ellipsoids lie strictly inside the region, so the trajectory never reaches its
  boundary. The proof is the assume–guarantee first-exit argument
  (`Compose.assume_guarantee`) with Grönwall (`dissipation_bound`) on each prefix.
* `sector_nonneg`: a channel `p = δ q` with `δ ∈ [ℓ, u]` satisfies the sector constraint
  `(p - ℓ q)(u q - p) ≥ 0` that the multiplier `τ` of LMI (8) weights.
* `compose_storage` (**Proposition 1**). Subsystem storages whose supply rates sum to a
  non-positive form add up to a storage of the interconnection.
-/

namespace Dynacert.Sector

open Set Dynacert

/-- **Lemma 1 (regional invariance, several ellipsoids).** -/
theorem region_invariant {ι : Type*} [Finite ι] {v v' : ι → ℝ → ℝ} {α c b : ι → ℝ} {T : ℝ}
    (hα : ∀ i, 0 < α i) (hcb : ∀ i, c i < b i)
    (hcont : ∀ i, ContinuousOn (v i) (Icc 0 T))
    (hder : ∀ i, ∀ t ∈ Ico 0 T, HasDerivWithinAt (v i) (v' i t) (Ici t) t)
    (h0 : ∀ i, v i 0 ≤ c i)
    (hdiss : ∀ t ∈ Ico 0 T, (∀ j, v j t ≤ b j) → ∀ i, v' i t ≤ -α i * v i t + α i * c i) :
    ∀ i, ∀ t ∈ Icc 0 T, v i t ≤ c i := by
  refine Compose.assume_guarantee hcont hcb fun τ hτ hass i t ht => ?_
  have hsub : Ico 0 τ ⊆ Ico 0 T := Ico_subset_Ico_right hτ.2
  have hb := dissipation_bound (v := v i) (v' := v' i) (γ := α i * c i) (hα i)
    ((hcont i).mono (Icc_subset_Icc_right hτ.2)) (fun s hs => hder i s (hsub hs))
    (fun s hs => hdiss s (hsub hs) (fun j => hass j s hs) i) t ht
  rw [mul_div_cancel_left₀ _ (hα i).ne'] at hb
  exact hb.trans (max_le (h0 i) le_rfl)

/-- A sector channel: `p = δ q` with `δ ∈ [ℓ, u]` gives `(p - ℓ q)(u q - p) ≥ 0`. -/
theorem sector_nonneg {p q δ lo hi : ℝ} (hp : p = δ * q) (hδ : δ ∈ Icc lo hi) :
    0 ≤ (p - lo * q) * (hi * q - p) := by
  subst hp
  have : (δ * q - lo * q) * (hi * q - δ * q) = (δ - lo) * (hi - δ) * (q * q) := by ring
  rw [this]
  exact mul_nonneg (mul_nonneg (by linarith [hδ.1]) (by linarith [hδ.2])) (mul_self_nonneg q)

/-- A sector term weighted by `-τ ≤ 0` contributes at most `0` to the supply. -/
theorem sector_term_le {κ a b : ℝ} (hκ : κ ≤ 0) (hab : 0 ≤ a * b) : κ * (a * b) ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg hκ hab

/-- A bounded channel `|w| ≤ δ` weighted by `γ ≥ 0` contributes at most `γ δ²`. -/
theorem energy_term_le {γ w δ : ℝ} (hγ : 0 ≤ γ) (hw : |w| ≤ δ) : γ * (w * w) ≤ γ * (δ * δ) := by
  refine mul_le_mul_of_nonneg_left ?_ hγ
  have h0 : 0 ≤ |w| := abs_nonneg _
  rw [← abs_mul_abs_self w]
  exact mul_le_mul hw hw h0 (h0.trans hw)

/-- Interconnection supply: an interface signal `y` sent with rate `-σ` and received with rate
`ρ ≤ σ` contributes `(ρ - σ) y² ≤ 0`. -/
theorem supply_pair_le {ρ σ y : ℝ} (h : ρ ≤ σ) : ρ * (y * y) + -σ * (y * y) ≤ 0 := by
  nlinarith [mul_self_nonneg y]

/-- **Proposition 1 (composition).** Storages `Vₖ` with right derivatives `V'ₖ`,
`V'ₖ ≤ -α Vₖ + Eₖ + σₖ` and supply rates summing to `Σ σₖ ≤ 0`: the sum `V = Σ Vₖ` has right
derivative `Σ V'ₖ ≤ -α V + Σ Eₖ`. -/
theorem compose_storage {ι : Type*} [Fintype ι] {V V' E σ : ι → ℝ → ℝ} {α t : ℝ}
    (hV : ∀ k, HasDerivWithinAt (V k) (V' k t) (Ici t) t)
    (hdiss : ∀ k, V' k t ≤ -α * V k t + E k t + σ k t) (hσ : ∑ k, σ k t ≤ 0) :
    HasDerivWithinAt (fun s => ∑ k, V k s) (∑ k, V' k t) (Ici t) t ∧
      ∑ k, V' k t ≤ -α * ∑ k, V k t + ∑ k, E k t := by
  refine ⟨HasDerivWithinAt.fun_sum fun k _ => hV k, ?_⟩
  have := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hdiss k
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at this
  linarith

end Dynacert.Sector
