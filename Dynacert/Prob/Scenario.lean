import Mathlib

/-!
# Scenario bounds for Monte Carlo validation

A certificate bounds a certified output for *every* admissible scenario. Monte Carlo
simulation answers a different, probabilistic question, and this file proves the probability
theory it relies on, once, under the same axiom policy as the certificates.

Let `μ` be a probability distribution over scenarios `Ω` (parameters, disturbance and reference
signals), and `g : Ω → ℝ` a measurable performance, e.g. the peak of `|e(t)|` over a run.
Draw `N` scenarios i.i.d. from `μ`: the product measure `Measure.pi fun _ : Fin N => μ`.

* `scenario_bound` (order statistics / the scenario approach): the mass of scenarios that
  exceed every sample, `μ {x | ∀ i, g (ω i) < g x}`, is larger than `ε` with probability at
  most `(1 - ε) ^ N`. So the sample maximum is a `(1 - ε)`-quantile bound with confidence
  `1 - (1 - ε) ^ N`. No continuity or atomlessness assumption on the law of `g` is needed
  (bang-bang disturbances produce atoms).
* `zero_failure_bound`: if a set `S` (e.g. `{g ≤ b}`) has `μ Sᶜ ≥ ε`, all `N` samples land in
  `S` with probability at most `(1 - ε) ^ N`. A clean Monte Carlo run against a certified bound
  therefore bounds the probability of a disagreement between the simulator and the theorem.
* `one_sub_pow_le_exp`: `(1 - ε) ^ N ≤ exp (-ε N)`, so `N ≥ ln (1 / β) / ε` samples suffice
  for confidence `1 - β`.

Nothing here makes a simulation result a certificate: the sampled values are computed in
floating point by an untrusted simulator. These theorems state exactly what a Monte Carlo
report means *if* the samples are i.i.d. from `μ` and `g` is evaluated exactly.
-/

namespace Dynacert.Prob

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {g : Ω → ℝ}

/-- The tail `t ↦ μ {g > t}` of the law of `g`. -/
noncomputable def tail (μ : Measure Ω) (g : Ω → ℝ) (t : ℝ) : ℝ≥0∞ := μ {x | t < g x}

theorem tail_antitone : Antitone (tail μ g) :=
  fun _ _ hst => measure_mono fun _ hx => lt_of_le_of_lt hst hx

/-- The scenarios whose own tail mass exceeds `ε` have total mass at most `1 - ε`
(the strict tail of a sample is stochastically sub-uniform). -/
theorem measure_lt_tail_le [IsProbabilityMeasure μ] (hg : Measurable g) (ε : ℝ≥0∞) :
    μ {x | ε < tail μ g (g x)} ≤ 1 - ε := by
  rcases eq_or_ne ε 0 with rfl | hε0
  · simpa using prob_le_one
  by_cases hε1 : 1 ≤ ε
  · have : {x | ε < tail μ g (g x)} = ∅ :=
      eq_empty_of_forall_notMem fun x hx => absurd (hx.trans_le prob_le_one) (not_lt.2 hε1)
    simp [this]
  replace hε1 := not_le.1 hε1
  have hεpos : 0 < ε := pos_iff_ne_zero.2 hε0
  have hmeas : ∀ t : ℝ, MeasurableSet {x | t < g x} := fun t =>
    measurableSet_lt measurable_const hg
  set U := {t : ℝ | tail μ g t ≤ ε}
  -- `U` is nonempty: the tail vanishes at `+∞`.
  have hUne : U.Nonempty := by
    have hanti : Antitone fun n : ℕ => {x | (n : ℝ) < g x} :=
      fun m n hmn x (hx : (n : ℝ) < g x) => show (m : ℝ) < g x from
        lt_of_le_of_lt (by exact_mod_cast hmn) hx
    have hlim := tendsto_measure_iInter_atTop (μ := μ)
      (fun n : ℕ => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ n : ℕ, {x | (n : ℝ) < g x}) = ∅ := by
      ext x
      simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      exact exists_nat_ge (g x)
    rw [hempty, measure_empty] at hlim
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 ε hεpos).exists
    exact ⟨n, hn.le⟩
  -- `U` is bounded below: the tail tends to `1` at `-∞`.
  have hUbdd : BddBelow U := by
    have hmono : Monotone fun n : ℕ => {x | -(n : ℝ) < g x} :=
      fun m n hmn x (hx : -(m : ℝ) < g x) => show -(n : ℝ) < g x from
        lt_of_le_of_lt (by simpa using hmn) hx
    have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
    have huniv : (⋃ n : ℕ, {x | -(n : ℝ) < g x}) = univ := by
      ext x
      simp only [mem_iUnion, mem_setOf_eq, mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_gt (-g x)
      exact ⟨n, by linarith⟩
    rw [huniv, measure_univ] at hlim
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).1 ε hε1).exists
    refine ⟨-(n : ℝ), fun t ht => ?_⟩
    by_contra h
    replace h := not_le.1 h
    exact absurd ((tail_antitone h.le).trans ht) (not_le.2 hn)
  set q := sInf U
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  -- Below `q` the tail exceeds `ε`.
  have hbelow : ∀ t < q, ε < tail μ g t := fun t ht =>
    not_le.1 fun h => absurd (csInf_le hUbdd h) (not_le.2 ht)
  -- At `q` it does not: the tail is right-continuous.
  have hat : tail μ g q ≤ ε := by
    have hmono : Monotone fun n : ℕ => {x | q + 1 / ((n : ℝ) + 1) < g x} := by
      intro m n hmn x (hx : q + 1 / ((m : ℝ) + 1) < g x)
      change q + 1 / ((n : ℝ) + 1) < g x
      refine lt_of_le_of_lt ?_ hx
      gcongr
    have hun : {x | q < g x} = ⋃ n : ℕ, {x | q + 1 / ((n : ℝ) + 1) < g x} := by
      ext x
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        linarith [hpos n]
    change μ {x | q < g x} ≤ ε
    rw [hun, hmono.measure_iUnion]
    refine iSup_le fun n => ?_
    obtain ⟨u, hu, hlt⟩ := exists_lt_of_csInf_lt hUne (lt_add_of_pos_right q (hpos n))
    exact (tail_antitone hlt.le).trans hu
  -- So the bad set lies in `{g < q}`, which has mass at most `1 - ε`.
  have hsub : {x | ε < tail μ g (g x)} ⊆ {x | g x < q} := fun x hx =>
    not_le.1 fun h => absurd ((tail_antitone h).trans hat) (not_le.2 hx)
  refine (measure_mono hsub).trans ?_
  have hmono : Monotone fun n : ℕ => {x | g x ≤ q - 1 / ((n : ℝ) + 1)} := by
    intro m n hmn x (hx : g x ≤ q - 1 / ((m : ℝ) + 1))
    change g x ≤ q - 1 / ((n : ℝ) + 1)
    refine le_trans hx ?_
    gcongr
  have hun : {x | g x < q} = ⋃ n : ℕ, {x | g x ≤ q - 1 / ((n : ℝ) + 1)} := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      linarith [hpos n]
  rw [hun, hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  have hc : {x | g x ≤ q - 1 / ((n : ℝ) + 1)} = {x | q - 1 / ((n : ℝ) + 1) < g x}ᶜ := by
    ext x
    simp
  rw [hc, prob_compl_eq_one_sub (hmeas _)]
  exact tsub_le_tsub_left (hbelow _ (by linarith [hpos n])).le 1

/-- **Scenario bound.** For `N` i.i.d. samples from `μ`, the probability that the scenarios
exceeding every sample have mass more than `ε` is at most `(1 - ε) ^ N`. -/
theorem scenario_bound [IsProbabilityMeasure μ] (hg : Measurable g) (N : ℕ) (ε : ℝ≥0∞) :
    Measure.pi (fun _ : Fin N => μ) {ω | ε < μ {x | ∀ i, g (ω i) < g x}} ≤ (1 - ε) ^ N := by
  calc Measure.pi (fun _ : Fin N => μ) {ω | ε < μ {x | ∀ i, g (ω i) < g x}}
      ≤ Measure.pi (fun _ : Fin N => μ) (Set.pi univ fun _ => {x | ε < tail μ g (g x)}) := by
        refine measure_mono fun ω hω i _ => ?_
        exact lt_of_lt_of_le hω (measure_mono fun x hx => hx i)
    _ = μ {x | ε < tail μ g (g x)} ^ N := by simp [Measure.pi_pi]
    _ ≤ (1 - ε) ^ N := by gcongr; exact measure_lt_tail_le hg ε

/-- **Zero-failure bound.** If `S` misses at least mass `ε`, all `N` i.i.d. samples land in
`S` with probability at most `(1 - ε) ^ N`. -/
theorem zero_failure_bound [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S)
    (N : ℕ) {ε : ℝ≥0∞} (hε : ε ≤ μ Sᶜ) :
    Measure.pi (fun _ : Fin N => μ) {ω | ∀ i, ω i ∈ S} ≤ (1 - ε) ^ N := by
  have hset : {ω : Fin N → Ω | ∀ i, ω i ∈ S} = Set.pi univ fun _ => S := by
    ext ω
    simp
  have hμS : μ S ≤ 1 - ε := by
    rw [← compl_compl S, prob_compl_eq_one_sub hS.compl]
    exact tsub_le_tsub_left hε 1
  rw [hset, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr

/-- `(1 - ε) ^ N ≤ exp (-ε N)`: `N ≥ ln (1 / β) / ε` samples give confidence `1 - β`. -/
theorem one_sub_pow_le_exp {ε : ℝ} (h1 : ε ≤ 1) (N : ℕ) :
    (1 - ε) ^ N ≤ Real.exp (-ε * N) := by
  calc (1 - ε) ^ N ≤ Real.exp (-ε) ^ N := by
        gcongr
        · linarith
        · linarith [Real.add_one_le_exp (-ε)]
    _ = Real.exp (-ε * N) := by rw [← Real.exp_nat_mul]; ring_nf

end Dynacert.Prob
