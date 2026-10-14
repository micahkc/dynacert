import Dynacert.Core.Dissipation

/-!
# Systems and dissipation certificates


This layer is independent of how a certificate is found. A quadratic Lyapunov function from an
LMI is one instance (`Dynacert.Linear`); polynomial (SOS) storage functions, barrier functions,
and so on plug in by constructing a `DissipationCert`.
-/

namespace Dynacert

open Set

variable {n m : ℕ}

/-- A continuous-time system `ẋ = f(x, w)` with state `x ∈ ℝⁿ` and disturbance `w ∈ ℝᵐ`. -/
structure System (n m : ℕ) where
  f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → ℝ)

/-- `x` solves `S` on `[0, T]` under disturbance `w`: it is continuous on `[0, T]` and has the
prescribed right derivative on `[0, T)`. Using right derivatives admits piecewise-continuous,
right-continuous disturbances (steps, zero-order hold). -/
structure System.IsSolution (S : System n m) (x : ℝ → Fin n → ℝ) (w : ℝ → Fin m → ℝ)
    (T : ℝ) : Prop where
  cont : ContinuousOn x (Icc 0 T)
  deriv : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (S.f (x t) (w t)) (Ici t) t

section DirDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `DV x h` is the derivative of `V` at `x` in direction `h`, in the sense that the chain rule
holds along every curve. -/
def HasDirDeriv (V : E → ℝ) (DV : E → E → ℝ) : Prop :=
  ∀ (c : ℝ → E) (c' : E) (s : Set ℝ) (t : ℝ),
    HasDerivWithinAt c c' s t → HasDerivWithinAt (fun τ => V (c τ)) (DV (c t) c') s t

/-- Fréchet differentiability gives a directional derivative. -/
theorem hasDirDeriv_of_hasFDerivAt {V : E → ℝ} {DV : E → E →L[ℝ] ℝ}
    (h : ∀ x, HasFDerivAt V (DV x) x) : HasDirDeriv V (fun x v => DV x v) :=
  fun c _ _ t hc => (h (c t)).comp_hasDerivWithinAt t hc

end DirDeriv

/-- A dissipation certificate for `S` under disturbances in `W`: a continuous storage function
`V` with `V̇ ≤ -α V + γ` along the dynamics, for every admissible disturbance. -/
structure DissipationCert (S : System n m) (W : Set (Fin m → ℝ)) where
  V : (Fin n → ℝ) → ℝ
  DV : (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  α : ℝ
  γ : ℝ
  hα : 0 < α
  V_cont : Continuous V
  hDV : HasDirDeriv V DV
  dissipation : ∀ x, ∀ w ∈ W, DV x (S.f x w) ≤ -α * V x + γ

namespace DissipationCert

variable {S : System n m} {W : Set (Fin m → ℝ)}

/-- Main soundness theorem: along any solution driven by admissible disturbances,
`V(x t) ≤ max (V (x 0)) (γ / α)`. -/
theorem bound (C : DissipationCert S W) {x : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ} {T : ℝ}
    (hx : S.IsSolution x w T) (hw : ∀ t ∈ Ico 0 T, w t ∈ W) :
    ∀ t ∈ Icc 0 T, C.V (x t) ≤ max (C.V (x 0)) (C.γ / C.α) :=
  dissipation_bound C.hα (C.V_cont.comp_continuousOn hx.cont)
    (fun t ht => C.hDV _ _ _ _ (hx.deriv t ht))
    (fun t ht => C.dissipation _ _ (hw t ht))

/-- Invariance of a sublevel set: if `V (x 0) ≤ c` and `γ / α ≤ c`, the solution stays in
`{V ≤ c}` on `[0, T]`. -/
theorem invariant (C : DissipationCert S W) {x : ℝ → Fin n → ℝ} {w : ℝ → Fin m → ℝ} {T c : ℝ}
    (hx : S.IsSolution x w T) (hw : ∀ t ∈ Ico 0 T, w t ∈ W) (h0 : C.V (x 0) ≤ c)
    (hc : C.γ / C.α ≤ c) : ∀ t ∈ Icc 0 T, C.V (x t) ≤ c :=
  fun t ht => (C.bound hx hw t ht).trans (max_le h0 hc)

end DissipationCert

end Dynacert
