# Polyhedral invariant sets (fixed K)

`dynacert MODEL.mo certify polyhedral [--facets N]` (default 128) certifies the same `Spec.Claim` as `lmi`,
with a polytope instead of an ellipsoid (docs/architecture.md §4.2). The theorem is
`<Model>.PolyCert.certified : Spec.Claim b` in `certs/Certs/<Model>/PolyCert.lean`, with
the sidecar `polyhedral.json`; `certify` with no method runs it after `lmi` and keeps the
tighter bound for each output.

`assess()` stays cheap (about 0.3 s). It does the structural checks: LTI, no uncertain
parameters, a current lmi certificate whose link can be reused. It then runs a 16-facet probe
capped at 5 s. The full search runs only in `run()`.

## Math

The closed loop in error coordinates is `ż = A z + B w`, with `|wⱼ| ≤ δⱼ`. The polytope
`S = {z | H z ≤ h}` is invariant if there is a Metzler `M` (`Mᵢⱼ ≥ 0` for `i ≠ j`) with

```
H A = M H          M h + |H B| δ < 0   (componentwise, strict)
```

On face `i` (`Hᵢz = hᵢ`, `Hⱼz ≤ hⱼ`), the derivative of `Hᵢz` is `Σⱼ Mᵢⱼ Hⱼz + Hᵢ B w`.
The diagonal term equals `Mᵢᵢhᵢ`, each off-diagonal term is at most `Mᵢⱼhⱼ` (here `Mᵢⱼ ≥ 0` is
used), and `Hᵢ B w ≤ (|HB|δ)ᵢ`, so the derivative is negative. The strict margin closes a
first-exit argument for right derivatives. Output bounds come from LP duality: multipliers
`λ± ≥ 0` with `λ⁺ᵀH = c`, `λ⁻ᵀH = −c`, and `λ±ᵀh ≤ b` give `|c·z| ≤ b` on `S`.

By LP duality, row `i` of the cheapest `M` (`min Σⱼ Mᵢⱼhⱼ` subject to `Mᵢ H = Hᵢ A` and
`Mᵢⱼ ≥ 0` off the diagonal) has value equal to the largest derivative of `Hᵢz` over face `i`.
So "a Metzler `M` exists" is the same as Nagumo's condition on every face.

## Lean (`Dynacert/Linear/Polyhedral.lean`, proved once)

| Declaration | Statement |
|---|---|
| `finite_first_exit` | finitely many constraints `gᵢ`, continuous on `[0,T]` with right derivatives on `[0,T)`, starting `≤ 0`; if every active constraint has a negative derivative while all hold, all hold on `[0,T]` (Mathlib's boundary comparison applied to `maxᵢ gᵢ`) |
| `PolyCert Mdl k` | `H, h, M, δ` over ℚ; `metzler`, `intertwine : H * A = M * H`, `margin : ∀ i, (M *ᵥ h) i + (absMat (H * B) *ᵥ δ) i < 0` |
| `PolyCert.invariant` | `Mdl.toSystem.IsSolution x w T → (∀ t ∈ Ico 0 T, ∀ j, \|w t j\| ≤ δ j) → x 0 ∈ polytope H h → ∀ t ∈ Icc 0 T, x t ∈ polytope H h` |
| `SparsePolyCert` / `toPolyCert` | the same certificate with each row of `M` as a `(column, value)` list, checked row by row (the kernel check is about quadratic in the facet count instead of cubic) |
| `PolyOutputCert H h c b`, `.abs_le` | `λ⁺, λ⁻ ≥ 0`, `λ⁺ ᵥ* H = c`, `λ⁻ ᵥ* H = -c`, `λ± ⬝ᵥ h ≤ b` ⟹ `\|c ⬝ᵥ z\| ≤ b` on the polytope |
| `mem_polytope_cast` | containment of a rational point, checked over ℚ |

All of these depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The generated `PolyCert.lean` imports `Certs.<Model>.Cert` and reuses the LMI certificate's
link proof (`Cert.model`, `vec`, `dist`, `link`, `init`, `out<k>`). It adds the polytope data,
`cert : PolyCert Cert.model k` (each field proved by `decide +kernel`), the output certificates
`pout<k>`, `tube` (the error state stays in the polytope on `[0, T]`), and `certified`.

## Search (`python/dynacert/methods/polyhedral.py`, untrusted)

1. **Start.** Build a contractive polytope in real modal coordinates. Each real mode gives a
   slab. Each complex pair `σ ± iω` gives a regular `p`-gon, with `tan(π/p) < 0.7·|σ/ω|`.
   Add `±` each output row. The normals are rounded to rationals. The denominators are refined
   while the rounded modal polytope is not contractive, which happens with ill-conditioned
   eigenvectors.
2. **Policy iteration** (Howard) for the smallest offsets with these normals. Alternate
   `M ← row LPs(h)` and `h ← −M⁻¹(|HB|δ + ε)`. Because `M_new h ≤ M_old h = −c < 0`, every
   `M` stays Metzler and Hurwitz, and `h` decreases monotonically.
3. **Adaptive refinement** up to `--facets`. Each output's bound is `b = λᵀh = −λᵀM⁻¹c`, so
   `y = −M⁻ᵀλ ≥ 0` is its sensitivity to each face. The faces with the largest `y` are
   bisected with their neighbours, which are the facets in the support of their row of `M`.
   New normals start redundant, and the iteration resumes.
4. **Exact.** Remove redundant facets. Solve each row of `M` exactly on its LP basis, so that
   `HA = MH` holds over ℚ. Set `h = −M⁻¹(|HB|δ + 1.5ε)`, inflate it along `−M⁻¹𝟙` if `z₀`
   lies outside, and round it up. Re-check every Lean field with `Fraction`s.

## Results

All-time peak bounds, from `|w| ≤ 1` and `z(0) = 0`. "Exact" is the L1 norm of the impulse
response, `∫₀^∞ |c e^{As} B| ds`, which is the supremum over all disturbances and all time.
Search time is on a loaded machine. Lean time is `lake build` of `PolyCert.lean`.

| Model | Output | Exact (L1) | LMI | Poly 64 | Poly 96 | **Poly 128** | Poly 192 | Poly 256 |
|---|---|---|---|---|---|---|---|---|
| ClosedLoop | `e` | 0.7557 | 0.8438 | 0.9127 | 0.8575 | **0.8281** | 0.8031 | 0.80 |
| ClosedLoop | `ev` | 1.2831 | 1.4307 | 1.5835 | 1.4887 | **1.4219** | 1.3782 | 1.37 |
| ClosedLoopComposed | `e` | 0.1810 | 0.2024 | 0.2169 | 0.2054 | **0.2020** | 0.1926 | |
| ClosedLoopComposed | `ev` | 0.5847 | 0.6525 | 0.7275 | 0.6786 | **0.6659** | 0.6295 | |

| Facets | Search | Lean kernel check (`SparsePolyCert`) |
|---|---|---|
| 32 | 0.5 s | 5 s |
| 92 | 2–4 s | 16 s |
| 128 | 6–9 s | 28–60 s |
| 192 | 16–23 s | 60 s |
| 256 | 40 s | 110 s (dense layout; sparse is faster) |

The 128-facet certificates are committed:

- `ClosedLoop`: `|e| ≤ 0.828123`, `|ev| ≤ 1.42188`. Both are tighter than the LMI's.
- `ClosedLoopComposed`: `|e| ≤ 0.201992` is tighter than the LMI's. `|ev| ≤ 0.665945` is
  looser, so the portfolio keeps the LMI bound for `ev`.

**Convergence is slow, O(1/k) for k facets.** Nagumo's condition must hold on the whole of
each face, not only at the support point. Where the flow is tangent to the minimal RPI set,
for example at the `e`-extreme point of `ClosedLoop` (where `cB = 0`), each face costs `O(face
length)`. The method is exact in the limit, but on these examples it beats the ellipsoid only
from about 100–130 facets in 2-D.

**Higher dimensions** (the examples' LTI certificates, 3–7 states, 128 facets) are summarized
in the table below. The bounds are mostly looser than the LMI's, because a polytope with about
a hundred facets is coarse in 4-D. Lightly damped or nearly defective modes need large
polygons or fine rounding.

| Model (n) | Outputs | Exact (L1) | LMI | Poly 128 | Search |
|---|---|---|---|---|---|
| AircraftPitchShortPeriod (4) | 4 | 0.030, 0.031, 0.0102, 0.0298 | 0.0341, 0.0414, 0.0130, 0.0361 | 0.0311, 0.0468, 0.0127, 0.0405 | 14 s |
| BatteryPackThermalFan (4) | 2 | 1.962, 44.85 | 2.221, 50.64 | 2.284, 49.36 | 170 s |

In earlier, smaller runs, CNCFeedAxis (3 states, stiff, eigenvector condition number 2.5e5)
needed finer rounding and kept only 26 facets, all looser than the LMI. ChilledWaterSupplyPI
and FlexibleJointServo (4 states) were looser than the LMI at 48 facets. The sweep over all
examples was stopped to save time.

## Limits and open issues

- **v1 scope:** one LTI model with no uncertain parameters (`lti-channel`) and a fixed
  initial point. It needs a current `lmi` certificate whose link proof it reuses.
  - A polytopic/LPV version needs one `H` with a Metzler `M_σ` for each vertex `A_σ`
    (`H A_σ = M_σ H`). The Lean side would be a convex combination of the vertex face bounds.
  - Initial sets (`Spec.InitialSet`, the funnel agent's box) are not handled.
- **Tightness:** O(1/k), as above. A Lean proof of the Metzler comparison lemma would allow
  `≤ 0` instead of a strict margin, but that would not change the rate. The route to the exact
  value is the peak-to-peak gain (§4.4, M5).
- **Kernel cost** grows about quadratically with the sparse layout, because vector literals
  are `vecCons` chains. Keep `--facets` at a few hundred at most.
