# Error-frame tubes

Every LTI certificate proves two theorems:

| Theorem | Statement |
|---|---|
| `<Model>.Cert.certified : Spec.Claim b` | the per-output bounds, `\|y(t)\| ≤ b` |
| `<Model>.Cert.tube` | under the same hypotheses, `z(t)ᵀ P z(t) ≤ level` on `[0, T]` |

Here `z = Cert.vec (x t) (u t)` is the error frame dynacert derives from the model, for
example `z = (x − x_ref, v − v_ref)`. The output bounds are corollaries of the tube:
`certified` begins with `have hV := tube …`.

## From the error frame to a tube

The frame is linear in states and references, `z = F_x x + F_u r`. `certified.json` records it
under `"frame"`. Given any reference trajectory `r(t)` that satisfies the declared derivative
relations, the physical state is confined to

```
X(t) = { x | (F_x x + F_u r(t))ᵀ P (F_x x + F_u r(t)) ≤ level } = x̄(t) ⊕ F_x⁻¹ E
```

with centre `x̄(t) = −F_x⁻¹ F_u r(t)` (the state at zero error) and `E` the certified ellipsoid.
The theorem holds for every admissible reference, so the cross-section is the same along any
trajectory: the set is carried along the reference without growing.

The extents of the tube in each state are exact projections of the ellipsoid,
`|x_i − x̄_i| ≤ √(level · (F_x⁻¹ P⁻¹ F_x⁻ᵀ)_ii)`.

## Usage

```
$ dynacert examples/ClosedLoop.mo tube --plot
Tube: ClosedLoop, error frame (e, ev), proved by ClosedLoop.Cert.tube
  set: zᵀ P z ≤ level; proved extents: |e| ≤ 0.8437, |ev| ≤ 1.431, |x − x̄| ≤ 0.8437, |v − v̄| ≤ 1.431
  30 runs on one random reference (rumoca): max zᵀPz/level = 0.7172
  adjoint worst case of |e|: max zᵀPz/level = 0.8363
  adjoint worst case of |ev|: max zᵀPz/level = 0.8334
  every run stays inside the proved tube (≤ 1)

$ dynacert examples/ClosedLoopUncertain.mo tube --reference path.csv   # columns: t,a_ref
```

- **Reference:** `--reference FILE.csv` gives the free reference signals (here `a_ref`).
  References with a declared derivative (`v_ref`, `x_ref`) are integrated from their start
  values, so the claim's `References` and `ReferenceStart` hypotheses hold. A CSV reference is
  simulated with the sympy export; the default random reference can use rumoca.
- **Worst cases:** the adjoint worst case of each output is computed on the same reference and
  shown in the figures.
- **Exit status:** 1 if any run leaves the tube.

## Interface (`dynacert.tube`)

`ErrorFrame` is the plug-in point for other frames:

| Member | Meaning |
|---|---|
| `names`, `P`, `level` | the certified set `{zᵀPz ≤ level}` |
| `states` | the physical states the frame reconstructs |
| `error(states, inputs) -> Z` | `z` along a run |
| `to_physical(ref, Z) -> {state: values}` | rows of `Z` mapped to physical states at one time |
| `bounds()` | the proved scalar extents |

`LinearFrame` implements it from a certificate sidecar. A Lie-group frame implements the same
methods with `ξ = log(Y⁻¹X)` and `to_physical` the exponential map: `p = p̄ + R̄ J_l(ξ_R) ξ_p`,
`R = R̄ Exp(ξ_R)`. Then `Tube.section` and the tube figures work unchanged; sections of a
nonlinear frame are drawn as the convex hull of mapped boundary samples.

## Funnels from an initial set

Annotating states with an initial interval,

```modelica
Real x(start = 0, fixed = true) annotation(__Dynacert(initialSet(min = -1, max = 1)));
```

replaces `x(0) = start` by `x(0) ∈ [min, max]` in the claim. (`initial` is a Modelica keyword
and cannot name a modifier, hence `initialSet`.) `Spec.lean` then defines

```lean
def InitialSet (p : Params) (s : States) : Prop :=
  (-1 : ℝ) ≤ s.x ∧ s.x ≤ (1 : ℝ) ∧ ... ∧ ∃ s₀ : States, Initial p s₀ ∧ s.w = s₀.w
```

(the annotated states in their intervals; every other state as in the model's `Initial`), and
`Claim`, `Cert.tube` and the new `Cert.funnel` assume `InitialSet p (x 0)`. Without any
`initialSet` annotation the generated files are unchanged.

**Initial bound.** In the error frame the initial set is `z₀ = c + G e`, `|eᵢ| ≤ ρᵢ` (`c` the
frame at the box centre, `G` the frame coefficients of the annotated states). Lean bounds the
storage over it by the rational number

```
boxBound P c G ρ = cᵀPc + 2 Σᵢ |(GᵀPc)ᵢ| ρᵢ + Σᵢⱼ |(GᵀPG)ᵢⱼ| ρᵢ ρⱼ  =: V₀
```

(`Dynacert.Linear.quad_le_boxBound`, one elementary lemma; the per-model fact
`boxBound P c₀ G₀ ρ₀ ≤ V0` is `decide +kernel`). It is the maximum of `V` over the box
vertices whenever one sign pattern aligns every term (always for one or two annotated states
around the origin), and a sound over-estimate otherwise. A convexity proof of "`V` ≤ max over
the 2ᵏ vertices" would be exact in general but needs a convex-hull argument per dimension; the
absolute-value bound keeps the Lean side to one lemma and the search side to a convex
expression (`cvxpy.abs`).

**Funnel.** `Dissipation.lean` weakens Mathlib's Grönwall bound to `max(V₀, γ/α)`. Before
weakening it is

```
zᵀPz ≤ ρ(t) = V₀ e^{−αt} + (γμ/α)(1 − e^{−αt})   on [0, T]
```

(`Dynacert.funnel_bound`, `ChannelCert.funnel`, `PolytopicCert.funnel` in
`Dynacert/Linear/Funnel.lean`). `Cert.funnel` states it with the explicit rational constants
`V₀`, `α` and `γμ/α = Σⱼγⱼδⱼ²/α` and `Real.exp`; the sidecar records them under `"funnel"`
(with `"initial"` for the box). The invariant level is `max(V₀, γμ/α)`, so the output bounds of
`Claim` cover the whole box.

**Search.** Minimizing the level alone balances `V₀` against `γμ/α`, which gives a flat funnel.
The search therefore first finds the smallest level `L*`, then minimizes the asymptotic level
`γμ/α` subject to `max(V₀, γμ/α) ≤ 1.1 L*` (`funnel_slack`): at most 10 % on the level (≈ 5 %
on the output bounds) for a funnel that shrinks to nearly the tube of a start at rest. For
`ClosedLoopInitial` (`x(0), v(0) ∈ [−1, 1]`): `V₀ = 4.383 → γμ/α = 2.185` with `α = 0.419`.

**Figures.** `tube.Funnel` (from the sidecar) gives `ρ(t)` and the ellipse scale
`√(ρ(t)/level)`; `Tube.level_at`, `Tube.section` and `Tube.funnel_halfwidths` follow the funnel.
`figures.tube`, `tube_phase` and `tube_margin` draw the shrinking funnel inside the tube, the
initial box, and runs from its corners (`Tube.funnel_runs`: the certified frame dynamics with
the disturbance that pushes `V` up fastest; illustration only):

```
$ dynacert examples/ClosedLoopInitial.mo lmi
$ dynacert examples/ClosedLoopInitial.mo tube --plot plots/
```

## Next steps

- **Reference envelopes** (polytopic over reference bounds) for error dynamics that depend on
  the reference.
- **Time-varying `P(t)`** along one trajectory (proposal M6).
