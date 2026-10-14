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

## Next steps

- **Shrinking funnels** for nonzero initial errors:
  `V(t) ≤ V₀ e^{−αt} + (γ/α)(1 − e^{−αt})`, from `gronwallBound`, plus an `initial(...)`
  annotation.
- **Reference envelopes** (polytopic over reference bounds) for error dynamics that depend on
  the reference.
- **Time-varying `P(t)`** along one trajectory (proposal M6).
