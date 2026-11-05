# Switched linear models (`if`-expressions)

The `switched` certify method proves peak bounds for Modelica models whose equations contain
`if`-expressions that switch, in continuous time, between linear modes:

```modelica
der(z) = if abs(u) > ulim then -lam*z else x;                        // anti-windup
u = -(if abs(z) > zLoad then kpHigh else kpLow)*w - ki*z;             // gain schedule
m*der(v) = -k*x - (if v > 0 then cReb else cComp)*v + f;              // two-stage damper
```

```
dynacert examples/switching/AsymmetricDamper.mo                # assess: modes, candidate bounds
dynacert examples/switching/AsymmetricDamper.mo certify switched
dynacert examples/switching/AsymmetricDamper.mo validate --n 200
```

It writes `certs/Certs/<Model>/SwitchedCert.lean`, proving

* `<Model>.SwitchedCert.certified : Spec.Claim b`, the claim of the shared `Spec.lean`, and
* `<Model>.SwitchedCert.tube`: the error-frame state stays in `{zᵀPz ≤ level}` on `[0, T]`
  (with `initialSet` annotations also `<Model>.SwitchedCert.funnel`),

plus the sidecar `switched.json` (modes, their conditions as text, `A` per mode, `P`, level,
bounds as `p/q`, theorem, axioms, `source_hash`). The theorems use only `propext`,
`Classical.choice` and `Quot.sound`; every numeric fact is checked by `decide +kernel`.

## Semantics: what the claim says

`Spec.lean` is the same file the `lmi` method would write: `emit_lti.emit_spec`, unchanged.
Its hypothesis `IsSolutionOn p u x y T` is rumoca's faithful transcription of the model's own
equations, `if`-expressions included, for example

```lean
def Equations (t : ℝ) (p : Params) (u : Inputs) (x dx : States) (y : Algebraics) : Prop :=
  y.u = -(p.kp * x.x) - p.ki * x.z
  ∧ dx.x = -(p.a * x.x) + y.u + u.d
  ∧ dx.z = (if |y.u| > p.ulim then -(p.lam * x.z) else x.x)
```

so the claim is about **classical solutions with right derivatives**: states continuous on
`[0, T]`, with a right derivative at every `t ∈ [0, T)` at which the equations hold, the `if`
evaluated at that instant. Every such solution is covered, whatever its switching times
(typically finitely many transversal crossings of the switching surfaces on `[0, T]`).

**Sliding motions are not classical solutions.** When the vector fields on the two sides of a
switching surface both point into it, the state slides along the surface, and at almost no
instant on the surface does the equation hold with either branch. Such a trajectory is not an
`IsSolutionOn`, and the claim says nothing about it. The common-`P` certificate would still
hold for it: a Filippov solution has `ż ∈ co{A_m z + B w}` (convex combinations of the modes
active near the surface), and `PolytopicCert` already proves the bound for every measurable
convex combination. Relaxing the transcription (and so the claim) to Filippov semantics is
future work: it needs a Filippov `IsSolutionOn` in rumoca's export and a measurable-selection
argument, not a new certificate.

## How it works

1. **Switches and modes** ([switched.py](../python/dynacert/switched.py)). The `if`-chains are
   read from rumoca's Lean `Equations` text and matched, equation by equation, with the
   sympy `Piecewise` atoms of the same DAE. If-expressions with the same condition chain form
   one *switch* (they always pick the same branch); a *mode* picks one branch of every switch,
   so `k` two-branch switches give `2^k` modes (a chain `if … elseif … else` has three
   branches). Every combination is kept, including ones whose conditions are jointly
   unsatisfiable (they only add vertices, which is conservative).
2. **One frame for all modes.** For each mode, a copy of the model has every `if` replaced by
   that mode's branch: same equation count and order, so Lean conjunct indices still match.
   `pipeline.linear_problem` runs on each copy. The modes must share coordinates, the
   disturbance matrix `B`, the state outputs and the initial data; only `A` may differ.
   Algebraic outputs may depend on the mode (`u` in a gain-scheduled loop): each mode has its
   own row and the bound is the largest per-mode bound.
3. **Search** (untrusted). `methods.lti.certify_polytopic(As=[A_m …], B, …)`: one `P` with the
   per-channel dissipation LMI at every mode matrix, rounded to rationals with exact PSD
   witnesses.
4. **Lean** ([emit_switched.py](../python/dynacert/emit_switched.py)).
   * `weights t p u x dx y : Fin K → ℝ` is the indicator of the active mode, written with the
     model's own conditions **copied verbatim from `Equations`, with the same binder names**;
     the weight of a mode is the product of its branch indicators. `weights_nonneg` and
     `weights_sum` (= 1) are closed by `split_ifs <;> norm_num`.
   * `step`: from `Equations t p u x dx y`, each coordinate derivative equals
     `Σ_m weights … m * (A_m z + B w)ᵢ`. Proof: one `split_ifs` on the switched equations and
     the unfolded weights together (so the equations and the weights are decided by the same
     hypotheses), then in every branch `linear_combination` with the active mode's
     multipliers (the generated proof tries each mode's multipliers; any that `ring` accepts
     is a proof).
   * `link`: along a solution, `ż = (Σ_m wt t m • A_m) z + B w` with
     `wt t = weights t p (u t) (x t) (dx t) (y t)`.
   * `tube`/`certified`: `PolytopicCert.invariant` already takes time-varying weights
     `wt : ℝ → Fin K → ℝ`, so the switching signal needs no new library theorem; the output
     bounds come from `LinearBoxCert` as for `lmi`. For a mode-dependent output, `out<k>`
     splits the output's own `if`s and uses the box certificate of the active mode's row.

## What is supported

* Continuous-time `if`-expressions (`if … then … elseif … else …`) anywhere in scalar
  equations, any number of them, as long as no branch or condition contains another `if`.
* Conditions of any form (nonlinear, on states, algebraics, inputs, parameters or time): they
  are never analysed, only copied, since the certificate holds under any switching.
* Disturbances, references (`reference(derivative = …)`), `initialSet` boxes (funnel).
* Mode-dependent algebraic outputs.

## What is not (and why)

| Not supported | Why / workaround |
|---|---|
| `when`, `reinit`, `pre` | discrete events and state jumps; rumoca's Lean export rejects them |
| Nested `if` | rejected by `analysis.modes`; flatten to an `elseif` chain |
| Affine modes (saturation `if u > umax then umax else u`, constant offsets) | a branch with a constant term is not linear in the error frame: the frame would need a per-mode equilibrium. Bound the saturated input as a disturbance instead |
| Uncertain parameters | v1; the vertices would be (mode × parameter corner) with products of indicator and interpolation weights |
| Modes that are not asymptotically stable | a common storage must decay in every mode (e.g. pure conditional integration freezes the integrator: `SwitchedPI`) |
| No common quadratic Lyapunov function | the method cannot certify; stability under the actual switching rule may still hold (or fail: `SwitchedUnstable`). Region-dependent (S-procedure) or piecewise-quadratic storage is future work |
| Sliding motions | not classical solutions (see above) |

`dynacert MODEL.mo` reports precisely which of these applies; for example, for the
conditional-integration PI loop:

```
switched    no   2 modes from 1 switch, linear in (x, z), but no common quadratic Lyapunov
                 function exists for the mode matrices (even without disturbances); mode 0
                 (|y.u| > p.ulim, max Re λ = 0) not asymptotically stable
```

## Results

Models in [examples/switching/](../examples/switching/README.md). Bounds are the Lean-checked
`certified` bounds; Monte Carlo is 200 i.i.d. scenarios (`validate --n 200`, achieved peak);
falsify is the best achieved peak of the adjoint and cross-entropy searches. Both are lower
bounds on the true worst case.

| Model | Modes | Output | Certified | Monte Carlo | Falsify | ratio |
|---|---|---|---|---|---|---|
| `SwitchedPILeak` (anti-windup, integrator bleed-off) | 2 | x | 28/171 ≈ 0.1637 | 0.1069 | 0.1080 | 0.66 |
| | | z | 369/1778 ≈ 0.2075 | 0.1949 | 0.1949 | 0.94 |
| `GainScheduledPI` (schedule on the load estimate) | 2 | w | 2617/8076 ≈ 0.3240 | 0.1707 | 0.1707 | 0.53 |
| | | z | 1185/6157 ≈ 0.1925 | 0.1492 | 0.1492 | 0.78 |
| | | u (mode-dependent row) | 11984/9581 ≈ 1.2508 | 0.7071 | 0.7070 | 0.57 |
| `AsymmetricDamper` (rebound vs compression) | 2 | x | 2993/6627 ≈ 0.4516 | 0.2861 | 0.2921 | 0.65 |
| | | v | 3583/4007 ≈ 0.8942 | 0.4625 | 0.4799 | 0.54 |
| `BumpStopSuspension` (3-stage damper × bump stop) | 6 | x | 8217/9868 ≈ 0.8327 | 0.2168 | 0.2179 | 0.26 |
| | | v | 18912/9355 ≈ 2.0216 | 0.3727 | 0.3706 | 0.18 |

The ratio is falsify / certified (the gap is the conservatism of one quadratic storage for all
modes, plus the ellipsoid-to-box step). The six-mode suspension is the loosest: one ellipsoid
must decay under spring rates 4 and 8 and three damping rates at once. With a bump-stop
stiffness of 10 (spring rate 14) no common quadratic storage exists at all.

Not certifiable by this method:

| Model | Why | Evidence |
|---|---|---|
| `SwitchedPI` (pure conditional integration, `der(z) = if abs(u) > ulim then 0 else x`) | the saturated mode freezes the integrator: `A` has eigenvalue 0, so no storage decays in that mode | bounded in simulation (MC 0.107 / 0.195, falsify 0.108 / 0.195): stable in practice, but a peak bound needs a region-dependent argument |
| `SwitchedUnstable` (two stable oscillators switched by quadrant) | both modes are stable, but no common quadratic Lyapunov function exists | genuinely unstable under this switching rule: the state grows exponentially (MC 2.01 / 1.91 and falsify 2.17 / 2.34 by `t = 10` from a disturbance of 0.1) |

Sliding: a gain schedule on the speed error itself (`kp = if abs(w) > eBand …`) makes the
control torque discontinuous across `|w| = eBand`, and the field can point into the surface
from both sides; the simulator then chatters (Monte Carlo slows by two orders of magnitude)
and such motions are outside the classical claim. Scheduling on the integrator state, whose
derivative `w` is continuous across the surface, avoids sliding; that is the version in the
examples.

Lean build times are 8–25 s per model (the six-mode model checks six LMI witnesses).
