# dynacert

Machine-checked safety certificates for Modelica models, in Lean 4 / Mathlib.

See [docs/capabilities.md](docs/capabilities.md) for everything it can do today, its limits and known
defects.

dynacert is the formally verified successor to [cp_reach](https://github.com/micahkc/cp_reach).
You annotate a Modelica model with what to certify. [rumoca](https://github.com/CogniPilot/rumoca)
exports the model to Lean and to Python from one DAE IR. Untrusted Python searches for a
certificate, and the Lean kernel checks it. The result is a theorem about rumoca's own
transcription of the model.

```
Model.mo + __Dynacert(...) annotations
   │ rumoca (one DAE IR)
   ├── lean-dae  ──► Model.lean   equations (trusted transcription)
   └── sympy-dae ──► model.py     same equations, for the search
                        │ dynacert (Python, untrusted): analysis, LMI search, exact rounding
        Spec.lean  the claim, from the model and its annotations only
        Cert.lean  link proof + certificate data + proof of the claim
                        │ lake build (Lean kernel)
                 theorem `<Model>.Cert.certified : <Model>.Spec.Claim bounds`
```

Proofs build on [gnc_lean](https://github.com/CogniPilot/gnc_lean), whose Lie-group, tube, and
ODE results are fully proved under the same axiom policy.

## Example

```modelica
model ClosedLoop
  parameter Real m = 1.0; parameter Real c = 0.2; parameter Real k = 1.0;
  parameter Real kp = 2.0; parameter Real kd = 0.8;
  input Real x_ref annotation(__Dynacert(reference(derivative = "v_ref", start = 0)));
  input Real v_ref annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref annotation(__Dynacert(reference));
  input Real d     annotation(__Dynacert(disturbance(bound = 1.0)));
  Real x(start = 0, fixed = true); Real v(start = 0, fixed = true);
  Real u_ff, F;
  Real e  annotation(__Dynacert(certify));
  Real ev annotation(__Dynacert(certify));
equation
  e = x - x_ref;  ev = v - v_ref;
  u_ff = m*a_ref + c*v_ref + k*x_ref;
  F = u_ff - kp*e - kd*ev;
  der(x) = v;  der(v) = (F + d - c*v - k*x) / m;
end ClosedLoop;
```

```
$ dynacert examples/ClosedLoop.mo lmi
CERTIFIED  ClosedLoop.Cert.certified  (axioms: Classical.choice, Quot.sound, propext)
  |e| ≤ 5649/6695  ≈ 0.843764   (simulated peak 0.7337)
  |ev| ≤ 7281/5089  ≈ 1.43073   (simulated peak 1.229)
```

The claim, from `certs/Certs/ClosedLoop/Spec.lean`:

```lean
def Claim (b : Fin 2 → ℚ) : Prop :=
  ∀ (p : Params) (u : ℝ → Inputs) (x : ℝ → States) (y : ℝ → Algebraics) (T : ℝ),
    p.Bound → IsSolutionOn p u x y T → Admissible u T → References u T →
    ReferenceStart u → Initial p (x 0) →
    (∀ t ∈ Ico 0 T, |(y t).e| ≤ (b 0 : ℝ) ∧ |(y t).ev| ≤ (b 1 : ℝ))
```

`Params`, `IsSolutionOn`, `Initial` and the rest are rumoca's transcription of the model. The
model has a reference trajectory and is linear in error coordinates, so the generated proof
changes coordinates to `(e, ev)` and closes every step with `linear_combination` of the
model's own equations.

## Annotations

| Annotation | Meaning in the claim |
|---|---|
| `input Real d annotation(__Dynacert(disturbance(bound = δ)))` | `∀ t, \|d(t)\| ≤ δ` |
| `input Real r annotation(__Dynacert(reference(derivative = "rd", start = r₀)))` | `r` continuous, `r' = rd` (right derivative), `r(0) = r₀` |
| `Real e annotation(__Dynacert(certify))` | conclusion `\|e(t)\| ≤ b` |
| `parameter Real c = 0.2 annotation(__Dynacert(uncertain(min = lo, max = hi)))` | the claim holds for every `c ∈ [lo, hi]` |
| `Real x(start = 0, fixed = true) annotation(__Dynacert(initialSet(min = lo, max = hi)))` | `x(0) ∈ [lo, hi]` instead of `x(0) = start` (`Spec.InitialSet`); the certificate adds the shrinking funnel `Cert.funnel` (`initial` is a Modelica keyword, hence `initialSet`) |

**Array variables** (`Real p[3]`, `input Real d[3]`, `parameter Real K[2, 3]`) are annotated as a
whole and read per component; the linear methods (`lmi`, `polyhedral`, `layered`) and the
simulation harness (`montecarlo`, `falsify`, `tube`) treat each element as a scalar coordinate.
In Lean, rumoca's `v : Fin n → ℝ` field gives the terms `(x t).p 0`, `(x t).p 1`, … (Modelica
`p[k]` is `p (k-1)`), and the outputs are named `e[1]`, `e[2]`, ….

| Annotation on an array | Meaning in the claim |
|---|---|
| `input Real d[3] annotation(__Dynacert(disturbance(bound = δ)))` | `\|d[i](t)\| ≤ δ` for every component (`Spec.Admissible` lists them), as if each were a scalar input; `bound = {δ₁, δ₂, δ₃}` gives one bound per component |
| `disturbance(bound = δ, norm = "2")` | the Euclidean ball `‖d(t)‖ ≤ δ`: not supported yet, rejected with a message (it would need equal rates per group in the LMI, a grouped budget in the Lean proof, and ball sampling in Monte Carlo) |
| `input Real r[3] annotation(__Dynacert(reference(derivative = "rd", start = r₀)))` | per component: `r[i]' = rd[i]` (`rd` an array of the same shape), `r[i](0) = r₀` (or `start = {…}`) |
| `Real e[3] annotation(__Dynacert(certify))` | one bound per component: `\|e[1](t)\| ≤ b₀`, `\|e[2](t)\| ≤ b₁`, … |
| `parameter Real c[2] = {…} annotation(__Dynacert(uncertain(min = lo, max = hi)))` | every component ranges over `[lo, hi]` independently (`Spec.ParamsOK` per component; `min`/`max` may be arrays) |
| `Real x[2](…) annotation(__Dynacert(initialSet(min = lo, max = hi)))` | `x[i](0) ∈ [lo, hi]` per component |

Array parameters that only set start values (`start = p0`) or enter the dynamics (gain matrices
`K * x`) are substituted elementwise from `Params.Bound`, like scalars.

## Layout

| Path | Contents |
|---|---|
| `Dynacert/Core/` | Quadratic forms and `PSDWitness`, dissipation (Grönwall), systems, first-exit tubes |
| `Dynacert/Linear/` | LTI, per-channel, and polytopic certificates; output bounds; bridge to gnc_lean supplies; `Scalar.lean`: lemmas that evaluate one component of rumoca's array equations |
| `Dynacert/Nonlinear/` | Mean-value Jacobian enclosures |
| `Dynacert/Prob/` | Scenario (order-statistic) and zero-failure bounds for Monte Carlo validation |
| `Dynacert/Lie/` | SE₂(3) log-error dynamics with right derivatives, chart-closing log tube, SO(3) invariance, physical output bounds |
| `Dynacert/Sector/` | Sector-multiplier certificates for nonlinear closed loops: LMI with quadratic supply checked by a dominance witness, regional invariance (several ellipsoids, first exit), composition of block storages, rigorous sector/peak bounds of `sin`, `cos`, `√(s²+h²)`, `atan2` ([docs/sector.md](docs/sector.md)) |
| `Rumoca/Prelude.lean` | rumoca's lean-dae prelude (the pipeline checks it is unchanged) |
| `certs/Certs/<Model>/` | Generated `Model`, `Spec`, `Cert`, plus `certified.json` and a plot |
| `examples/` | Annotated Modelica models; `notebooks/` |
| `python/dynacert/` | Analysis, search methods, Lean emission, pipeline, CLI, plots |
| `docs/roadmap.md` | Plan and status |

## Usage

```bash
lake exe cache get                   # prebuilt Mathlib (Lean v4.29.1, Mathlib pinned to gnc_lean's)
lake build                           # library + every certificate under certs/
pip install -e .                     # numpy, scipy, sympy, cvxpy, matplotlib
pip install -e '.[worstcase]'        # optional: CasADi + IPOPT for falsify's collocation
python -m pytest                     # Python tests (run locally; there is no hosted CI)
```

### Command line

The commands follow the layers of [docs/architecture.md](docs/architecture.md): give dynacert a
Modelica model to see what applies to it, grouped by layer and with reasons, then certify,
validate, and view:

```
$ dynacert examples/ClosedLoop.mo
ClosedLoop (ClosedLoop.mo, inferred): 2 states, 4 inputs, 5 parameters
  spec: certify e, ev; disturbances |d| ≤ 1; references x_ref, v_ref, a_ref
  certified: |e| ≤ 0.843764 (lmi), |ev| ≤ 1.43073 (lmi)

L2 analyze (structure)
  structure   yes  der(x) = A x + B u with constant coefficients
                   ...
L3 certify (Lean-checked methods)
  lmi         yes  linear in (e, ev), 1 disturbance channel
                   candidate found: |e| ≤ 0.8438, |ev| ≤ 1.431 (not yet checked by Lean)
  layered     no   layered: references and uncertain parameters are not supported yet (use the lmi approach)

L4 validate (evidence, untrusted)
  montecarlo  yes  samples disturbance d, reference a_ref
  ...
L5 view (products)
  tube        yes  error frame (e, ev) proved by ClosedLoop.Cert.tube

$ dynacert examples/ClosedLoop.mo certify             # portfolio: every feasible method, cheapest first
$ dynacert examples/ClosedLoop.mo certify lmi         # or the named methods only
$ dynacert examples/ClosedLoop.mo validate            # --sample (montecarlo), then --search (falsify)
$ dynacert examples/ClosedLoop.mo validate --sample --n 500
$ dynacert examples/ClosedLoop.mo view tube           # the proved tube along a reference
$ dynacert examples/ClosedLoop.mo view plots          # certificate + tube figures → certs/Certs/<Model>/plots
$ dynacert examples/ClosedLoop.mo view report         # the same in one PDF (default certs/Certs/<Model>/report.pdf)
$ dynacert examples/ClosedLoop.mo certify -h          # each verb's options, per method
$ dynacert --list                                     # every registered approach, by layer
```

`certify` runs the methods, continuing after one fails, and prints a method × output table:

```
certify TwoMassLayered: method × output bound   (* = kept, tightest)
  method          |a.x|         |b.x|
  lmi          1.33087*      1.01047
  layered      1.36022      0.549046*
  kept: |a.x| ≤ 4147/3116 (lmi), |b.x| ≤ 5323/9695 (layered)
```

Every method that built is recorded in `certs/Certs/<Model>/certificates.json` (theorem, Lean
file, bounds, axioms, source hash, time) with the kept bound per output; `certified.json` stays
the `lmi` sidecar. Each sidecar records `source_hash`, the sha256 of the Modelica source and the
model name, so a certificate of an edited model is recognized as stale. If `certify` emits a
`Spec.lean` that differs from the one on disk, the model or its annotations changed: once the
new certificate builds, every other certificate file in that directory that imports the old
`Spec` (with its sidecar and index entry) is deleted, and the deletions are printed.
`Model.lean`, `Spec.lean`, and `source.mo` are never deleted.

The direct form still runs any single approach, as before:

```
$ dynacert examples/ClosedLoop.mo lmi                 # = certify lmi
$ dynacert examples/ClosedLoop.mo montecarlo --n 500  # = validate --sample --n 500
$ dynacert examples/ClosedLoop.mo falsify -h          # each approach's own options
```

| Approach | Layer (verb) | Applies when |
|---|---|---|
| `structure` | analyze (`structure`) | always: Lie-group, gravity, layer, and linear structure; `--lean` links SE₂(3) in Lean |
| `lmi` | certify | error dynamics are linear, `A` multi-affine in uncertain parameters, and the LMI search succeeds (checked during assessment) |
| `layered` | certify | per-component LTI certificates whose couplings close under assume–guarantee |
| `montecarlo` | validate `--sample` (untrusted) | certified outputs and something to sample; compares against the certificate if it is current |
| `falsify` | validate `--search` (untrusted) | as `montecarlo`; worst-case search: adjoint gradients with switching times (exact for linear models), CasADi/IPOPT direct collocation, cross-entropy |
| `sector` | certify | nonlinear dynamics built from `sin`, `cos`, `√(s²+h²)`, `atan2` atoms about an equilibrium: exact linear part + residual channels with sector multipliers, rigorous residual bounds in Lean, region fixed point ([docs/sector.md](docs/sector.md)) |
| `compose` | certify | as `sector`, decomposed across a cut chosen from the coupling graph and screened by Proposition 2; block LMIs with supply rates, solved by ADMM |
| `tearing` | analyze | loop-tearing baseline: peak-to-peak cycle gain across each candidate cut |
| `tube` | view `tube` (set proved by `Cert.tube`) | a current certificate: carries the proved error-frame set along a reference (random or `--reference FILE.csv`), checks simulated runs stay inside; see [docs/tube.md](docs/tube.md) |

### Examples

[examples/README.md](examples/README.md) catalogs 42 annotated models from twelve industries
(automotive, aerospace, marine, rail, energy, process, buildings, water, robotics, biomedical,
precision, agriculture): 34 Lean-certified, 8 nonlinear validation-only, each with Monte Carlo
and worst-case results. `dynacert timings` compares the run times recorded for every model.

[examples/capabilities/](examples/capabilities/README.md) has small models, one per capability,
including what dynacert rejects and repros of known failures.

### Figures

Any run can draw its figures. Run `--figures list` to see the choices for an approach:

```
$ dynacert examples/ClosedLoop.mo montecarlo --plot                 # every figure → certs/Certs/ClosedLoop/plots/
$ dynacert examples/ClosedLoop.mo falsify --report closedloop.pdf   # all of them in one PDF
$ dynacert examples/PendulumPD.mo falsify --figures worstcase-e --theme paper --format pdf,svg --plot figs/
$ dynacert examples/ClosedLoop.mo montecarlo --figures envelope,phase --show
```

| Approach | Figures |
|---|---|
| `lmi` | `certificate`: phase plane with the certified ellipse, simulations against the bounds |
| `montecarlo` | `exceedance` (tail probabilities, DKW band, scenario-bound ε), `histogram` (peaks), `envelope` (quantile fan chart over time), `traces` (worst highlighted), `phase` (with the certified ellipse), `tightness` |
| `tube` | `tube` (each state with the proved band around the reference), `tube-phase` (the set carried along the path in a state plane), `tube-margin` (zᵀPz/level per run) |
| `falsify` | `worstcase-<output>` (each method's worst trajectory, the disturbance with its switch times, the switching function σ), `tightness` (lower bounds vs. the certified bound) |

Options: `--plot [DIR]`, `--report FILE.pdf`, `--show`, `--figures a,b`,
`--theme light|dark|paper`, `--format png,svg,pdf`, `--dpi N`. In Python, use `mc.plot("envelope")`
and the `dynacert.figures` module (`with figures.theme("dark"): ...`).

`view plots` draws the `lmi` certificate figure and the `tube` figures (the tube options such as
`--n` and `--reference` apply); `view report` puts them in one PDF.

Common options: `--model NAME` (default: the last model in the file), `--json`, `-q`. Exit
status: 0 success (for `certify`: at least one method certified), 1 failed or counterexample, 2
not applicable, 64 usage. New
approaches are plugins: see [docs/approaches.md](docs/approaches.md).

### From Python / Jupyter

```python
import dynacert
cert = dynacert.check("examples/ClosedLoop.mo", "ClosedLoop")  # or dynacert.load("ClosedLoop")
cert              # claim, verified bounds, theorem, axioms
cert.verify()     # re-check with the Lean kernel
runs = cert.simulate(40)   # the Modelica model under admissible inputs
cert.plot(runs)            # trajectories vs. verified bounds
cert.table(runs)           # verified bound vs. simulated peak
```

### Monte Carlo validation (untrusted)

```python
mc = cert.montecarlo(eps=0.01, beta=1e-6)  # 1375 i.i.d. admissible scenarios, simulated by rumoca
mc                     # no sample above the bound; achieved peak vs certified bound
cert.crosscheck(20)    # rumoca's native solver vs the sympy export, same scenarios
cert.falsify("e", init=mc)                 # cross-entropy search for a worst case
```

```
$ dynacert examples/ClosedLoop.mo montecarlo
Monte Carlo: ClosedLoop, 1375 i.i.d. scenarios on [0, 10] (rumoca, seed 0, 28.2 s)
  output   certified    achieved   ratio  violations
  e         0.843764    0.744213   0.882           0
  ev         1.43073     1.24889   0.873           0
  No sample exceeds a certified bound: P(peak > bound) ≤ 0.009998 with confidence 1 - 1e-06 [...]
  Per output, P(peak > achieved) ≤ 0.009998 with confidence 1 - 1e-06 [...]

$ dynacert examples/ClosedLoop.mo falsify
|e|: achieved 0.7499978 vs certified 0.843764 (ratio 0.88887)  by adjoint/switch
    adjoint/scan                 0.7499556
    adjoint/switch               0.7499978
    collocation t*=10+           0.7498426
```

The probabilistic statements are proved once in Lean (`Dynacert.Prob.scenario_bound`,
`zero_failure_bound`) and hold under the recorded sampling distribution. Simulations are never
certificates. See [docs/montecarlo.md](docs/montecarlo.md).

See [examples/notebooks/mass_spring_damper.ipynb](examples/notebooks/mass_spring_damper.ipynb).

Compiling a model needs rumoca with vendor-annotation support (branch `dynacert-lean`) and its
`lean_dae` / `sympy_dae` targets. Set `DYNACERT_RUMOCA` (binary) and `DYNACERT_TARGETS`
(`examples/codegen` in that checkout).

## How certificates are checked

Every matrix inequality reduces to a `PSDWitness`: Python supplies rational `L` and `d ≥ 0`
with `M = Lᵀ diag(d) L`, and `decide +kernel` checks the identity by exact rational arithmetic.
Python adds strict margins so rounding preserves feasibility. The pipeline then audits
`#print axioms` of the final theorem: only `propext`, `Classical.choice`, and `Quot.sound` are
accepted.

## Scope of the current guarantees

- Solutions are continuous on `[0, T]` with right derivatives on `[0, T)` (`IsSolutionOn`),
  which admits step and zero-order-hold disturbances, but not arbitrary measurable ones.
- Disturbances have componentwise peak bounds.
- Claims about algebraic variables hold on `[0, T)`, where the model's equations are asserted.
  Claims about states hold on `[0, T]`.
- Sound but not complete: if no certificate is found, nothing is claimed.

## License

Apache License 2.0. See [LICENSE](LICENSE).
