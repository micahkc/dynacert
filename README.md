# dynacert

Machine-checked safety certificates for Modelica models, in Lean 4 / Mathlib.

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

## Layout

| Path | Contents |
|---|---|
| `Dynacert/Core/` | Quadratic forms and `PSDWitness`, dissipation (Grönwall), systems, first-exit tubes |
| `Dynacert/Linear/` | LTI, per-channel, and polytopic certificates; output bounds; bridge to gnc_lean supplies |
| `Dynacert/Nonlinear/` | Mean-value Jacobian enclosures |
| `Dynacert/Prob/` | Scenario (order-statistic) and zero-failure bounds for Monte Carlo validation |
| `Dynacert/Lie/` | SE₂(3) log-error dynamics with right derivatives, chart-closing log tube, SO(3) invariance, physical output bounds |
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
```

### Command line

Give dynacert a Modelica model to see which approaches apply to it, then run one:

```
$ dynacert examples/PendulumPD.mo
PendulumPD (PendulumPD.mo, inferred): 2 states, 1 inputs, 7 parameters
  spec: certify e; disturbances |tau_d| ≤ 1

  lmi         certificate  no   the dynamics are not linear: der(omega) is nonlinear in theta
  montecarlo  validation   yes  samples disturbance tau_d
                                no certificate: reports achieved peaks and probabilistic bounds only
  falsify     validation   yes  searches disturbance tau_d
                                no certificate: reports achieved peaks and probabilistic bounds only

$ dynacert examples/ClosedLoop.mo lmi                 # certify: search, emit Lean, kernel check
$ dynacert examples/ClosedLoop.mo montecarlo --n 500  # validate against the certificate
$ dynacert examples/ClosedLoop.mo falsify -h          # each approach's own options
$ dynacert --list                                     # every registered approach
```

| Approach | Kind | Applies when |
|---|---|---|
| `lmi` | certificate (Lean-checked) | error dynamics are linear, `A` multi-affine in uncertain parameters, and the LMI search succeeds (checked during assessment) |
| `montecarlo` | validation (untrusted) | certified outputs and something to sample; compares against the certificate if it is current |
| `falsify` | validation (untrusted) | as `montecarlo`; worst-case search: adjoint gradients with switching times (exact for linear models), CasADi/IPOPT direct collocation, cross-entropy |
| `tube` | validation (set proved by `Cert.tube`) | a current certificate: carries the proved error-frame set along a reference (random or `--reference FILE.csv`), checks simulated runs stay inside; see [docs/tube.md](docs/tube.md) |

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

Common options: `--model NAME` (default: the last model in the file), `--json`, `-q`. Exit
status: 0 success, 1 failed or counterexample, 2 approach not applicable, 64 usage. New
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
