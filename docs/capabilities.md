# What dynacert can do

Status as of 2026-11-02, from a review of the working tree (uncommitted changes included). Results
quoted here were run on that date unless a source document is named.

dynacert takes an annotated Modelica model and produces a Lean theorem stating that the model's
outputs stay within bounds, for every disturbance, reference and parameter the annotations allow.
Python searches for the proof data, and the Lean kernel checks it. If no proof is found, nothing is
claimed.

| Snapshot | |
|---|---|
| Certificate methods | 8 (`lmi`, `polyhedral`, `switched`, `layered`, `sector`, `compose`, `funnel`, `lie`) |
| Certificates in the repo | 73, across 65 models |
| Annotated example models | `examples/`, including the 18 new certified ones in `examples/capabilities/` |
| Python tests | 108 of 109 pass (the failure is listed under [Known defects](#known-defects)) |
| Axioms allowed in a theorem | `propext`, `Classical.choice`, `Quot.sound`; the pipeline audits every theorem |

## What a result means

A certificate is the theorem `<Model>.<Method>Cert.certified : <Model>.Spec.Claim b`. In words:

> For all parameters in their ranges, all admissible inputs, and every solution of rumoca's Lean
> transcription of the model that starts in the stated initial set, each certified output stays
> within its bound on `[0, T)`, for every `T`.

- `Spec.lean` is generated from the model and annotations only, so no search result can change the
  claim.
- **Trusted:** the Lean kernel, Mathlib, gnc_lean, dynacert's Lean library, rumoca's Modelica-to-Lean
  transcription, and a person reading `Spec.lean`.
- **Not trusted:** Python, solvers, floating point, structure discovery, method choice, simulation.
- **Scope:** solutions are continuous with right derivatives, which admits step and zero-order-hold
  inputs but not arbitrary measurable ones. Sliding motions at a switching surface are not covered.
  Finite-horizon claims (`funnel`) hold only on their horizon. The theorem is about the model, not
  the hardware.

## Stating a claim: annotations

| Annotation | Meaning in the claim |
|---|---|
| `Real e annotation(__Dynacert(certify))` | Conclusion: `\|e(t)\| ≤ b`, with `b` found by the search |
| `input Real d annotation(__Dynacert(disturbance(bound = δ)))` | For every `\|d(t)\| ≤ δ` |
| `input Real r annotation(__Dynacert(reference(derivative = "rd", start = r₀)))` | For every `r` with `r' = rd`, `r(0) = r₀` |
| `parameter Real c annotation(__Dynacert(uncertain(min = lo, max = hi)))` | For every `c` in `[lo, hi]` |
| `Real x(...) annotation(__Dynacert(initialSet(min = lo, max = hi)))` | For every `x(0)` in `[lo, hi]`; also proves a shrinking funnel |
| `annotation(__Dynacert(horizon = T))` on the model | Finite horizon, for `funnel` |
| `Real x annotation(__Dynacert(nominal = "x_ref"))` | The state's reference trajectory, for `funnel` |

Arrays are annotated as a whole and read per component. `bound`, `min`, `max` and `start` may be
arrays, and outputs are named `e[1]`, `e[2]`, and so on.

## Certificate methods

| Method | Handles | How it proves the bound | Lean theorem | Typical time |
|---|---|---|---|---|
| `lmi` | Linear in error coordinates; `A` multi-affine in uncertain parameters | One ellipsoid, with an LMI per parameter corner | `Cert.certified`, `Cert.tube`, `Cert.funnel` | 30–40 s |
| `polyhedral` | Linear, fixed parameters and start | Invariant polytope (Metzler certificate, LP duality); reuses the `lmi` link | `PolyCert.certified` | 80 s for both, at 128 facets |
| `switched` | `if` / `elseif` between linear modes | One ellipsoid that decays in every mode, so it holds under any switching | `SwitchedCert.certified` | 30 s |
| `layered` | Linear components with weak coupling | One certificate per component, joined by mutual first exit (assume–guarantee) | `LayeredCert.certified` | 50 s with `lmi` |
| `sector` | Nonlinear near an equilibrium: polynomials, `sin`, `cos`, `√(s²+h²)`, `√(1−Σx²)`, `atan2(y,h)` | Exact linear part plus residual channels, with Lean-proved bounds on a region fixed point | `SectorCert.certified` | 1–2 min |
| `compose` | As `sector`, across a cut | Automatic cut, per-block LMIs solved by ADMM (or `--solver central`), supply rates | `ComposeCert.certified` | Several minutes |
| `funnel` | `ẋ = Ax + Σ a sin(x_k) + c(t) + Bw` along a polynomial path, on a finite horizon | Piecewise-polynomial `P(t)`, univariate SOS | `FunnelCert.certified` | 2 min at 8 segments |
| `lie` | SE₂(3) vehicle, body-frame PD, coasting reference on a circular orbit, inverse-square gravity | Log-error tube in the Lie algebra | `LieCert.certified` | 30 s |

Times are from today's runs on the shared machine with the library already built. Larger models take
longer: the planar quadrotor takes about 3.5 minutes in Lean (docs/sector.md).

### Which features each method accepts

Checked today with `dynacert MODEL.mo` on purpose-built probes, not taken from the docs.

| Method | Disturbance | Reference | Uncertain parameter | Initial box | Arrays |
|---|---|---|---|---|---|
| `lmi` | yes | yes | yes | yes | yes |
| `polyhedral` | yes | yes | no | no | yes |
| `switched` | yes | yes | no | yes | no |
| `layered` | yes | no | no | untested | crashes (see below) |
| `sector` | yes | no | no | no | no |
| `compose` | yes | no | no | no | no |
| `funnel` | yes | polynomial `nominal` only | untested (assessment doesn't screen it) | no | no |
| `lie` | yes | coasting reference only | no | no | required |

## Finding structure

`dynacert MODEL.mo structure` looks for linear form, error coordinates, layers and cascades, SO(3) and
SE₂(3) kinematics, gravity class, log-error pairs, and quaternion, SE(3) and integrator forms. Findings
only choose which proof is attempted. Anything a certificate uses is re-proved in a generated link
file. `--lean` builds the SE₂(3) link. `tearing` is a peak-to-peak small-gain analysis across each
cut; it explains failures and produces no certificate.

## Evidence and products (untrusted)

| Command | Gives you |
|---|---|
| `validate --sample` (`montecarlo`) | Random admissible scenarios, peak comparison, and scenario bounds such as `P(peak > achieved) ≤ ε` from theorems in `Dynacert.Prob` |
| `validate --search` (`falsify`) | Directed worst-case search: adjoint with switching times, CasADi collocation, cross-entropy |
| `view tube` | The proved set along a reference (random or `--reference FILE.csv`), checked against simulated runs |
| `view plots`, `view report` | Certificate and tube figures, or one PDF |
| `--crosscheck N` | rumoca's solver against the sympy export on N scenarios |

Figures: `exceedance`, `histogram`, `envelope`, `traces`, `phase`, `tightness`, `worstcase-<output>`,
`tube`, `tube-phase`, `tube-margin`, `certificate`. Options: `--plot [DIR]`, `--report F.pdf`, `--show`,
`--figures a,b`, `--theme light|dark|paper`, `--format png,svg,pdf`, `--dpi N`.

## Using it

```bash
dynacert MODEL.mo                     # what applies, by layer, with reasons
dynacert MODEL.mo certify             # every feasible method, keep the tightest bound per output
dynacert MODEL.mo certify lmi sector  # named methods only
dynacert MODEL.mo validate            # Monte Carlo, then worst-case search
dynacert MODEL.mo view tube
dynacert --list                       # every approach, by layer
dynacert timings                      # recorded run times
```

Exit status: 0 success, 1 failed or counterexample, 2 not applicable, 64 usage. Each model's results
are in `certs/Certs/<Model>/`, with `certificates.json` recording the theorem, bounds, axioms and
source hash for each method, plus the kept bound per output. Editing the model makes old certificates
stale, and they are removed once a new one builds.

From Python:

```python
import dynacert
cert = dynacert.check("examples/ClosedLoop.mo", "ClosedLoop")  # or dynacert.load("ClosedLoop")
cert.verify()              # re-check with the Lean kernel
runs = cert.simulate(40); cert.plot(runs); cert.table(runs)
mc = cert.montecarlo(eps=0.01, beta=1e-6); cert.falsify("e", init=mc)
```

New methods are plugins: see [approaches.md](approaches.md).

## Results worth knowing

| Model | Method | Certified | Worst found | Note |
|---|---|---|---|---|
| `ReservoirCascadePoly` | `polyhedral` | \|h1\| ≤ 1.0002, \|h2\| ≤ 3.0005 | 0.99995, 2.966 | Exact peaks are 1 and 3; `lmi` gives 1.471 and 3.209 |
| `ThreeZoneRadiant` | `layered` | \|z1.T\| ≤ 0.7885 | 0.7858 | `lmi` gives 1.112 |
| `PathFollowScheduled` | `sector` | \|y\| ≤ 0.0504 | 0.0491 | Tight on a nonlinear loop |
| `PlanarQuadrotor` | `sector` | \|e_x\| ≤ 0.160 m, \|θ\| ≤ 0.146 rad | 0.094, 0.077 (Monte Carlo) | Published grid result: 0.178, 0.164 (docs/sector.md) |
| `Quadrotor3D` | `compose` | \|e_x\|, \|e_y\| ≤ 0.055, \|e_z\| ≤ 0.040 | not run here | Added today by a separate job; uncommitted |
| `RobotArmSwingFunnel` | `funnel` | \|e\| ≤ 0.0253 rad on [0, 2] s | 0.0056 (Monte Carlo on [0, 2]) | Looser; proved over a large swing |

## What it can't do yet

| Not supported | What happens |
|---|---|
| `when`, `reinit`, `pre`, `sample`, time events, clocks | rumoca's export rejects them |
| Euclidean-ball disturbances (`norm = "2"`) | Rejected with a message |
| A certified output that reads a disturbance directly (`y = Cz + Dw`) | Rejected by the linear methods |
| An uncertain parameter in the input matrix `B` | Rejected by `lmi` |
| `atan2(y, constant)` | sympy rewrites it to `atan`, which has no atom |
| Other functions, such as `exp` | Rejected; Monte Carlo and falsification still run |
| Saturation (affine modes), Filippov sliding, region-dependent storage | Not modeled; see switching.md |
| Controlled invariance, safety and reach-avoid, temporal specs | Proposed in architecture.md |
| A new SE₂(3) controller without new Lean | `lie` is one PD theorem; the migration is in generality.md |

## Known defects

Found during this review. None is fixed. None is a soundness problem: they stop a certificate or
weaken evidence, and can't produce a wrong theorem. Repros are in
[examples/capabilities/known-failures/](../examples/capabilities/known-failures/).

| # | Defect | Effect | Where |
|---|---|---|---|
| 1 | `Model.var` is defined twice; the second raises `KeyError` instead of returning `None` | `layered` crashes on array models; the one failing test | `python/dynacert/model.py:81`, `:110` |
| 2 | `_lin_comb` calls `sympy.reduced` with no generators | `sector` fails on models with no algebraic variables (`InvertedPendulumHold`) | `python/dynacert/emit_sector.py:130` |
| 3 | The generated `obtain hR0 := hR` doesn't bind `hR0` | `sector` fails to build with exactly one region coordinate (`CraneHoistSwing`) | `python/dynacert/emit_sector.py:462` |
| 4 | Generated `Type mismatch` at line 94 of `SectorCert.lean` / `ComposeCert.lean`; cause not diagnosed | `TwoAxisTiltHeave`, `CraneTwoAxisSwing` | `python/dynacert/emit_sector.py` |
| 5 | Assessment accepts, and the run rejects: "linear factors in bounded channels need a region coordinate" | `TiltedThrustHeave` | `python/dynacert/sector.py:746` |
| 6 | `compose`: "ADMM failed for objective e" (`--solver central` not tried on these) | `CraneHoistSwing`, `CraneTwoAxisSwing` | `python/dynacert/approaches/sector.py:263` |
| 7 | `montecarlo` and `falsify` don't sample `initialSet` boxes | Bounds with an initial box look very loose (`OvenWarmStartFunnel`: 0.177 against 2.418), and the box goes unexercised | `python/dynacert/montecarlo.py` |
| 8 | Validators default to `T = 10` and ignore `horizon` | `RobotArmSwingFunnel` reports 0.0246 from outside its [0, 2] claim; on [0, 2] it is 0.0056 | `python/dynacert/approaches/monte_carlo.py` |
| 9 | Validators compare with the `lmi` bound when a tighter kept bound exists | `ThreeZoneRadiant` shows 0.71, not 0.997 | `certificate_note` in `approaches/monte_carlo.py` |
| 10 | Collocation fails on array disturbances: `'d[1]' is not in list` | `falsify` exits 1 on `GimbalThreeAxis`, `QuaternionAttitudeReport`; earlier stages do finish | `python/dynacert/collocation.py` (location inferred) |
| 11 | `falsify` fails on explicit `time` in equations: `NameError: name 't' is not defined` | `RobotArmSwingFunnel` | sympy lambdify path (location not traced) |
| 12 | `falsify` didn't finish on `GeoServicerTracking` within 500 s; both validators timed out on `ValveGainTwoSwitches` | No worst-case evidence for those; causes not diagnosed | |
| 13 | `view plots` and `tube` need an `lmi` certificate | `view` says "no current certificate" on a model certified by `switched` | `python/dynacert/approaches/tube.py` |
| 14 | `--plot` falls back to `./<Model>_plots/` for models certified only by a non-`lmi` method, not their certificate directory | Stray folders in the repo root | `python/dynacert/cli.py:641` |
| 15 | `funnel` and pre-index certificates aren't all in `certificates.json` | `PendulumPID`, `ClosedLoopUncertain` are missing from the index | `certs/Certs/` |
| 16 | `Dynacert.lean` doesn't import `Nonlinear/{TrigBounds,FunnelLink,UnivariateSOS,SOSFunnel}` or `Lie/QuatFn` | `lake build Dynacert` skips them; certificates still pull them in | `Dynacert.lean` |
| 17 | The README and `examples/README.md` undercount models and omit `horizon` and `nominal` | Docs lag the code | |

Not checked in this review: a full `lake build` (skipped because of the machine's memory limit), so
each new certificate was built on its own target. Existing certificates weren't rebuilt.

## Where to read more

| Topic | Document |
|---|---|
| The six layers and method families | [architecture.md](architecture.md) |
| Nonlinear methods, cuts | [sector.md](sector.md) |
| Switching semantics | [switching.md](switching.md) |
| Polytopes | [polyhedral.md](polyhedral.md) |
| Tubes and funnels | [tube.md](tube.md) |
| Monte Carlo and falsification | [montecarlo.md](montecarlo.md) |
| Structure discovery | [structure.md](structure.md) |
| The rule "no new proof per model" | [generality.md](generality.md) |
| Examples | [../examples/capabilities/README.md](../examples/capabilities/README.md), [../examples/README.md](../examples/README.md) |
