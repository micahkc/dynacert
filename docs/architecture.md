# How dynacert handles a model

Status: draft for discussion, 2026-10-14. This proposes a hierarchy for everything dynacert does
with a model: what is trusted, what decides routing, where certificate methods come from
(including reachability methods we do not have yet), and where validation and plots fit. Today
these are all flat "approaches"; the hierarchy says which of them are alternatives to each other
and which are steps that follow one another.

## 1. Six layers

Each layer answers one question and depends only on the layers above it.

```
L0  Model        what are the equations?        rumoca, one DAE IR → Model.lean (trusted)
                                                 + sympy / CasADi / native solver (untrusted views)
L1  Claim        what is asserted?              Spec.lean, from the __Dynacert annotations only
L2  Structure    what form do the dynamics      structure discovery (untrusted, decides routing);
                 have?                           each finding used is re-proved in a Link file
L3  Certificate  how is the claim proved?       a method = Python search + Lean soundness theorem
                                                 + combinators that join methods
L4  Evidence     how tight is it, is the        Monte Carlo, falsification, cross-checks
                 pipeline right?                 (untrusted, never a certificate)
L5  Products     what is it used for?           bounds, tubes along trajectories, plots, reports
```

Only L0's `Model.lean`, L1, and L3's Lean side are trusted. A wrong decision at L2 or a bad
number at L3 can only make the build fail. L4 and L5 read certified data but add no
guarantees.

| Layer | Code today |
|---|---|
| L0 | rumoca targets `lean_dae`, `sympy_dae`, `casadi-ode`, the native solver; `problem.py` |
| L1 | `spec.py`, `emit_lti.emit_spec` |
| L2 | `structure.py` (findings), `approaches/lmi.nonlinear_terms`, `pipeline.linear_problem` |
| L3 | `approaches/lmi.py`, `approaches/layered`, `Dynacert/{Linear,Lie,Compose,Nonlinear}` |
| L4 | `montecarlo.py`, `worstcase.py`, `collocation.py`, `approaches/{montecarlo,falsify}.py` |
| L5 | `tube.py`, `figures.py`, `approaches/tube.py`, `api.py` |

## 2. L1: claim shapes

The claim is fixed by the annotations, never by the method. Methods differ in which claim
shapes they can prove.

| Claim | Statement | Annotations | Status |
|---|---|---|---|
| Output peak bound | `∀ t, \|yᵢ(t)\| ≤ bᵢ` | `certify`, `disturbance(bound)` | done |
| Invariant set (tube) | `∀ t, z(t) ∈ E` in an error frame | as above; the frame is derived | done (`Cert.tube`) |
| Funnel | `V(z(t)) ≤ ρ(t)`, shrinking from a nonzero initial set | `initial(...)` | proposed |
| Finite-horizon reach set | `∀ t ∈ [0, T], x(t) ∈ R(t)` | `horizon` | proposed (D4) |
| Safety / reach-avoid | `x(t) ∉ Unsafe`, possibly reaching a goal | `unsafe(...)`, `goal(...)` | proposed (D4) |
| Temporal specs (STL) | e.g. settles within τ | `stl(...)` | idea |

Chance constraints such as `P(peak > s) ≤ ε` are not claims. They are L4 statements about a
sampling distribution, backed by `Dynacert.Prob`.

## 3. L2: model classes

Structure discovery classifies the model. The class decides which L3 methods are tried. Each
property a certificate relies on is re-proved from `Model.lean` (the Link step), so a wrong
classification fails the build.

| Class | Test (L2) | Example | Methods that apply (L3) |
|---|---|---|---|
| LTI in error coordinates | `f` linear in states, references and disturbances | `ClosedLoop` | quadratic dissipation, L1, zonotope |
| LPV / polytopic | linear, `A` multi-affine in uncertain parameters | `ClosedLoopUncertain` | common quadratic over vertices |
| Layered / cascade | the state-dependency graph splits into components | `TwoMassLayered` | composition of per-layer certificates |
| Lie-group kinematics | `Ṙ = R[ω]×`, `ṗ = v`, `v̇ = Ra + g` (SE₂(3)) | `QuadrotorTracking` | log-error tube (+ residuals) |
| Smooth nonlinear | explicit ODE, analytic `f` | `PendulumPD` | Jacobian enclosure, contraction, SOS, Taylor models |
| Polynomial | `f` polynomial | — | SOS storage, barriers |
| Sampled-data / clocked | Modelica clocks, `sample` | — | e^{Ah} enclosure + intersample bound |
| Hybrid | events, `when`, piecewise | — | none yet |

The classes are not exclusive. A quadrotor is layered, attitude then translation, and each
layer is Lie-group. Composition (§4.4) is what lets one model use several methods.

## 4. L3: where certificate methods come from

Every certificate method is a pair: an untrusted search that produces exact data, and a
soundness theorem proved once in Lean that turns checked data into the claim. The methods
come from three mathematical families, plus combinators that join them.

### 4.1 Certificate functions

Find a function whose sublevel set cannot be left. The proof is a pointwise inequality on
data (`V̇ ≤ −αV + γ‖w‖²`, `B ≤ 0` on the boundary, ...), checked as a PSD witness or a
polynomial identity. This family is cheap to check and scales with the size of the data, not
the horizon.

| Method | Model class | Search | Lean check | Status |
|---|---|---|---|---|
| Quadratic dissipation (LTI) | LTI | LMI (cvxpy) | `PSDWitness`, `LTICert.invariant` | done (`lmi`) |
| Common quadratic over vertices | LPV | vertex LMIs | `PolytopicCert` | done (`lmi`) |
| Regional polytopic | nonlinear, on a region | vertex LMIs + region radius | `PolytopicCert.regional_invariant` | Lean done, not generated |
| Jacobian enclosure + quadratic | smooth nonlinear | mean-value enclosure, vertex LMIs | `Nonlinear/Enclosure` + regional polytopic | Lean partly done |
| Polytope + residual | nonlinear, Lie | P, sector gain, radius | gnc `PolytopicResidualTube` | needs bridge |
| Lie log-error tube | SE₂(3) | algebra controller, vertex LMIs, radius fixed point | `Lie.log_tube_of_residuals` | Lean core and link done; control residual lemma open |
| Contraction metric | smooth nonlinear | metric LMI over the Jacobian enclosure | gnc `Contraction.differential_to_incremental` | proposed |
| Time-varying metric P(t) (funnels) | nonlinear along a trajectory | polynomial P(t), Bernstein | matrix-Bernstein PSD lemma + Grönwall | proposed (M6) |
| SOS storage / barrier | polynomial | SOS programme | polynomial identity + Gram `PSDWitness` | proposed (Phase 4) |

### 4.2 Set propagation (flowpipes)

Propagate an enclosure of the reachable set in time steps. The proof is an enclosure of the
flow map over each step. This family is tighter on finite horizons and handles non-invariant
behaviour, but checking cost grows with the number of steps, and nonlinear versions need the
model as data in Lean.

| Method | Model class | Lean needs | Status |
|---|---|---|---|
| Zonotope / support-function flowpipe | LTI | rational enclosure of e^{Ah} (Taylor + remainder), Minkowski sums | proposed (shares M5's lemma) |
| Ellipsoidal reachability | LTI | Riccati-type ellipsoid update with a containment witness per step | proposed |
| Sampled-data step | LTI + ZOH controller | e^{Ah} enclosure + intersample bound | proposed (M7) |
| Interval / mixed-monotone embedding | nonlinear | interval evaluation of `f` → needs a deep embedding of the equations (D2) | proposed, after D2 |
| Taylor models / validated integration | nonlinear | Taylor-model arithmetic over the deep embedding | research; LeanCert only if its axioms pass |
| Hamilton–Jacobi level sets | any | grid solutions are not checkable certificates | out of scope (an L5 view at most) |

### 4.3 Input–output characterizations

Bound the output directly from the input with an exact gain, without a set. The proof is
variation of constants plus an enclosure of the impulse response.

| Method | Model class | Lean needs | Status |
|---|---|---|---|
| Peak-to-peak (L1) gain | LTI | variation of constants for `IsSolutionOn`, enclosure of `\|C e^{As} B\|`, exponential tail bound | proposed (M5); the tightest possible bound for LTI |
| IQC / multipliers | LTI + structured nonlinearity | frequency-domain inequality → KYP LMI | idea |

### 4.4 Combinators

These are not methods by themselves. They take certificates and produce certificates, and they
are how one model combines several methods.

| Combinator | From → to | Lean |
|---|---|---|
| Change of frame | model coordinates → error coordinates (linear, Lie log) | generated Link (`linear_combination`, `LieLink`) |
| Ellipsoid → box / output | set → `\|yᵢ\| ≤ b` | `BoxCert` |
| Algebra → group | log-coordinate set → physical position, velocity, attitude | `Lie/PhysicalOutput` |
| Vertex hull | per-vertex inequality → all parameters in the box | `PolytopicTube.vertex_supply` |
| Assume–guarantee | per-layer bounds with assumptions → whole model | `Compose.assume_guarantee` |
| Coupled energy | joint weighted storage when peak composition fails | gnc `CoupledTube` |
| Portfolio | several methods → keep the tightest bound | min over certified bounds; trivial in Lean |

### 4.5 Controllers, MPC included

A controller is part of the model (L0), not a method. How an MPC controller is certified
depends on what is written in the Modelica model:

- **Linear feedback plus a tube MPC design.** The robust positive invariant set is an
  L3 quadratic-dissipation certificate. Constraint tightening is an L1 claim.
- **Explicit MPC (piecewise affine).** The closed loop is a hybrid model, which needs a hybrid
  method (none yet).
- **Online optimization in the loop.** A certificate would have to trust the solver's
  optimality, so this stays at L4: simulation, falsification, Monte Carlo.

## 5. Routing

1. Load (L0). Read the claim (L1). Classify (L2).
2. Collect the L3 methods whose class and claim shape match. Run their cheap assessment, which
   may include the numeric search (as `lmi` does).
3. Try them from cheapest to most expensive (portfolio). Every one that builds proves the same
   `Claim`. Keep the tightest, and record the others for comparison.
4. Optionally: L4 against the kept certificate (agreement, tightness, counterexamples), and L5
   products (tubes, plots).

### Matrix of class × claim

✓ = a method exists; ○ = proposed method; — = no route.

| | peak bound | tube / invariant | funnel | finite-horizon reach | safety |
|---|---|---|---|---|---|
| LTI | ✓ dissipation, ○ L1, ○ zonotope | ✓ | ○ Grönwall | ○ zonotope | ○ via reach set |
| LPV | ✓ vertices | ✓ | ○ | ○ | ○ |
| Layered | ✓ assume–guarantee | ✓ per layer | ○ | ○ | ○ |
| Lie SE₂(3) | ○ log tube + physical outputs | ○ | ○ | — | ○ via tube |
| Smooth nonlinear | ○ enclosure, ○ contraction | ○ regional | ○ P(t) | ○ Taylor models (after D2) | ○ barrier |
| Polynomial | ○ SOS | ○ SOS | ○ SOS in t | ○ | ○ barrier |
| Sampled-data | ○ e^{Ah} | ○ | — | ○ | ○ |
| Hybrid | — | — | — | — | — |

## 6. L4 and L5

**Evidence (L4).** Evidence is always about one fixed claim, and usually about one certificate.

| Tool | Question | Output |
|---|---|---|
| Monte Carlo (`Prob.scenario_bound`) | typical behaviour, agreement | achieved peak, ε at confidence 1−β |
| Falsification (adjoint/PMP, collocation, cross-entropy) | how bad can it get? | achieved worst case: a lower bound, or a counterexample |
| Cross-check (rumoca native vs sympy export) | do the two transcriptions agree? | discrepancy per output |
| Tightness report | how conservative is the proof? | lower bound vs certified bound |

**Products (L5).** These only display or transform what is already proved.

| Product | Reads |
|---|---|
| Bounds, theorem, axioms | `certified.json` |
| Tube along a reference | `Cert.tube` + the error frame (`tube.py`) |
| Physical bounds of a Lie tube | `Lie/PhysicalOutput` |
| Plots, PDF reports | everything above |

## 7. What changes in the code

Today's six approaches fall into the layers like this:

| Today | Layer | Becomes |
|---|---|---|
| `structure` | L2 | part of `dynacert MODEL.mo` (assessment) |
| `lmi`, `layered` | L3 | methods under `certify` |
| `montecarlo`, `falsify` | L4 | `validate --sample`, `validate --search` |
| `tube` | L5 | `view tube` |

Proposed CLI:

```
dynacert MODEL.mo                         L2 findings + which L3 methods apply (and why not)
dynacert MODEL.mo certify [METHOD ...]    L3: one method, or the portfolio
dynacert MODEL.mo validate [--sample | --search]   L4 against the current certificate
dynacert MODEL.mo view tube|plots|report  L5
```

For the plugin interface, every plugin declares its layer:
- **L3 methods** also declare the model classes and claim shapes they accept.
- **L4 and L5 plugins** declare what they need, such as a current certificate or an error
  frame.

Assessment then reads like the matrix in §5, and `certify` can run the portfolio.

## 8. Open decisions

| # | Question | Suggestion |
|---|---|---|
| A1 | One `Spec.lean` per model, shared by all methods (as `lmi` and `layered` do now)? | Yes. `certify` refuses to overwrite a `Spec.lean` that differs |
| A2 | One certificate file per method (`Cert.lean`, `LayeredCert.lean`, ...)? | Yes, plus `certified.json` recording every method that built and the kept bounds |
| A3 | Deep embedding of the equations (D2) | Needed before any nonlinear flowpipe (§4.2) or interval method; not needed for §4.1 |
| A4 | Which proposed method first? | L1 gain (exact bounds for every LTI model) and the Lie log tube (flagship), as in the proposal |
| A5 | Claim shapes beyond peak and tube | Funnel first (cheap: Grönwall is in Mathlib), then `horizon`, then `unsafe` |
