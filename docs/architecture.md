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
| L2 | `structure.py` (findings), `approaches/lmi.nonlinear_terms`, `pipeline.linear_problem`, `scalarize.py` (array elements as scalar coordinates) |
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
| Funnel | `V(z(t)) ≤ ρ(t) = V₀e^{-αt} + (γμ/α)(1 − e^{-αt})`, shrinking from a nonzero initial set | `initialSet(min, max)` on states | done for LTI and LPV (`Cert.funnel`, `Linear/Funnel.lean`; `ClosedLoopInitial`) |
| Finite-horizon reach set | `∀ t ∈ [0, T], x(t) ∈ R(t)` | `horizon` | proposed (D4) |
| Safety / reach-avoid | `x(t) ∉ Unsafe`, possibly reaching a goal | `unsafe(...)`, `goal(...)` | proposed (D4) |
| Controlled invariance (viability) | `∃` admissible control keeping `x(t) ∈ S` against every disturbance | `control(bound)` on free plant inputs, `constraint(...)` | proposed |
| Temporal specs (STL) | e.g. settles within τ | `stl(...)` | idea |

Chance constraints such as `P(peak > s) ≤ ε` are not claims. They are L4 statements about a
sampling distribution, backed by `Dynacert.Prob`.

## 3. L2: model classes

Structure discovery classifies the model. The class decides which L3 methods are tried. Each
property a certificate relies on is re-proved from `Model.lean` (the Link step), so a wrong
classification fails the build.

| Class | Test (L2) | Example | Methods that apply (L3) |
|---|---|---|---|
| LTI in error coordinates | `f` linear in states, references and disturbances | `ClosedLoop` | quadratic dissipation, polyhedral RPI, L1, zonotope |
| LTI plant with free control inputs | linear, some inputs annotated `control` | — | polyhedral controlled invariance |
| LPV / polytopic | linear, `A` multi-affine in uncertain parameters | `ClosedLoopUncertain` | common quadratic over vertices |
| Layered / cascade | the state-dependency graph splits into components | `TwoMassLayered` | composition of per-layer certificates |
| Lie-group kinematics | `Ṙ = R[ω]×`, `ṗ = v`, `v̇ = Ra + g` (SE₂(3)) | `SpacecraftTracking` (first target), `QuadrotorTracking` (underactuated, open) | log-error tube (+ residuals) |
| Smooth nonlinear | explicit ODE, analytic `f` | `PendulumPD` | Jacobian enclosure, contraction, SOS, Taylor models |
| Polynomial | `f` polynomial | — | SOS storage, barriers |
| Sampled-data / clocked | Modelica clocks, `sample` | — | e^{Ah} enclosure + intersample bound |
| Hybrid | events, `when`, piecewise | — | none yet |

The classes are not exclusive. A quadrotor is layered, attitude then translation, and each
layer is Lie-group. Composition (§4.5) is what lets one model use several methods.

## 4. L3: where certificate methods come from

Every certificate method is a pair: an untrusted search that produces exact data, and a
soundness theorem proved once in Lean that turns checked data into the claim. The methods
come from four mathematical families, plus combinators that join them.

### Overview

The first five columns are the usual comparison of reachability methods. The last two say
what each needs in Lean and where it stands in dynacert.

| Approach | Practical dimension | Horizon | Exactness | Dynamics | Lean check | dynacert |
|---|---|---|---|---|---|---|
| HJ reachability | ~5–6 (grid) | finite or infinite | near-exact, not formally sound | general nonlinear, games | none: a grid value function is not a checkable certificate | out of scope (L5 picture at most) |
| Set propagation, linear (§4.3) | hundreds and up | finite | tight, small conservatism | linear | rational e^{Ah} enclosure + per-step containment | proposed |
| Set propagation, nonlinear (§4.3) | ~5–20 | finite | grows with time (wrapping) | nonlinear | interval / Taylor-model arithmetic over a deep embedding (D2) | after D2 |
| LMI ellipsoids (§4.1) | hundreds | infinite | conservative shape | linear, uncertain-linear | `PSDWitness` | **done** (`lmi`) |
| SOS (§4.1) | ~6–12 | infinite | moderate, degree-dependent | polynomial | polynomial identity + Gram `PSDWitness` | proposed |
| Polyhedral, fixed K (§4.2) | tens | infinite | exact (in the limit) | linear | Metzler / LP-multiplier identities over ℚ | **done** v1 (`polyhedral`; LTI, fixed x₀; see docs/polyhedral.md) |
| Polyhedral, controlled (§4.2) | ~4–6 explicit, more implicit | infinite | exact | linear | vertex inequalities + convexity | proposed (needs a new claim shape) |
| Peak-to-peak gain (§4.4) | hundreds | infinite | exact for the peak | linear | variation of constants + impulse-response enclosure | proposed (M5) |

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
| Polytope + residual | nonlinear, Lie | P, sector gain, radius | `Lie.residual_supply` (any real inner-product space; vertex LMIs + sector residuals); gnc `PolytopicResidualTube.certificate` | Lean done; used by the Lie tube |
| Lie log-error tube | SE₂(3) | algebra controller, vertex LMIs, radius fixed point | `Lie.log_tube_of_residuals`, `Lie.pd_field`, `Lie.pdResidual_le`, `Lie.pd_spacecraft_tube` | Lean done for a PD law and a coasting reference (`Lie.pd_spacecraft_tube`); generator in progress; general controllers and moving references (vertex polytope over ā, ω̄) open |
| Contraction metric | smooth nonlinear | metric LMI over the Jacobian enclosure | gnc `GNC.Contraction.differential_to_incremental` | proposed |
| Time-varying metric P(t) (funnels) | nonlinear along a trajectory | polynomial P(t), Bernstein | matrix-Bernstein PSD lemma + Grönwall | proposed (M6) |
| SOS storage / barrier | polynomial | SOS programme | polynomial identity + Gram `PSDWitness` | proposed (Phase 4) |

### 4.2 Polyhedral invariant sets

The set is a polytope `S = {x | Hx ≤ h}` instead of an ellipsoid. These are the invariant sets
of the MPC literature: terminal sets, tube MPC, and constraint tightening. Their certificates
are exact linear algebra over ℚ, so they need no PSD factorization and no rounding margin.

**Fixed K: robust positively invariant (RPI) sets.** The model is a closed loop
`ẋ = Ax + Bw`, `|w| ≤ δ`. In continuous time, `S` is invariant if there is a Metzler matrix `M`
(nonnegative off the diagonal) with

```
H A = M H      and      M h + |H B| δ ≤ 0
```

Then `y = Hx − h` satisfies `ẏ ≤ M y` componentwise, and a cooperative-system comparison keeps
`y ≤ 0`. On a face (`Hᵢx = hᵢ`, `Hⱼx ≤ hⱼ`), the step bounding `Σ_{j≠i} Mᵢⱼ Hⱼx` needs
`Mᵢⱼ ≥ 0`, which is where the Metzler condition enters. With only `≤ 0`, the boundary
derivative can be zero, so a plain first-exit argument does not close the proof. Either:
- require a strict margin `Mh + |HB|δ < 0`, which matches the rational-margin policy and the
  existing first-exit machinery; or
- prove the Metzler comparison lemma (`e^{Mt} ≥ 0`). Output bounds `|c x| ≤ b` on `S` follow from LP duality: multipliers `λ ≥ 0` with
`λᵀH = ±c` and `λᵀh ≤ b`, also checked exactly.

- **Search** (Python): directions `H` (box, symmetric facets, or support directions of an outer
  approximation of the minimal RPI set à la Raković), then an LP for `h` and `M`. `HA = MH`
  is a linear equality, so an exact rational LP or a projection onto its solution space keeps
  it exact.
- **Lean, proved once:** first exit under the strict margin (or the Metzler comparison lemma),
  for right derivatives, in the same shape as `Core/Dissipation`; and LP-duality output bounds. Per model: rational identities checked by
  `decide +kernel`.
- **Tightness:** the minimal RPI set is the closure of the set reachable from 0. Under
  *componentwise* disturbance bounds, its support function in direction `c` is the weighted L1
  norm of the impulse response, `Σⱼ δⱼ ∫₀^∞ |cᵀ e^{As} bⱼ| ds`. That is the induced
  L∞ → L∞ gain from `w` to `cᵀx`. For a Euclidean disturbance ball the integrand becomes
  `‖cᵀ e^{As} B‖₂`. Polyhedral outer
  approximations therefore converge to the exact supremum over all time (0.7557 for
  `ClosedLoop`; 0.7500 on `[0, 10]`), against 0.8438 from the ellipsoid. This is an alternative route to M5's exact bounds that avoids
  enclosing the matrix exponential.

**Controlled invariance.** The model is a plant `ẋ = Ax + Bu + Ew` with control inputs `u`
in a polytope `U`. The maximal controlled invariant set is the set of states from which
*some* admissible control keeps the state in the constraint set against every disturbance.

- **Certificate:** for each vertex `vᵢ` of `S`, a control `uᵢ ∈ U` such that the field points
  inward against every disturbance vertex (Nagumo at the vertices). Convexity then gives a
  continuous, piecewise-linear vertex controller (Gutman–Cwikel) that keeps the whole set
  invariant.
- **Claim:** a new shape, `∃` a feedback that keeps `x(t) ∈ S` (§2), with control inputs
  annotated in the model.
- **Practical dimension:** about 4–6 when the vertices are explicit, because the number of
  vertices grows quickly.
- **A synthesis loop:** the vertex controller can be emitted back to Modelica. The closed
  loop is then certified by the fixed-K route above.

### 4.3 Set propagation (flowpipes)

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

### 4.4 Input–output characterizations

Bound the output directly from the input with an exact gain, without a set. The proof is
variation of constants plus an enclosure of the impulse response.

| Method | Model class | Lean needs | Status |
|---|---|---|---|
| Peak-to-peak (L1) gain | LTI | variation of constants for `IsSolutionOn`, enclosure of `\|C e^{As} B\|`, exponential tail bound | proposed (M5); the tightest possible bound for LTI |
| IQC / multipliers | LTI + structured nonlinearity | frequency-domain inequality → KYP LMI | idea |

### 4.5 Combinators

These are not methods by themselves. They take certificates and produce certificates, and they
are how one model combines several methods.

| Combinator | From → to | Lean |
|---|---|---|
| Change of frame | model coordinates → error coordinates (linear, Lie log) | generated Link (`linear_combination`, `LieLink`) |
| Ellipsoid → box / output | set → `\|yᵢ\| ≤ b` | `BoxCert` |
| Algebra → group | log-coordinate set → physical position, velocity, attitude | `Lie/PhysicalOutput` |
| Vertex hull | per-vertex inequality → all parameters in the box | gnc `GNC.PolytopicTube.vertex_supply` |
| Assume–guarantee | per-layer bounds with assumptions → whole model | `Compose.assume_guarantee` |
| Coupled energy | joint weighted storage when peak composition fails | gnc `GNC.CoupledTube.invariant_tube` |
| Portfolio | several methods → keep the tightest bound | min over certified bounds; trivial in Lean |

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

| | peak bound | tube / invariant | funnel | finite-horizon reach | safety | controlled invariance |
|---|---|---|---|---|---|---|
| LTI | ✓ dissipation, ✓ polyhedral RPI, ○ L1, ○ zonotope | ✓ ellipsoid, ✓ polytope | ✓ Grönwall | ○ zonotope | ○ via reach set or polytope | — |
| LTI plant + control inputs | — | — | — | — | ○ polyhedral | ○ polyhedral |
| LPV | ✓ vertices, ○ polyhedral (vertex Metzler conditions) | ✓ | ✓ Grönwall | ○ | ○ | ○ |
| Layered | ✓ assume–guarantee (linear layers, state outputs, no references or uncertain parameters) | ✓ per layer | ○ | ○ | ○ | — |
| Lie SE₂(3) | ○ log tube + physical outputs (Lean done for PD + coasting reference) | ○ | ○ | — | ○ via tube | — |
| Smooth nonlinear | ○ enclosure, ○ contraction | ○ regional | ○ P(t) | ○ Taylor models (after D2) | ○ barrier | — |
| Polynomial | ○ SOS | ○ SOS | ○ SOS in t | ○ | ○ barrier | ○ SOS |
| Sampled-data | ○ e^{Ah} | ○ | — | ○ | ○ | ○ (discrete-time polyhedral) |
| Hybrid | — | — | — | — | — | — |

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

**Status (2026-10-14): implemented.** `dynacert MODEL.mo` prints the assessment grouped by layer;
`certify [METHOD ...]` (portfolio by `cost`), `validate [--sample|--search]`, and `view
tube|plots|report` run the plugins by their `layer`; the direct `dynacert MODEL.mo APPROACH` form
is unchanged. Plugins declare `layer`, `classes`, `claims`, `cost` (`approaches/base.py`) and are
discovered automatically. A1 and A2 (§8) are implemented in `certindex.py`: `source_hash` in
every sidecar, `certificates.json` with the kept bounds, and removal of certificate files of an
old `Spec.lean`. See [approaches.md](approaches.md).

Today's six approaches fall into the layers like this:

| Today | Layer | Becomes |
|---|---|---|
| `structure` | L2 | part of `dynacert MODEL.mo` (assessment); `structure --lean` (emits and builds `LieLink.lean`) becomes the Link step of the Lie method under `certify` |
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

Structure discovery runs on every assessment. It is cheap except for symbolic elimination on
larger models (about 17 s for `QuadrotorTracking`, 34 s for `SpacecraftTracking`), so its
findings stay cached in `prob.cache["structure"]`.

## 8. Open decisions

| # | Question | Suggestion |
|---|---|---|
| A1 | One `Spec.lean` per model, shared by all methods (as `lmi`, `layered`, and the planned Lie certificate do; all emit it with `emit_lti.emit_spec`)? | Yes. A differing `Spec.lean` means the model or its annotations changed. `certify` then regenerates it and invalidates or rebuilds every certificate file in that directory, so no stale certificate proves an old claim next to a new model. Each sidecar records a hash of `source.mo` and the annotations, which makes the staleness check mechanical |
| A2 | One certificate file per method? | Yes: `Cert.lean` (lmi), `LayeredCert.lean`, and planned `LieCert.lean` + `LieLink.lean`. `certified.json` records every method that built and the kept bounds |
| A3 | Deep embedding of the equations (D2) | Needed before any nonlinear flowpipe (§4.3) or interval method; not needed for §4.1–4.2 |
| A4 | Which proposed method first? | Exact LTI bounds by either polyhedral RPI (§4.2: exact rational checks, no matrix exponential) or the L1 gain (§4.4); then the Lie log tube (flagship) |
| A5 | Claim shapes beyond peak and tube | Funnel done (`initialSet`, `Cert.funnel`); next `horizon`, then `unsafe` |
