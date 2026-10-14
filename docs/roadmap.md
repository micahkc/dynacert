# dynacert roadmap

dynacert is the formally verified successor to cp_reach. A user writes a Modelica model and
annotates what to certify. The tool compiles it with rumoca and searches numerically for a
certificate, then produces a Lean theorem about the model with no assumptions beyond the
annotated specification. This document covers the target architecture, how cp_reach maps
onto it, and the order of work.

## 1. Principles

1. **Python searches, Lean checks.** Every number is found in Python: Lyapunov matrices, LMI
   multipliers, gains, radii, Bernstein coefficients, PSD factorizations. Lean never solves or
   searches anything. It checks exact rational data by kernel computation (`decide +kernel`) and
   applies theorems proved once in the library.
2. **No assumptions.** Every theorem in the library is fully proved, with axioms limited to
   `propext`, `Classical.choice`, `Quot.sound`, and no `sorry` or `native_decide`. A final
   certificate has only one kind of hypothesis: the specification the user wrote (disturbance
   bounds, reference envelope, initial set, parameter ranges). A method that would need an
   unproved hypothesis is not available until that hypothesis is a theorem.
3. **The claim is fixed by the model, not by the method.** The theorem statement (`Spec.lean`)
   is generated from the model and its annotations only. Which methods are chosen, and what
   numbers they produce, affect only whether the proof builds. A wrong choice or bad numbers
   make the build fail; they cannot weaken the claim.
4. **One source for both views.** The Lean equations and the Python model come from the same
   rumoca DAE IR in one compilation. If they ever disagree, the certificate fails to check;
   nothing unsound is produced.
5. **Proved once, used per model.** Each method has a soundness theorem proved once by hand.
   Per model, only data and the wiring between proved pieces are generated.

## 2. Architecture

```
Model.mo + __Dynacert(...) annotations
   │
   │ rumoca (one DAE IR)
   ├── lean-dae target ──► Model.lean      equations (trusted transcription)
   └── python target   ──► model.py        same equations + annotations as data
                              │
                 dynacert (Python, untrusted)
                   select methods from annotations and model structure
                   numeric search (cvxpy, scipy, ...)
                   exact rounding to ℚ, factorization, margins
                   emit Lean from templates
                              │
        Spec.lean   the claim (from model + annotations only)
        Link.lean   model equations ⇒ structure each method needs
        Cert.lean   certificate data + composition proving Spec
                              │
                 lake build (Lean kernel) ──► theorem, axiom audit
                              │
                 dynacert (Python): simulation, Monte Carlo, plots of the certified sets
```

### Responsibilities

| Component | Role |
|---|---|
| **rumoca** | Modelica → DAE IR. `lean-dae` target (Mathlib specification), a Python target (same IR, symbolic), simulation targets for validation. Passes `__Dynacert` annotations through to templates. |
| **gnc_lean** | General mathematics: SE₂(3) exp/log/Jacobians, exact log error dynamics, tubes and first-exit arguments, cascades, Bernstein enclosures, contraction. Fully proved under the same axiom policy. |
| **dynacert (Lean)** | Exact certificate checkers (`PSDWitness`, LMI ↔ quadratic form), method soundness theorems that compose gnc_lean results, the certificate result type, templates for `Spec`/`Link`/`Cert`. |
| **dynacert (Python)** | Method selection, numerical search, rational rounding, Lean emission, CLI, simulation and plotting. Untrusted throughout. |

New general results (true for any model, not tied to the pipeline) go into gnc_lean. dynacert
keeps the pipeline-specific layer.

### Trusted base

- The Lean kernel, Mathlib, gnc_lean, and dynacert's Lean library.
- rumoca's Modelica → `Model.lean` transcription.
- Reading `Spec.lean`, which is short and generated directly from the annotations.

Not trusted: the Python package, numerical solvers, floating point, method selection, and
rumoca's Python and simulation targets.

## 3. Methods

A method is a pair:

```
dynacert/methods/<name>.py        search + rounding + emission          (untrusted)
Dynacert/Methods/<Name>.lean      certificate structure + soundness      (proved once)
```

The certificate structure lists the data (rational matrices, scalars, witnesses) and the
facts the kernel checks about it. The soundness theorem turns a checked certificate into a
bound in a common result type: for every solution of the model satisfying the specification
hypotheses, each certified output stays within its bound. Compositions (cascade, change of
coordinates, algebra → group) are methods too: they take results and produce results.

### Catalog

| Method | Python finds | Lean checks | Proof status |
|---|---|---|---|
| **LTI dissipation** | P, α, γ (cvxpy LMI), rounding, LDLᵀ | `PSDWitness` of the LMI; `LTICert` soundness | Done (MassSpringDamper) |
| **Ellipsoid → box** | per-state bounds, factorization | `BoxCert` | Done |
| **Multi-channel disturbance** | P, α, μⱼ per channel | LMI with diag(μ); bound Σμⱼwⱼ² | Small extension of LTI |
| **Output bound** (z = Cx + Dw) | second LMI, γ = √(μ₁+μ₂) | two `PSDWitness`es | To write |
| **Initial-condition sets** | ellipsoid/box inclusion witness | V(x₀) ≤ c | To write |
| **Polytopic (parameters, references)** | common P over vertices | vertex LMIs + convex-hull step (`PolytopicTube.vertex_supply`, gnc_lean) + model affine in parameters | Needs ℚ LMI → `hvertex` bridge |
| **Polytope + residual** | P, sector gain γ, region radius ρ | `PolytopicResidualTube.certificate` (gnc_lean) | Needs bridge |
| **Nonlinear via Jacobian enclosure** | interval/Bernstein enclosure of the Jacobian entries, common P | enclosure check (gnc_lean Bernstein, trig bounds) + vertex LMIs + `Contraction.differential_to_incremental` | To write |
| **SE₂(3) log tube** | algebra controller K, P over reference-box vertices, residual radius | see §5 | Main new theorem |
| **Cascade** | inner and outer certificates, small-gain weights | `CoupledTube` (gnc_lean) | To wire |
| **Reference envelope** | trajectory, Bernstein coefficients of ā, ω̄ | `BernsteinPolynomial.checked_sound` (gnc_lean) | To wire |
| **Time-varying metric P(t)** | polynomial P(t) | PSD for all t ∈ [0,T] (Bernstein or SOS in t) | Open: neither library has it |

## 4. Annotations

rumoca currently parses annotations into the AST and drops them before the DAE IR. Only fixed
keys (`Evaluate`, `Inline`, `experiment`, `__rumoca(Solver…)`) are used. The change is
vendor-neutral: any `__Vendor(...)` subtree is passed through to templates.

- **Variable level.** Follow the path `description` already takes:
  `InstanceData` → flat `Variable` → DAE `VariableAttributes` (+ wire form, schema bump) →
  `dae_backend.rs` projection as `attributes.vendor_annotations`.
- **Model level.** Read `ClassDef.annotation` the way `experiment_settings_for_model`
  (`rumoca-compile/src/experiment.rs`) reads `experiment`, and expose it to templates as
  `model_annotations`.
- **Equation level** would need grammar changes. Nothing below uses it.

This is the "Lie group annotations … geometry must survive elaboration" item in rumoca's
SPEC_0052.

### Vocabulary (draft)

```modelica
input Real d          annotation(__Dynacert(disturbance(bound = 1.0, norm = "2")));
input Real x_ref      annotation(__Dynacert(reference(min = -1, max = 1)));
Real e                annotation(__Dynacert(certify));
parameter Real m = 1  annotation(__Dynacert(uncertain(min = 0.9, max = 1.1)));

model Quadrotor
  // ...
  annotation(__Dynacert(
    initial(box = {...}),
    lieGroup(type = "SE23", error = "left",
             rotation = {R11,R12,R13,R21,R22,R23,R31,R32,R33},
             velocity = {vx,vy,vz}, position = {px,py,pz},
             angularVelocity = {wx,wy,wz}, acceleration = {ax,ay,az})));
end Quadrotor;
```

Every annotation either appears in `Spec.lean` as a hypothesis the user can read (bounds,
envelopes, initial sets, parameter ranges) or is checked in `Link.lean` (structure claims such
as `lieGroup`). A `lieGroup` annotation on states that do not satisfy SE₂(3) kinematics fails
to build.

Feedforward and reference cancellation is not annotated. The controller that computes it
belongs in the Modelica model, so the cancellation follows from the equations.

These annotations replace cp_reach's `uncertainty.yaml`, `reach_query.yaml`, and `*_lie.json`.

## 5. SE₂(3) / Lie-group certificates

The log-coordinate bound is tighter than a Euclidean one for two reasons:

- For group-affine kinematics the log error dynamics are exactly linear in ξ apart from the
  input forcing.
- The certified ellipsoid in the algebra maps through exp to a correlated set, rather than
  through an outer box.

gnc_lean already proves most of the chain:

| Step | gnc_lean |
|---|---|
| SE₂(3), 5×5 embedding, ad, exp | `Lie/SE23.lean`, `Lie/Exponential.lean` (`groupExp_toMatrix`) |
| Left Jacobian and inverse, d/dt exp | `Jacobian.blockLeft`/`blockInverse`, `matrixExp_curve_derivative_all` |
| Principal log, chart ‖ξ_R‖ < π | `Lie/PrincipalLog.lean` (`log_exp`, `isOpen_domain`) |
| Component ODE ⇔ group ODE | `spacecraft_ode_iff` (`Dynamics/RigidBodyKinematics.lean`) |
| Exact log error dynamics (left error Y⁻¹X), chart needed only at t | `principal_proposition1_at` (`Control/LocalLogBackstepping.lean`) |
| Input distortion J⁻¹(ξ) residual bounds | `control_residual_bounds` (`Lie/ControlResidual.lean`) |
| SO(3) Jacobian norms | `left_operatorNorm`, `leftInv_operatorNorm` (`Lie/Jacobian.lean`) |
| Algebra → position bound | `leftAt_nonexpansive` (`Dynamics/LieErrorReconstruction.lean`) |
| Group-affine test | `group_affine_iff` (`Dynamics/SpacecraftGroupAffinity.lean`) |
| Polytope + residual + first exit | `PolytopicResidualTube.certificate` |

### Certificate chain

1. **Link.** From rumoca's `Equations`, regroup the annotated states and prove
   `SpacecraftODEAt` (ṗ = v, v̇ = Ra + g, Ṙ = R[ω]×) and that R stays in SO(3).
2. **Error dynamics.** Use `principal_proposition1_at` to split the closed loop into
   (A_C − ad_n̄ + BK)ξ plus a residual.
3. **Residual bound.** Use `control_residual_bounds` to bound the residual by α(θ), β(θ)
   terms on the certified set (a sector bound).
4. **Vertex LMIs.** Check the vertex LMIs over the reference box with `PSDWitness`. The
   reference box itself is checked by Bernstein bounds.
5. **Tube.** First exit (`PolytopicResidualTube`) gives invariance. The set is chosen inside
   ‖ξ_R‖ < π, so the chart condition is part of the conclusion, not a hypothesis.
6. **Outputs.** Map to physical bounds: ‖Δp‖ ≤ ‖ξ_p‖ through `leftAt_nonexpansive`, attitude
   angle from ‖ξ_R‖, sub-ellipsoid witnesses for ‖ξ_p‖ and ‖ξ_R‖.
7. **Cascade.** Couple the inner angular-rate loop with `CoupledTube`.

Python's part of this chain is the algebra-coordinate controller, P over the vertices, the
radius fixed point at which the residual bound closes, rounding, and witnesses.

### To prove

- **SE₂(3) log tube with forced error.** `OrbitalLogTube.certificate` assumes a shared input
  between vehicle and reference. The quadrotor needs the same first-exit structure with the
  forcing term from `principal_proposition1_at`. This is the main new theorem, assembled from
  existing pieces.
- **SO(3) invariance.** Ṙ = R[ω]× ⇒ RᵀR constant, so a model with 9 scalar R entries stays a
  rotation. Alternatively the model uses quaternions (`foh_quaternion_to_rotation`).
- **Attitude-angle output.** angle(R̄ᵀR) = ‖ξ_R‖.
- **Velocity-channel disturbances.** These need an operator-norm bound on the full
  `blockInverse`. Avoid them by modeling disturbances as acceleration and torque, which enter
  through `controlInput`.

### Notes from cp_reach

- Follow gnc_lean's forms, not cp_reach's code.
  `Applications/DynamicInversion/Review.lean` records corrections to Lin, Goppert & Hwang (TAC
  2024): the sign of the printed inverse in eqs. (16)/(17), the Appendix C coefficients c₁
  and c₃, and the nonvanishing-determinant claim.
- The exact form takes ad at the true input; gnc_lean's re-centering identities move it to
  the reference input plus a correction.
- Use one error convention throughout (left error Y⁻¹X, as in gnc_lean). cp_reach uses
  Log(X⁻¹X̄) for the quadrotor and X̄⁻¹X for the satellite.
- Report bounds in the frame they hold in. cp_reach's `check_containment` compares algebra
  coordinates against group/Euler bounds.

## 6. Porting cp_reach

| cp_reach | dynacert | Side |
|---|---|---|
| `ir/loader.py`, `ir/ast_parser.py`, `ir/state_space.py` | rumoca Python target from the same IR | Python |
| `dynamics/state_space.py`, `classification.py` | model inspection and method selection | Python |
| `reachability/lmi.py` (multi-channel peak bound, output gain) | LTI, multi-channel, and output-bound methods | both |
| `reachability/polytopic.py` (corner substitution) | Jacobian enclosure method (sound for sin/cos) | both |
| `reachability/certification.py` (estimated Lipschitz grid) | time-varying metric method (open) | both |
| `reachability/cascaded.py`, `physics/rigid_body.py`, `physics/angular_acceleration.py`, `development/applications/quadrotor/` | SE₂(3) log tube + cascade | both |
| `ellipsoids.py`, ellipsoid sampling | box and sub-ellipsoid witnesses; sampling stays for plots only | both |
| satellite HCW, TH-LTV | LTI and polytopic examples | both |
| satellite SE₂(3), Δv planning | SE₂(3) method; planning stays Python | both |
| `planning/` (min-snap) | reference generation; envelope checked by Bernstein | Python + check |
| `workflows.simulate_dist`, `frequency_sweep`, Monte Carlo | validation through rumoca simulation targets | Python |
| `plotting/` | plots read the certified rational data | Python |
| `config/uncertainty.py`, `config/query.py` | `__Dynacert` annotations | rumoca + Python |
| rover EMI / rollover geometry | example or out of scope | Python |
| EKF (stub) | estimator-error certificates (future) | both |

cp_reach behaviors that do not carry over as-is, because they are not sound:

- solver output accepted without an exact re-check;
- Jacobian vertices from corner substitution (not a hull for sin/cos);
- an estimated Lipschitz constant;
- the layer-1 ω bound only warned on, never enforced;
- B = I in place of J⁻¹(ξ);
- reachable-set bounds from boundary sampling;
- a single max|·| point in place of a vertex cover.

## 7. Phases

### Status (2026-10-05)

- **Phase 0: done.**
  - dynacert is on Lean/Mathlib v4.29.1 with gnc_lean as a Lake dependency.
  - rumoca branch `dynacert-lean` passes vendor annotations through, ships the `lean_dae`
    and `sympy_dae` targets, and emits `IsSolutionOn`.
  - `dynacert check` certifies `ClosedLoopComposed`, `ClosedLoop`, and `ClosedLoopUncertain` from
    annotated `.mo` files, with no hand-written Lean.
- **Phase 1: partly done.** Done:
  - ℚ LMI → gnc_lean supply bridge (`Linear/Supply.lean`);
  - per-channel disturbances;
  - linear and block-norm outputs;
  - initial conditions;
  - reference-driven error coordinates;
  - polytopic parameter uncertainty (global and regional).

  Open: output feedthrough (`D w`), Euclidean disturbance groups, HCW/TH-LTV examples.
- **Phase 2: Lean core done.**
  - `Lie/LogErrorWithin` (right-derivative log error dynamics);
  - `Lie/LogTube` (chart-closing first-exit tube);
  - `Lie/SO3` (9-scalar rotation stays in SO(3));
  - `Lie/PhysicalOutput` (position, velocity, and attitude bounds).

  Open: a controller-specific supply theorem (vertex LMIs + `control_residual_bounds`), the
  generator, and the quadrotor example.
- **Monte Carlo validation: done** ([montecarlo.md](montecarlo.md)). `Prob/Scenario`
  (scenario and zero-failure bounds, proved). `montecarlo.py` simulates i.i.d. admissible
  scenarios through rumoca's native solver (generated harness) or the sympy export, reports
  agreement and tightness, cross-checks the two paths, and runs a cross-entropy falsifier.
- **Approach registry (proposal M2, partly):** `dynacert MODEL.mo` assesses every approach
  (`approaches/`: `lmi`, `montecarlo`, `falsify`), and `dynacert MODEL.mo APPROACH` runs one.
  Open: `Spec.lean` is still emitted by the LTI path ([approaches.md](approaches.md)).
- **Phase 3: started.** `Nonlinear/Enclosure` (mean-value gains, `cos` enclosure) and
  `PolytopicCert.regional_invariant`. Open: the generator for nonlinear models.


### Phase 0: plumbing

Exit: `cp_reach/examples/general/models/closed_loop.mo` goes to a checked theorem with no
hand-written files.

- Move dynacert to gnc_lean's toolchain (Lean/Mathlib v4.29.1) and add gnc_lean as a Lake
  dependency. Adopt its axiom audit. Pin rumoca's `lean-dae` template to the same version.
- Move `lean_target/` into the rumoca repository. Add the vendor-annotation pass-through.
- `lean-dae`: add `IsSolutionOn T` with right derivatives on `[0, T)`, so step disturbances
  are admissible.
- Add a rumoca Python target from the DAE IR.
- Restructure `oracle/` into a `dynacert` Python package with the CLI `dynacert check Model.mo`
  (rumoca → search → emit → `lake build` → plots).
- Generate `Spec.lean` and `Link.lean`.
- Prove the change to error coordinates for `ClosedLoop` in Lean, with the feedforward
  controller included in the model.
- Plotting from certified data.

First prototype (2026-10-05): `MSDError.mo` → rumoca `lean-dae` → hand-written link file →
`MassSpringDamper.reach`. This has since been replaced by the generated pipeline, which also
derives the error coordinates from the model.

### Phase 1: linear parity with cp_reach

Exit: every linear cp_reach example certified, with plots.

- ℚ matrix LMI → quadratic-form bridge in gnc_lean's `hvertex` form. Every later method
  depends on it.
- Multi-channel disturbances, with an explicit norm semantics (Euclidean ball vs
  componentwise).
- Output bounds and initial-condition sets.
- Polytopic parameter uncertainty.
- HCW and TH-LTV satellite examples.

### Phase 2: SE₂(3) quadrotor

Exit: the cp_reach quadrotor flowpipe example certified, with no hypotheses beyond its
annotations.

- SE₂(3) log tube theorem with forced error.
- SO(3) invariance and the attitude-angle output.
- Reference envelope through Bernstein.
- Angular-rate cascade.
- Python: algebra controller, vertex LMI, radius fixed point, emission.

### Phase 3: nonlinear systems

Exit: the cp_reach pendulum example certified.

- Jacobian enclosure method (Bernstein / trig bounds) with contraction or polytope + residual.
- Time-varying metrics: PSD of P(t) for all t, by Bernstein or SOS in t.

### Phase 4: beyond cp_reach

- SOS storage functions and barrier certificates.
- Estimator-error certificates.
- Sampled-data and timing models (rumoca SPEC_0052 §2).
- Counterexample search and replay in simulation when a certificate fails (SPEC_0052 §5).

## 8. Open decisions

- **Toolchain.** Moving dynacert to v4.29.1 is small; porting gnc_lean forward is large
  (208k lines, internal Lean API in its audit, 7k kernel checks). Proposed: follow gnc_lean's
  pin.
- **Disturbance norm.** cp_reach treats each channel as a peak Euclidean bound; dynacert's LTI
  method uses wᵀw ≤ μ. Pick one default and make the annotation explicit.
- **rumoca upstream.** Propose the vendor-annotation pass-through upstream, or keep it on a
  fork until the vocabulary settles.
- **cp_reach.** Archive it after Phase 1 reaches parity, or keep it as the place for
  experiments.
