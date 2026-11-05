# rumoca changes needed for the full-stack quadrotor

**Update 2026-10-19 (later): items 1–7 are done** in
`/home/micah/Research/development/rumoca/lean_target/rumoca-dynacert-pinned` (set
`DYNACERT_RUMOCA` to it). Item 8 is open. dynacert now syncs rumoca's per-function modules
`Rumoca/Fn/<Modelica/path>.lean` into its own `Rumoca/` (`pipeline.sync_rumoca`). Both
`ClosedLoop` and `ClosedLoopPID` elaborate in Lean, and `ManeuverPID` is back to the nested
redeclare. Two small follow-ups came up:

| # | Change | Why |
|---|---|---|
| 9 | sympy-dae: compute `EQUATIONS` lazily (e.g. a PEP 562 module `__getattr__`) | Importing the QuadrotorFullStack module takes 66 s, because `EQUATIONS = equations()` inlines every function call at import. dynacert builds its own view with `equations(call=…)` and never uses the inlined list. |
| 10 | lean-dae: `set_option linter.style.longLine false` in `Rumoca/Fn/**` modules (as `Model.lean` does) | dynacert builds with Mathlib's standard linter set, so `Rumoca/Fn/LieGroups/SE23/Quat/left_jacobian.lean` and others print a warning for every long line. dynacert can't edit these copies, because they must match rumoca's text. |

Found while adding array support to dynacert's linear methods and Monte Carlo (2026-10-22):

| # | Change | Why |
|---|---|---|
| 11 | Python binding: set one element of an array parameter (`params={'sys.c[1]': …}`), or accept a list for `sys.c` | Monte Carlo samples uncertain array parameters per component. Today it gives "unknown parameter", so dynacert's harness wraps each array in one scalar parameter per element. |
| 12 | sympy-dae: support `identity(n)` | `unsupported-feature:sympy-dae-scalar:integer`. |
| 13 | lean-dae: accept matrix literals written `[a, b; c, d]` | `{{a, b}, {c, d}}` works; the MATLAB-style form is rejected. |
| 14 | casadi-ode: support `m * der(v[i]) = …` | It fails with `residual_equations`, which blocks dynacert's collocation-based falsifier on array models. |

The original list follows.

Status: 2026-10-19. Driving model: [`examples/aerospace/QuadrotorFullStack.mo`](../examples/aerospace/QuadrotorFullStack.mo),
a full-stack quadrotor on SE₂(3) written against `modelica_models/LieGroups`. It has a replaceable
controller with two implementations: `ClosedLoop`, the log-linear SE₂(3) controller, and
`ClosedLoopPID`, an ArduCopter-style PID cascade. Both simulate correctly with `rumoca sim`.
Neither reaches dynacert, because rumoca's `lean-dae` and `sympy-dae` targets reject them.

The list was found by rendering both closed loops through scratch copies of the two templates,
lifting one gate at a time. With items 3–6 handled, **both closed loops render on both targets**.
Nothing else in the model is rejected.

Repro files are in [`rumoca-repros/`](rumoca-repros/). Commands below assume

```bash
R=/home/micah/Research/development/rumoca/rumoca-dynacert-target/release/rumoca
T=/home/micah/Research/development/rumoca/rumoca-dynacert/examples/codegen
cd docs/rumoca-repros
```

| # | Change | Priority | Blocks |
|---|---|---|---|
| 1 | Nested `redeclare` is silently dropped | P0 (trusted base) | swapping controllers correctly |
| 2 | `constrainedby` modifiers ignored without a redeclare | P0 (trusted base) | correct start values / `Initial` |
| 3 | Functions in `lean-dae` and `sympy-dae` | P1 | everything: both controllers and the plant |
| 4 | Array slices `x[a:b]` | P1 | both controllers |
| 5 | `fill` | P1 | `motor_dev` output |
| 6 | Element-wise power on arrays `.^` | P1 (workaround exists) | `att_err` output |
| 7 | Single-file `--source-root` libraries resolving each other | P2 | explicit library roots |
| 8 | Clocks and events in `lean-dae` | later | sampled-data controller, estimator |

## P0: transcription bugs

rumoca's Modelica → `Model.lean` transcription is in dynacert's trusted base. A wrong
transcription still gives a valid Lean certificate, but for a model the user didn't write.
These two come first for that reason.

### 1. Nested `redeclare` is silently dropped

`Outer(cl(redeclare C2 ctrl))` keeps the default `C1`. The one-level form
`Loop(redeclare C2 ctrl)` works. MLS §7.3 allows redeclarations inside a nested modification.
This happens on the `dynacert-lean` branch and on `main` (cfe53b91d).

**Why.** Swapping the controller while keeping the plant and the claim fixed is the intended
workflow. `QuadrotorFullStack.ManeuverPID` was first written as
`Maneuver(cl(redeclare ArduPilotPID ctrl))`. It flew the log-linear controller with no warning,
and its results matched the default controller's exactly. A certificate of that model would have
been checked against the wrong controller.

**Fix.** Implement the nested redeclare, or reject it with an error.

```bash
$R compile NestedRedeclare.mo -m NestedRedeclare.Direct --emit flat-mo | grep "u ="   # ctrl.u = -(2*ctrl.x)   correct
$R compile NestedRedeclare.mo -m NestedRedeclare.Nested --emit flat-mo | grep "u ="   # cl.ctrl.u = -cl.ctrl.x  wrong (C1)
```

### 2. `constrainedby` modifiers are ignored when nothing is redeclared

In `replaceable Plant p constrainedby Plant(x0 = 5)`, the modifier `x0 = 5` is applied only after
a redeclare. MLS §7.3.2 applies the constraining clause's modifiers to the original declaration as
well. This also happens on `main`.

**Why.** Start values become the `Initial` hypothesis in `Spec.lean`, so the claim would be about
a different initial state than the one written. This bug, together with bug 1, is why
`QuadrotorFullStack.Maneuver` uses a replaceable class (`replaceable model Loop = ClosedLoop;
Loop cl(...)`).

```bash
$R compile ConstrainedbyMod.mo -m ConstrainedbyMod.Top  --emit flat-mo | grep "p.x0"   # = 0   wrong (should be 5)
$R compile ConstrainedbyMod.mo -m ConstrainedbyMod.Top2 --emit flat-mo | grep "p.x0"   # = 5   correct
```

## P1: export features

### 3. Functions (`unsupported-feature:{lean,sympy}-dae-functions`)

This is the main blocker. The template gate is at `model.lean.jinja:296` and `model.py.jinja:296`.

**Why.** All of the Lie-group arithmetic is in library functions. The log-linear loop keeps 15
in the DAE:

- `LieGroups.SE23.Quat.{inverse, product, log_map, left_jacobian}`
- `LieGroups.SO3.Quat.{to_DCM, kinematics, inverse, rotate, product, normalize, log_map, left_jacobian, left_jacobian_inv, wedge}`
- `LieGroups.SE3.Quat.left_Q`

The PID adds `SO3.EulerB321.to_Quat` and `Util.saturate`. The plant uses `to_DCM` and
`kinematics` too, so no controller gets through. Monte Carlo and falsification are blocked as
well, since dynacert loads every model through `sympy-dae`.

**Already in place.** The DAE IR (`--emit dae-json`, `storage.functions`) already holds every body
as a straight-line list of assignments, with `if` lowered to conditional expressions
(`function_aggregate_lowering`). The only remaining loop is one `for` in
`SE23.Quat.left_jacobian`. A transcription can therefore be a `let` chain.

**Requirements and why each matters:**

- **One shared definition per function.** Emit each function once, as a `noncomputable def`
  named by its full Modelica path (`LieGroups.SE23.Quat.log_map`). Put it in a module shared
  across models, e.g. `Rumoca/Fn/LieGroups/SE23/Quat.lean`. Identical source should give
  identical text, with a drift check like the one dynacert does for `Rumoca/Prelude.lean`.
  - Why: dynacert can then prove each library lemma once and reuse it in every model that calls
    the function. Examples: `to_DCM q ∈ SO(3)` for unit `q`, `product` is the group product,
    `log_map` equals gnc_lean's principal log on its domain (with an error bound for the
    small-angle branches). Per-model copies would need the lemmas re-proved for each model.
- **Keep call sites as calls in `Model.lean`.** Do not inline.
  - Why: the trusted file stays auditable line by line against the `.mo`. Inlining `log_map ∘
    product ∘ inverse` gives one unreadable expression.
  - Why: structure discovery (L2) can recognize the controller's log error from the call
    `log_map(product(inverse(Xr), X))` instead of reverse-engineering expanded algebra.
- **Types and statements:**
  - vector and matrix inputs and outputs as `Fin n → ℝ` and `Matrix (Fin m) (Fin n) ℝ`;
  - locals and `constant`s (e.g. `eps`) as `let`;
  - nested calls (`log_map` calls `normalize` and `left_jacobian_inv`; `rotate` calls `to_DCM`);
  - element-wise assignment to an output array building the whole vector;
  - the `for` loop unrolled, or written as a `Finset` sum or fold.
- **sympy-dae:** emit Python functions that build sympy expressions, with `Piecewise` for
  conditionals. sympy is untrusted, so evaluating calls inline is fine. Keep the function name
  visible (e.g. an applied `sympy.Function` with an implementation) so structure discovery can
  match on it.

```bash
$R compile function.mo -m function_call --target $T/lean_dae -o /tmp/out   # unsupported-feature:lean-dae-functions
```

### 4. Array slices `x[a:b]` (`unsupported-feature:{lean,sympy}-dae-subscript:slice`)

**Why.** Slicing is how a model takes the components out of an SE₂(3) element
`X = {p, v, q}`. `QuadrotorFullStack` uses:
- `X[7:10]` and `Xr[7:10]`: the quaternion, passed to `to_DCM` and `log_map`;
- `Xr[4:6]`: velocity;
- `delta[7:9]`: rate command;
- slice equations such as `a_tgt[1:2] = a_ff[1:2] + …`.

Writing these out element by element makes the trusted file harder to check against the source.

**Fix.** A Prelude helper, or `fun i : Fin k => x ⟨i + a - 1, _⟩`, plus slice targets on the
left-hand side of an equation.

```bash
$R compile slice.mo -m slice --target $T/lean_dae -o /tmp/out   # unsupported-feature:lean-dae-subscript:slice
```

### 5. `fill` (`unsupported-feature:{lean,sympy}-dae-builtin:fill`)

**Why.** It is used in `motor_dev = motors.fm - fill(m*g/4, 4)`, the hover-thrust offset in the
motor-margin output. It's standard Modelica and trivial to support (`fun _ => c`).

```bash
$R compile fill.mo -m fill --target $T/lean_dae -o /tmp/out   # unsupported-feature:lean-dae-builtin:fill
```

### 6. Element-wise power on arrays `.^` (`unsupported-feature:{lean,sympy}-dae-array-power`)

**Why.** It is used in `att_err = sqrt(sum(log_map(…).^2))`. Supporting it is `fun i => v i ^ n`.
The workaround is `v*v`, so this is low priority.

```bash
$R compile array_power.mo -m array_power --target $T/lean_dae -o /tmp/out   # unsupported-feature:lean-dae-array-power
```

## P2 and later

### 7. A single-file library passed as `--source-root` doesn't resolve from another library

Setup: `A.mo` is a single-file package given as `--source-root`, and another source-root library
`Bfile.mo` calls `A.f`. The call is unresolved. It works when `A` is given as a directory root or
comes from `MODELICAPATH`, and when the top-level model calls `A.f` directly.

**Why.** dynacert should eventually pass library roots explicitly, so they can be recorded with
the certificate, rather than relying on the environment. Today it uses `MODELICAPATH`
(`MODELICAPATH=…/modelica_models`), so nothing is blocked.

```bash
$R compile source-root/top.mo -m top --emit flat-mo \
  --source-root source-root/libA/A.mo --source-root source-root/libB/Bfile.mo | grep -c unresolved   # 2
MODELICAPATH=$PWD/source-root/libA $R compile source-root/top.mo -m top --emit flat-mo \
  --source-root source-root/libB/Bfile.mo | grep -c unresolved                                          # 0
```

### 8. Clocks and events in `lean-dae` (`unsupported-feature:lean-dae-events`)

Not needed for the current claim. It becomes needed when:
- the controller is certified as sampled-data (ArduCopter's rate loop runs at about 400 Hz);
- an estimator with resets is added (`when`, `pre`).

The `if time > 5` gust in `Maneuver` only matters for simulation, not certification.

## Already supported (no change needed)

Each was tested on both targets:
- one-level `redeclare` (a two-controller toy was certified end to end with `lmi`);
- implicit derivative equations such as `J*der(w) = …`;
- `cross`, matrix–vector products, `cat`, 1-D `sum`, dot products, `min`/`max`, `atan`, `atan2`;
- `for` loops in equations;
- `if` expressions in equations;
- start values bound to array parameters (`start = x0, each fixed = true`);
- `__Dynacert` annotations on array inputs and on variables inside sub-components. The
  reference-state envelope on `ref.w` therefore needs new dynacert vocabulary only.
