# Monte Carlo validation

A certificate is a worst-case statement. For **every** admissible scenario, each certified
output stays within its bound. Monte Carlo simulation cannot prove that, and dynacert never
reports it as a certificate (roadmap D7). Simulation answers three other questions:

1. **Agreement.** Does an independent simulation of the model ever exceed the proved bound? If
   it does, something in the trusted base disagrees with the simulator: rumoca's
   transcription, the specification, or the simulator itself.
2. **Tightness.** How far is the certified bound from what the system actually reaches?
3. **Risk.** Above what level are a scenario's peaks rare, and how rare are they?

The probability theory is proved once in Lean ([Dynacert/Prob/Scenario.lean](../Dynacert/Prob/Scenario.lean))
under the same axiom policy as the certificates (`propext`, `Classical.choice`, `Quot.sound`).

## Setting

| Symbol | Meaning |
|---|---|
| `Ω` | admissible scenarios: uncertain parameters in their boxes, disturbance signals with `\|d(t)\| ≤ bound`, reference signals that satisfy their declared derivatives |
| `μ` | a probability distribution on `Ω`, chosen by us and recorded in every report (`montecarlo.Distribution`) |
| `g(ω)` | performance of a scenario: `sup_{t ∈ [0,T]} \|y(t)\|` for a certified output `y` |
| `b` | the certified bound. The Lean theorem gives `g(ω) ≤ b` for **all** `ω ∈ Ω` |
| `ω₁ … ω_N` | i.i.d. samples from `μ`, i.e. one draw from `μ^N = Measure.pi (fun _ : Fin N => μ)` |
| `L = maxᵢ g(ωᵢ)` | the achieved peak |

`L` is achieved by an actual admissible scenario, so `L ≤ sup g ≤ b` holds deterministically,
up to simulation error. The gap `b / L` bounds the conservatism of the certificate from above.

## Theorems (Lean, `Dynacert.Prob`)

**`scenario_bound`** (order statistics; the scenario approach of Calafiore and Campi, and
Tempo, Calafiore and Dabbene). For measurable `g` and any `ε`,

```
μ^N { ω | μ {x | ∀ i, g(ωᵢ) < g(x)} > ε }  ≤  (1 − ε)^N
```

With confidence `1 − β`, where `β = (1 − ε)^N`, the scenarios that exceed the achieved peak `L`
have probability at most `ε`: `L` is a `(1 − ε)`-quantile bound. There is no assumption that
`g` has a continuous law. This matters because bang-bang disturbances and endpoint parameters
put atoms in the distribution of `g`. The proof uses the tail `F(t) = μ{g > t}`, the quantile
`q = inf{t | F(t) ≤ ε}` and right-continuity of `F`. It shows `μ{x | F(g x) > ε} ≤ 1 − ε` and
closes with `Measure.pi_pi`.

**`zero_failure_bound`.** If `μ(Sᶜ) ≥ ε`, then `μ^N {all ωᵢ ∈ S} ≤ (1 − ε)^N`. With
`S = {g ≤ b}`: a run in which no sample exceeds the certified bound shows, with confidence
`1 − β`, that scenarios on which the simulator contradicts the theorem have probability `< ε`.

**`one_sub_pow_le_exp`.** `(1 − ε)^N ≤ exp(−εN)`, so `N ≥ ln(1/β)/ε` samples are enough. For
example, `ε = 1%` and `β = 10⁻⁶` need `N = 1375`. `stats.samples_for` computes the exact minimum
and checks it in rational arithmetic.

The Python side also offers results that are standard but not proved in Lean, and labels
them that way: Wilks' bound for discarding the `k` largest samples
(`stats.wilks_confidence_failure`), Clopper–Pearson intervals for an exceedance probability
at a chosen level, and the DKW band around the whole empirical distribution (used in the plot).

### What the probabilities do and do not cover

- They are about `μ`. A different sampling distribution gives different numbers. The worst
  case is not covered by any `μ`; only the certificate covers it.
- They assume each `g(ωᵢ)` is computed exactly. Solver error, sampling the output on a time
  grid, and the pseudo-random generator are outside the theorems.
- The `N` samples must be i.i.d. from `μ`. The falsifier's samples are not, so it reports an
  achieved value and no probability.

## The sampling distribution `μ`

`montecarlo.Distribution` (defaults in brackets):

- **Disturbances.** Piecewise constant on `segments` [40] equal intervals of `[0, T]`. Each
  value is held for a random number of segments from `holds` [1, 2, 4, 8]. With probability
  `p_bang` [0.5] the signal is bang-bang (`±bound`); otherwise its levels are uniform in
  `[−bound, bound]`. Worst cases of linear systems are bang-bang, so `μ` puts substantial mass
  there.
- **Uncertain parameters.** With probability `p_vertex` [0.5] the parameter sits at a random
  endpoint; otherwise it is uniform on its interval.
- **References.** A free reference (one with no declared derivative) is a sum of `harmonics`
  [3] sinusoids with random amplitude, frequency and phase. References with a declared
  derivative are integrated from their `start` values, so the claim's `References` and
  `ReferenceStart` hypotheses hold.

Piecewise-constant inputs are continuous on each segment and admissible under `IsSolutionOn`,
so every sample is a scenario the Lean claim covers.

## Simulating with rumoca

The rumoca Python binding does not take time-varying `inputs=` yet. dynacert therefore
generates a small Modelica **harness** around the certified model:

```modelica
model DynacertMC_ClosedLoop
  ClosedLoop sys;
  parameter Real dw_d_1 = 0; ...            // disturbance levels, one per segment
  parameter Real dr_a_ref_a1 = 0, ...;      // reference harmonics
  Real ref_x_ref(start = 0.0, fixed = true);
equation
  sys.d = 1.0 * (if time < 0.25 then dw_d_1 elseif ... else dw_d_40);
  sys.a_ref = dr_a_ref_a1 * sin(6.28... * dr_a_ref_f1 * time + dr_a_ref_p1) + ...;
  der(ref_x_ref) = sys.v_ref;  sys.x_ref = ref_x_ref;  ...
end DynacertMC_ClosedLoop;
```

It compiles once. Each scenario is then one `simulate(params=...)` call, about 20 ms for the
examples. Uncertain parameters are overridden directly as `sys.<name>`. The harness uses the
certificate's own Modelica source (`certs/Certs/<Model>/source.mo`, which the `lmi` approach now
stores).

Two backends simulate the same `Scenario`:

| Backend | Path | Use |
|---|---|---|
| `rumoca` (default) | rumoca's native solver on the harness | independent of the Lean export |
| `sympy` | fixed-step RK4 on rumoca's sympy export, the DAE IR behind `Model.lean` | no binding needed |

`crosscheck` runs both backends on the same scenarios. On the three examples their peaks agree
to within `4·10⁻⁶` of the bound. A large difference would point at a transcription problem
between rumoca's simulation pipeline and the export the theorem is about.

If rumoca's default (BDF) solver rejects a run, the **same** scenario is solved again with
`rk-like`, and the report counts these fallbacks. Skipping failed runs would condition `μ` on
solver success. Runs that fail in both solvers are listed in the report, which then says its
statements are conditional.

## Falsification (worst-case search)

`dynacert MODEL.mo falsify` maximizes each output's peak over admissible scenarios. Three
strategies are available. `--method auto` (the default) runs every one that applies, each
seeded by the previous one. Every candidate is re-simulated with rumoca's native solver and
reported with its value, so the result is an achieved peak: a lower bound on `sup g`, with no
probability attached.

### Adjoint (Pontryagin) — [worstcase.py](../python/dynacert/worstcase.py)

Linearizing along a trajectory gives the gradient of `±y(t*)` with respect to the
disturbance in one backward pass:

```
δy(t*) = ∫₀^{t*} σ(s)ᵀ δw(s) ds,   σ = B_wᵀ λ,   λ̇ = −Aᵀλ,   λ(t*) = ∇ₓ g
```

Here `A = ∂f/∂x` and `B_w = ∂f/∂w` are symbolic derivatives of rumoca's sympy export, the DAE
the Lean specification is about. The first-order optimum is bang-bang, `w = δ·sign σ`. The
search runs in stages:

1. **scan:** for 10 candidate peak times `t*`, both signs, and every uncertain-parameter
   corner, set each grid segment to the sign of `∫σ` over it. For a linear model this is the
   exact worst case on the grid.
2. **refine:** repeat along the best trajectory, with `t*` moved to its peak, until it stops
   improving. This handles nonlinear models.
3. **switching times:** move the switches to the zero crossings of `σ`, interpolated on the
   integration grid. This removes the grid restriction and reaches the continuous-time
   optimum. The scenario stores the switch times (`Scenario.edges`). The rumoca harness turns
   them into movable event times, and the sympy integrator splits its steps at them.
4. **multistart** (nonlinear models, `--starts`, default 5): stages 2–3 from the worst
   Monte Carlo runs.

The backward pass uses Heun's method. With first-order Euler, the zero crossings, and with
them the switch times, are off by O(dt).

### Direct collocation (CasADi + IPOPT) — [collocation.py](../python/dynacert/collocation.py)

This maximizes `±y(t*)` over interval-wise disturbance levels and the uncertain parameters
jointly. It uses Radau collocation (degree 3) of rumoca's `casadi-ode` export, the `rhs`
function rumoca builds from its solve IR, which is a different path from the sympy export.
The output `y = g(x, u)` comes from the sympy export, because the CasADi export has states
only. In `auto` it is warm-started at the adjoint's peak time.
- **Optimum:** IPOPT gives a local optimum. For a linear model at fixed parameters the problem
  is a linear program, so the optimum is global on its interval grid.
- **What it adds:** it is the only strategy that optimizes uncertain parameters continuously,
  so it can find interior parameter worst cases that corner enumeration misses. The same
  formulation extends to state constraints and other objectives.
- **On its own** (`--method collocation`): it cold-starts at 4 peak times and both signs.

### Cross-entropy — `montecarlo.falsify`

This search is derivative-free and needs no Jacobians. Disturbance signs are Bernoulli
variables refit to the elite frequencies; parameters and reference coefficients are clipped
Gaussians. `--method ce` runs it alone, seeded from Monte Carlo. In `auto` it polishes
(`--polish`) only when collocation did not run and the model is nonlinear or has uncertain
parameters.

### Results

Values are rumoca re-simulations, on `[0, 10]` with a 200-segment grid. "Exact" is
`∫₀¹⁰ |C e^{As} B| ds` at the worst parameter corner.

| Model, output | adjoint, grid | adjoint, switching times | collocation | exact | certified |
|---|---|---|---|---|---|
| `ClosedLoop`, `\|e\|` | 0.749956 | **0.7499978** | 0.749843 | 0.7499987 | 0.843764 |
| `ClosedLoop`, `\|ev\|` | 1.274291 | **1.274918** | 1.274514 | 1.274920 | 1.43073 |
| `ClosedLoopUncertain`, `\|e\|` | 0.824835 | **0.825019** | 0.824811 (c → 0.1) | 0.82502 | 0.933564 |
| `ClosedLoopUncertain`, `\|ev\|` | 1.407943 | **1.408316** | 1.407885 | 1.40833 | 1.58954 |
| `PendulumPD`, `\|e\|` (nonlinear) | 0.0439318 | **0.0439354** | 0.0439353 (cold) | — | — |

Notes on the table:
- **Linear models:** the switching-time stage is within `2·10⁻⁶` of exact.
- **Collocation** lags slightly because its switches are tied to its intervals. It does
  recover the worst parameter corner (`c → 0.1`) on its own.
- **Pendulum:** cross-entropy reaches 0.0439325 in about 400 simulations.
- **Run times:** `dynacert examples/ClosedLoop.mo falsify` takes about 30 s for both outputs.

## Usage

```python
import dynacert
cert = dynacert.load("ClosedLoopUncertain")
mc = cert.montecarlo(eps=0.01, beta=1e-6)   # N = 1375 i.i.d. scenarios via rumoca
mc                     # report: agreement, achieved vs certified, ε at confidence 1 − β
mc.table(); mc.plot()  # per-output table; empirical exceedance curves
mc.violations()        # indices of samples above a certified bound (should be empty)
cert.crosscheck(20)    # rumoca native vs sympy export, same scenarios
cert.falsify("e", init=mc)             # cross-entropy from the Python API
```

```
$ dynacert examples/ClosedLoopUncertain.mo montecarlo --eps 1/50 --crosscheck 10 --save
$ dynacert examples/ClosedLoopUncertain.mo falsify
```

`--save` writes `montecarlo.json` (marked untrusted, with the worst scenario per output for
replay) and `montecarlo.png` next to the certificate (or into a directory given to `--save`).
The exit status is 1 if any sample exceeds a certified bound.

Both approaches also run on models with no certificate, including nonlinear ones such as
`examples/PendulumPD.mo`. They then report achieved peaks and the `scenario_bound` statement
only.

## Possible extensions

- **Lean:** Wilks' `k`-discard bound (a binomial tail; the same quantile argument). A
  certified-plus-statistical statement for a specification that is *not* certified (a chance
  constraint `P(g > s) ≤ ε`), stated about `μ` and an exact evaluator of `g`.
- **Importance sampling** toward the adjoint worst-case direction, to estimate small
  exceedance probabilities near `b`.
- **rumoca:** time-varying `inputs=` in the Python binding would remove the generated harness.
