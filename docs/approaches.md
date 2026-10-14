# Approaches

An approach is one way of analyzing an annotated Modelica model. The CLI lists the
registered approaches, says which ones apply to a model, and runs the one you choose:

```
dynacert MODEL.mo                     # assess every approach: yes/no and why
dynacert MODEL.mo APPROACH [options]  # run one
```

Each approach is one file under [python/dynacert/approaches/](../python/dynacert/approaches/).

| Approach | Kind | File |
|---|---|---|
| `lmi` | certificate | [lmi.py](../python/dynacert/approaches/lmi.py) |
| `montecarlo` | validation | [monte_carlo.py](../python/dynacert/approaches/monte_carlo.py) |
| `falsify` | validation | [falsify.py](../python/dynacert/approaches/falsify.py) |

## Kinds

- **certificate:** the result is a theorem checked by the Lean kernel. It needs a soundness
  theorem proved once in `Dynacert/` and emitted Lean that the kernel checks per model
  (roadmap §3). Python only searches.
- **validation:** the result is evidence from simulation, optimization or search. It is
  untrusted, and is reported as evidence, never as a certificate (roadmap D7).

## What a run gets

`dynacert MODEL.mo` compiles the model once with rumoca and builds a
[`Problem`](../python/dynacert/problem.py). Every approach receives it:

| Field | Contents |
|---|---|
| `prob.model` | rumoca's sympy export: variables by role, equations in Lean's order, `der` symbols |
| `prob.spec` | the `__Dynacert` annotations: certified outputs, disturbances, uncertain parameters, references |
| `prob.lean_src` | rumoca's Lean transcription (`Model.lean`) |
| `prob.mo`, `prob.model_name` | the source file and model |
| `prob.certificate()` | the certificate in `certs/Certs/<Model>/` if it was built from this exact source, else `None` |
| `prob.cache` | a dict for approaches to share work (`lmi` keeps its search result there between assess and run) |

## Writing one

```python
# python/dynacert/approaches/my_approach.py
from . import VALIDATION, Approach, Assessment, register


@register
class MyApproach(Approach):
    name = "mine"                      # the CLI word: dynacert MODEL.mo mine
    kind = VALIDATION                  # or CERTIFICATE
    summary = "one line for `dynacert --list`"

    def add_arguments(self, p):        # argparse options after the approach name
        p.add_argument("--horizon", type=float, default=10.0)

    def assess(self, prob) -> Assessment:
        # Cheap and side-effect free. Say exactly why the approach does not apply; if it does,
        # say what to expect.
        if not prob.spec.certify:
            return Assessment.no("no __Dynacert(certify) outputs")
        return Assessment.yes("applies because ...", "expect ...")

    def run(self, prob, opts, verbose=print):
        ...                            # progress through `verbose`
        return self.outcome(ok=True, status="validated", text="report for the terminal",
                            data={"json": "serializable"}, files=[])
```

Figures are optional. Override `figures(prob, outcome, opts)` to return
`{name: zero-argument function -> matplotlib Figure}`; the CLI builds only the ones selected
with `--figures`, under the chosen `--theme`, and writes them with `--plot` or `--report`.
`run` can pass live objects (a Monte Carlo run, simulators, candidate scenarios) to it through
`self.outcome(..., artifacts={...})`; they are never serialized. Reuse `dynacert.figures` for a
consistent look (`palette()` gives the theme's colors).

Then add the module to the import line at the bottom of
[approaches/__init__.py](../python/dynacert/approaches/__init__.py). The import order is the
order the CLI lists approaches in.

Conventions:

- **`assess` decides feasibility.** It checks structure first (linearity, input shapes,
  annotations). If the numeric part is fast, it runs that too, so that "yes" means a
  candidate was found. `lmi` solves its LMI during assessment and reports the predicted
  bounds.
- **`run` assumes `assess` said yes.** The CLI calls `assess` first and exits with status 2
  and the reasons if it said no. If `assess` raises, the approach is reported as infeasible
  instead of crashing the listing.
- **`Outcome.ok` is false for failures and counterexamples.** It sets the exit status (1).
  Use `status` for the one-word verdict, `text` for people and `data` for `--json`.
- **Reuse what exists.** `pipeline.linear_problem` derives error coordinates and `A`/`B`;
  `montecarlo.ScenarioSpace` samples admissible scenarios; the rumoca and sympy backends
  simulate them; `stats` handles sample sizes and confidence.

## Example: an MPC approach

Which kind an MPC approach is depends on what it claims:

- **Validation.** Close the loop with an MPC controller (for example cvxpy over a
  linearization from `pipeline.linear_problem`, or a nonlinear solver over the sympy
  model). Simulate it against admissible scenarios and report constraint satisfaction and
  peaks. This fits the interface above now.
- **Certificate.** Prove that an MPC law keeps the certified outputs bounded, for example
  through a terminal set and cost: an invariant ellipsoid and an LMI decrease condition,
  checked like the `lmi` certificate. This needs a Lean soundness theorem first, then an
  emitter, as `lmi` has.
