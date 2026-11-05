# Approaches

An approach is one way of analyzing an annotated Modelica model. Each one belongs to a layer of
[architecture.md](architecture.md) §1, and the layer decides the CLI verb that runs it:

```
dynacert MODEL.mo                                  # assess every approach, grouped by layer: yes/no and why
dynacert MODEL.mo certify [METHOD ...]             # L3: named methods, or the portfolio (cheapest first)
dynacert MODEL.mo validate [--sample] [--search]   # L4: montecarlo, falsify (default: both, sampling first)
dynacert MODEL.mo view tube|plots|report           # L5
dynacert MODEL.mo APPROACH [options]               # run any one approach directly
```

Each approach is one file under [python/dynacert/approaches/](../python/dynacert/approaches/).

| Approach | Kind | Layer | File |
|---|---|---|---|
| `structure` | analysis | analyze | [structure.py](../python/dynacert/approaches/structure.py) |
| `lmi` | certificate | certify (cost 10) | [lmi.py](../python/dynacert/approaches/lmi.py) |
| `layered` | certificate | certify | [structure.py](../python/dynacert/approaches/structure.py) |
| `sector` | certificate | certify (cost 40) | [sector.py](../python/dynacert/approaches/sector.py), see [sector.md](sector.md) |
| `compose` | certificate | certify (cost 45) | [sector.py](../python/dynacert/approaches/sector.py): cut selection, Proposition 2, ADMM |
| `tearing` | analysis | analyze | [sector.py](../python/dynacert/approaches/sector.py): loop-tearing cycle gain (§IV baseline) |
| `switched` | certificate | certify (cost 15) | [switched.py](../python/dynacert/approaches/switched.py), see [switching.md](switching.md) |
| `montecarlo` | validation | validate (`--sample`) | [monte_carlo.py](../python/dynacert/approaches/monte_carlo.py) |
| `falsify` | validation | validate (`--search`) | [falsify.py](../python/dynacert/approaches/falsify.py) |
| `tube` | validation | view (`view tube`) | [tube.py](../python/dynacert/approaches/tube.py) |

## Kinds

- **certificate:** the result is a theorem checked by the Lean kernel. It needs a soundness
  theorem proved once in `Dynacert/` and emitted Lean that the kernel checks per model
  (roadmap §3). Python only searches.
- **validation:** the result is evidence from simulation, optimization or search. It is
  untrusted, and is reported as evidence, never as a certificate (roadmap D7).
- **analysis:** the result describes the model (structure discovery); it decides routing and
  is untrusted.

## Layers and plugin attributes

| Attribute | Meaning |
|---|---|
| `layer` | `"analyze"`, `"certify"`, `"validate"` or `"view"`. Left empty, it follows `kind`: certificate → certify, validation → validate, analysis → analyze (set by `@register`) |
| `classes` | model classes a certify method accepts: `"lti"`, `"lpv"`, `"layered"`, `"lie-se23"`, `"nonlinear"` (informational; `assess` decides) |
| `claims` | claim shapes proved or used: `"peak"`, `"tube"`, ... |
| `cost` | portfolio order for `certify` without names: lower runs first (default 100; `lmi` is 10) |
| `cert_file`, `sidecar` | the Lean file and JSON sidecar a certify method writes under `certs/Certs/<Model>/`. Without `cert_file`, the file is derived from the theorem (`M.LayeredCert.certified` → `LayeredCert.lean`) |

After a certify method succeeds, `certify` (and the direct form) records it in
`certs/Certs/<Model>/certificates.json`: `{method, theorem, file, sidecar, bounds, axioms,
source_hash, time}` from `Outcome.data` (`theorem`, `bounds`, `axioms`; axioms fall back to the
sidecar), plus `kept`, the tightest bound per output among the entries of the current source.
It also stamps `source_hash` into the sidecar. A certify method should therefore return
`data={"theorem": ..., "bounds": {output: "p/q"}, "axioms": [...]}` and write `Spec.lean` with
`emit_lti.emit_spec`, so that a changed claim invalidates the other methods' files (they are
found by their `import Certs.<Model>.Spec` line). The bookkeeping lives in
[certindex.py](../python/dynacert/certindex.py).

`view plots` and `view report` draw the `lmi` certificate figure and the figures of a `tube`
run; other L5 plugins with `layer = "view"` run as `view NAME`.

## What a run gets

`dynacert MODEL.mo` compiles the model once with rumoca and builds a
[`Problem`](../python/dynacert/problem.py). Every approach receives it:

| Field | Contents |
|---|---|
| `prob.model` | rumoca's sympy export: variables by role, equations in Lean's order, `der` symbols |
| `prob.spec` | the `__Dynacert` annotations: certified outputs, disturbances, uncertain parameters, references |
| `prob.scalar` | `(model, spec)` with array variables as scalar components (`scalarize.view`); the same objects as `prob.model`, `prob.spec` for a model without arrays |
| `prob.lean_src` | rumoca's Lean transcription (`Model.lean`) |
| `prob.mo`, `prob.model_name` | the source file and model |
| `prob.certificate()` | the `lmi` certificate in `certs/Certs/<Model>/` if it was built from this exact source (its `source_hash`, or for old sidecars the text of `source.mo`), else `None` |
| `prob.source_hash`, `prob.is_current(sidecar)` | sha256 of the source text and model name; whether a sidecar was built from it |
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
    layer = "validate"                 # dynacert MODEL.mo validate mine (default: from kind)
    claims = ("peak",)

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

Every module in the package is imported automatically
([approaches/__init__.py](../python/dynacert/approaches/__init__.py)): `lmi`, `monte_carlo`,
`falsify`, `tube` first, then the rest alphabetically; that is the order the CLI lists
approaches in. A module that fails to import is reported on stderr and skipped, so a broken
plugin does not take down the CLI.

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
- **Array variables are scalarized.** `prob.model` and `prob.spec` keep rumoca's arrays
  (`Real p[3]` is one variable with a `Matrix` of symbols). The linear methods and the
  simulation approaches work on `prob.scalar` = `scalarize.view(prob.model, prob.spec)`: one
  scalar variable per element (`p[1]`, Lean term `p 0`), one scalar equation per component
  with the Lean term that extracts it from rumoca's conjunct (`congrFun eq0 1`, `eq1 2`,
  `eq3 2 (by norm_num) (by norm_num)` for `∀ i : ℕ, 2 ≤ i → i ≤ 3 → …` loops), and the
  annotations of array variables per component (README, "Array variables"). The emitted link
  evaluates each component with `simp only [scalarize.SIMPS]` (lemmas in
  `Dynacert/Linear/Scalar.lean`) before `linear_combination`; models without arrays emit
  exactly the same Lean as before. `montecarlo.scalar_target(prob)` gives the scalar view for
  the harness (one Modelica equation `sys.d[1] = …` per component; uncertain array parameters
  are bound to wrapper parameters `th_c_1_`, because rumoca tunes whole arrays only).
  `disturbance(norm = "2")` on an array is rejected by every method (not implemented).
- **Reuse what exists.** `pipeline.linear_problem` derives error coordinates and `A`/`B`;
  `montecarlo.ScenarioSpace` samples admissible scenarios; the rumoca and sympy backends
  simulate them; `stats` handles sample sizes and confidence.
