"""Falsification (untrusted): search for worst-case scenarios.

Strategies (`--method`; `auto` runs every available one in this order, each seeded by the last):

* `adjoint`: gradients of the output peak with respect to the disturbance, from symbolic
  Jacobians of rumoca's sympy export (`dynacert.worstcase`). Bang-bang on the grid, then
  switches moved to the zero crossings of the switching function; exact for linear models.
  For nonlinear models it also restarts from the worst Monte Carlo scenarios (multistart).
* `collocation`: direct collocation with CasADi + IPOPT on rumoca's CasADi export
  (`dynacert.collocation`), uncertain parameters optimized jointly. Local optimum (global on its
  grid for a linear model at fixed parameters, which is then a linear program).
* `ce`: derivative-free cross-entropy search (`montecarlo.falsify`); also searches references.

Every candidate is re-simulated with the chosen backend (rumoca by default), so each reported
value is an achieved peak, a lower bound on the true worst case. With a certificate, a value
above the certified bound is a counterexample to the pipeline.
"""

from __future__ import annotations

import numpy as np

from .. import collocation, montecarlo, worstcase
from . import VALIDATION, Approach, Assessment, register
from .monte_carlo import certificate_note, scenario_inputs, simulation_check


def _linear(prob) -> bool:
    from .lmi import nonlinear_terms

    try:
        return not nonlinear_terms(prob)
    except Exception:  # noqa: BLE001 - unknown structure: treat as nonlinear
        return False


@register
class Falsify(Approach):
    name = "falsify"
    kind = VALIDATION
    summary = ("worst-case search (adjoint + switching times, CasADi collocation, cross-entropy): "
               "lower bounds, counterexamples")

    def add_arguments(self, p):
        p.add_argument("--method", choices=["auto", "adjoint", "collocation", "ce"],
                       default="auto", help="strategy (default auto: every available one, "
                                            "each seeded by the previous)")
        p.add_argument("--output", action="append",
                       help="output to maximize (repeatable; default: every certified output)")
        p.add_argument("--segments", type=int,
                       help="disturbance grid on [0, T] (default 200; 40 for --method ce)")
        p.add_argument("--starts", type=int, metavar="K",
                       help="adjoint restarts from the K worst Monte Carlo runs (default: 5 for "
                            "nonlinear models, else 0)")
        p.add_argument("--polish", type=int, metavar="ITERS",
                       help="cross-entropy iterations after the gradient methods (default: 0 "
                            "when collocation runs, which also optimizes parameters, or for "
                            "linear models without uncertain parameters; else 4)")
        p.add_argument("--iters", type=int, default=20,
                       help="cross-entropy iterations for --method ce (default 20)")
        p.add_argument("--pop", type=int, default=40, help="cross-entropy population (default 40)")
        p.add_argument("--seed-runs", type=int, default=100, metavar="N",
                       help="Monte Carlo runs for multistart and --method ce (default 100)")
        p.add_argument("--T", type=float, default=10.0, help="horizon (default 10)")
        p.add_argument("--dt", type=float, default=0.005, help="adjoint integration step")
        p.add_argument("--backend", default="rumoca", choices=["rumoca", "sympy"],
                       help="simulator for reported values and cross-entropy")
        p.add_argument("--seed", type=int, default=0)

    def assess(self, prob) -> Assessment:
        bad = simulation_check(prob)
        if bad:
            return bad
        note, _ = certificate_note(prob)
        space = montecarlo.ScenarioSpace(prob.spec, 10.0)
        why = worstcase.Adjoint(prob.model, prob.spec, space).applicable()
        col = collocation.available()
        methods = ["adjoint" if why is None else f"adjoint unavailable ({why})",
                   "collocation" if col is None and why is None
                   else f"collocation unavailable ({col or why})",
                   "cross-entropy"]
        return Assessment.yes("searches " + ", ".join(scenario_inputs(prob)),
                              "methods: " + "; ".join(methods), note,
                              adjoint=why is None, collocation=col is None and why is None)

    def run(self, prob, opts, verbose=print):
        note, bounds = certificate_note(prob)
        verbose(note)
        outputs = opts.output or list(prob.spec.certify)
        unknown = set(outputs) - set(prob.spec.certify)
        if unknown:
            raise ValueError(f"not certified outputs: {sorted(unknown)}")
        segs = opts.segments or (40 if opts.method == "ce" else 200)
        dist = montecarlo.Distribution(segments=segs)
        space = montecarlo.ScenarioSpace(prob.spec, opts.T, dist)
        adj = worstcase.Adjoint(prob.model, prob.spec, space, opts.dt)
        use_adj = opts.method in ("auto", "adjoint")
        use_col = opts.method in ("auto", "collocation")
        if (use_adj or use_col) and adj.applicable() is not None:
            verbose(f"gradient methods unavailable ({adj.applicable()}); using cross-entropy")
            use_adj = use_col = False
        if use_col and collocation.available() is not None:
            if opts.method == "collocation":
                raise ValueError(f"collocation unavailable: {collocation.available()}")
            use_col = False
        use_ce = opts.method == "ce" or not (use_adj or use_col)
        linear = _linear(prob)
        polish = opts.polish if opts.polish is not None else (
            0 if use_col or (linear and not prob.spec.uncertain) else 4)
        nstarts = opts.starts if opts.starts is not None else (0 if linear else 5)
        sim = montecarlo.backend(prob, space, opts.backend)
        col = (collocation.Collocation(prob.model, prob.spec, space, prob.source, prob.model_name)
               if use_col else None)
        mc = None
        if (use_ce or (use_adj and nstarts)) and opts.seed_runs:
            verbose(f"Monte Carlo: {opts.seed_runs} runs to seed the search")
            mc = montecarlo.run(prob, opts.seed_runs, T=opts.T, backend_name=opts.backend,
                                seed=opts.seed, dist=dist, bounds=bounds)

        lines, data, ok, everything = [], {}, True, {}
        for o in outputs:
            b = float(bounds[o]) if o in bounds else None
            found = []                                   # (value, method, scenario)

            def add(method, scn):
                v = montecarlo._peaks(sim.run(scn))[o]
                found.append((v, method, scn))
                verbose(f"  {method}: {v:.7g}")

            best_scn = None
            if use_adj:
                verbose(f"adjoint |{o}|")
                starts = []
                if nstarts and mc is not None:
                    idx = np.argsort(mc.peaks[o])[::-1][:nstarts]
                    ok_idx = mc._ok()
                    starts = [mc.scenarios[ok_idx[int(i)]] for i in idx]
                r = adj.search(o, starts=starts, verbose=verbose)
                for stage, _, scn in r.candidates:
                    if stage in ("scan", "switch", "multistart"):
                        add(f"adjoint/{stage}", scn)
                best_scn = r.scenario
            if use_col:
                verbose(f"collocation |{o}|")
                if best_scn is not None:
                    seeds = [best_scn]
                else:                                    # cold start: zero disturbance
                    K = space.dist.segments
                    th = dict(zip([u.name for u in prob.spec.uncertain],
                                  worstcase.nominal_theta(prob.model, prob.spec)))
                    refs = {n: np.zeros((space.dist.harmonics, 3)) for n in space.free}
                    seeds = [montecarlo.Scenario(th, {n: np.zeros(K) for n, _ in space.dists},
                                                 refs)]
                for s0 in seeds:
                    run0 = adj.fwd.run(s0)
                    if best_scn is not None:
                        y = run0.outputs[o]
                        i = int(np.argmax(np.abs(y)))
                        cands = [(float(run0.t[i]), float(np.sign(y[i]) or 1.0))]
                    else:
                        cands = [(t, s) for t in np.linspace(opts.T / 4, opts.T, 4)
                                 for s in (1.0, -1.0)]
                    for tstar, sign in cands:
                        c = col.solve(o, tstar, sign, s0, run0)
                        tag = "" if c.status == "solved" else f", {c.status}"
                        add(f"collocation t*={tstar:.4g}{'+' if sign > 0 else '-'}{tag}",
                            c.scenario)
            if use_ce or polish:
                top = max(found, key=lambda t: t[0])[2] if found else None
                iters = opts.iters if use_ce and not found else polish
                verbose(f"cross-entropy |{o}| ({iters} iterations)")
                f = montecarlo.falsify(prob, o, iters=iters, pop=opts.pop, T=opts.T,
                                       seed=opts.seed, backend_name=opts.backend, dist=dist,
                                       init=top if top is not None else mc, bounds=bounds)
                found.append((f.value, "cross-entropy", f.scenario))
            everything[o] = found
            v, how, scn = max(found, key=lambda t: t[0])
            exceeds = b is not None and v > b * (1 + 1e-6)
            ok &= not exceeds
            vs = (f"vs certified {b:.6g} (ratio {v / b:.5f})" if b is not None
                  else "(no certificate)")
            lines.append(f"|{o}|: achieved {v:.7g} {vs}  by {how}"
                         + ("  COUNTEREXAMPLE" if exceeds else ""))
            for val, h, _ in found:
                lines.append(f"    {h:<28} {val:.7g}")
            data[o] = {"achieved": v, "bound": b, "method": how,
                       "candidates": [{"method": h, "achieved": val} for val, h, _ in found],
                       "scenario": scn.to_json()}
        lines.append(f"Values are re-simulated with {opts.backend} over [0, {opts.T:g}]: achieved "
                     "peaks, lower bounds on the worst case, with no probability attached.")
        return self.outcome(ok, "validated" if ok else "counterexample", "\n".join(lines),
                            {"outputs": data, "T": opts.T, "segments": segs},
                            artifacts={"found": everything, "sim": sim, "space": space,
                                       "adjoint": adj if use_adj or use_col else None,
                                       "mc": mc, "bounds": bounds})

    def figures(self, prob, outcome, opts):
        from .. import figures

        a = outcome.artifacts
        cache = {}

        def simulate(scn):
            if id(scn) not in cache:
                cache[id(scn)] = a["sim"].run(scn)
            return cache[id(scn)]

        figs = {}
        for o, found in a["found"].items():
            b = float(a["bounds"][o]) if o in a["bounds"] else None
            figs[f"worstcase-{o}"] = (lambda o=o, found=found, b=b: figures.worstcase(
                found, o, simulate, bound=b, space=a["space"], adjoint=a["adjoint"],
                model=prob.model.name))
        if a["bounds"]:
            def tight():
                rows = {}
                for o, found in a["found"].items():
                    if o not in a["bounds"]:
                        continue
                    mcv = float(a["mc"].peaks[o].max()) if a["mc"] is not None else None
                    rows[o] = {"certified": float(a["bounds"][o]), "montecarlo": mcv,
                               "falsify": max(v for v, _, _ in found)}
                return figures.tightness(rows, model=prob.model.name)
            figs["tightness"] = tight
        return figs
