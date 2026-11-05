"""Command line: assess a Modelica model, then certify, validate and view it.

    dynacert MODEL.mo                              assessment, grouped by layer, with reasons
    dynacert MODEL.mo certify [METHOD ...]         L3: the named methods, or the portfolio
    dynacert MODEL.mo validate [--sample] [--search]   L4: Monte Carlo and/or falsification
    dynacert MODEL.mo view tube|plots|report       L5: tube, or figures of the certificate(s)
    dynacert MODEL.mo APPROACH [options]           run one approach directly (any layer)
    dynacert MODEL.mo VERB|APPROACH -h             options
    dynacert --list                                every registered approach, by layer

`certify` with no method runs every feasible certify method, cheapest first, continuing after
failures, and keeps the tightest bound per output (certs/Certs/<Model>/certificates.json).
`validate` runs --sample (montecarlo) then --search (falsify) by default. `view plots` draws the
lmi certificate figure and the tube figures into <certificate dir>/plots; `view report` puts
them in one PDF (default <certificate dir>/report.pdf).

Common options (after MODEL.mo and the verb or approach): --model NAME (default: the last model
in the file), --root DIR (the dynacert project), --json (print the result as JSON), -q (quiet).

Figures (after a run): --plot [DIR] writes them, --report FILE.pdf collects them in one PDF,
--show opens them; --figures a,b selects some (--figures list shows them), --theme
light|dark|paper, --format png,svg,pdf, --dpi N.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

from . import approaches, certindex, problem, timing
from .approaches import CERTIFY, LAYER_TITLES, LAYERS, VALIDATE, VIEW
from .pipeline import CertError

EXIT_OK, EXIT_FAILED, EXIT_INFEASIBLE, EXIT_USAGE = 0, 1, 2, 64

VERBS = ("certify", "validate", "view")
VALIDATE_FLAGS = {"montecarlo": "--sample", "falsify": "--search"}
VIEW_PRODUCTS = ("plots", "report")


_COMMON_KEYS = {"model", "root", "json", "quiet", "plot", "report", "show", "figures", "theme",
                "format", "dpi"}


def _options(opts) -> dict | None:
    """The approach's own options, for the timing record."""
    if opts is None:
        return None
    return {k: v for k, v in vars(opts).items() if k not in _COMMON_KEYS}


def _common() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(add_help=False)
    p.add_argument("--model", help="model to analyze (default: the last model in the file)")
    p.add_argument("--root", help="dynacert project directory (default: found automatically)")
    p.add_argument("--json", action="store_true", help="print the result as JSON")
    p.add_argument("-q", "--quiet", action="store_true", help="no progress messages")
    g = p.add_argument_group("figures")
    g.add_argument("--plot", nargs="?", const="", metavar="DIR",
                   help="write the run's figures (default DIR: <certificate dir>/plots, else "
                        "./<Model>_plots)")
    g.add_argument("--report", metavar="FILE.pdf", help="all selected figures in one PDF")
    g.add_argument("--show", action="store_true", help="open the figures in a window")
    g.add_argument("--figures", metavar="A,B",
                   help="only these figures (comma-separated; 'list' prints the choices)")
    g.add_argument("--theme", default="light", choices=["light", "dark", "paper"])
    g.add_argument("--format", default="png", metavar="png,svg,pdf",
                   help="file formats for --plot (comma-separated; default png)")
    g.add_argument("--dpi", type=int, default=150)
    return p


def _verb_options(verb: str) -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(add_help=False)
    if verb == "validate":
        g = p.add_argument_group("validate")
        g.add_argument("--sample", action="store_true", help="Monte Carlo sampling (montecarlo)")
        g.add_argument("--search", action="store_true", help="worst-case search (falsify)")
    return p


def _hint(a) -> str:
    """The command that runs approach `a` in the layered CLI."""
    if a.layer == CERTIFY:
        return f"certify {a.name}"
    if a.layer == VALIDATE:
        return "validate " + VALIDATE_FLAGS.get(a.name, a.name)
    if a.layer == VIEW:
        return f"view {a.name}"
    return a.name


def _tags(a) -> str:
    parts = []
    if a.classes:
        parts.append("classes " + ",".join(a.classes))
    if a.claims:
        parts.append("claims " + ",".join(a.claims))
    return "; ".join(parts)


def _list(out=print):
    w = max(len(n) for n in approaches.REGISTRY)
    out("approaches (by layer):")
    for layer in LAYERS:
        group = approaches.by_layer(layer)
        if not group:
            continue
        out(f" {LAYER_TITLES[layer]}")
        for a in sorted(group, key=lambda a: a.cost) if layer == CERTIFY else group:
            out(f"  {a.name:<{w}}  {a.kind:<11}  {a.summary}")
            extra = [x for x in (_tags(a), f"run: {_hint(a)}") if x]
            out(f"  {'':<{w}}  {'':<11}  ({'; '.join(extra)})")


def _usage(out=print):
    out(__doc__.strip())
    out("")
    _list(out)


def _kept_line(prob) -> str | None:
    """'certified: |e| ≤ ... (lmi), ...' from the index, if any current certificate exists."""
    d = prob.cert_dir
    if not d.exists():
        return None
    try:
        idx = certindex.load(d, prob.model.ns)
        best = certindex.kept(idx["certificates"], prob.source_hash)
    except Exception:  # noqa: BLE001 - informational only
        return None
    if not best:
        return None
    return "certified: " + ", ".join(f"|{o}| ≤ {float(Fraction(k['bound'])):.6g} ({k['method']})"
                                     for o, k in best.items())


def _assess(prob, mo: str, as_json: bool) -> int:
    res = approaches.assess_all(prob)
    if as_json:
        print(json.dumps({n: {"feasible": a.feasible, "kind": approaches.get(n).kind,
                              "layer": approaches.get(n).layer, "notes": a.notes,
                              "details": a.details}
                          for n, a in res.items()}, indent=1, default=str))
        return EXIT_OK
    print(prob.describe())
    kl = _kept_line(prob)
    if kl:
        print("  " + kl)
    w = max(len(n) for n in res)
    for layer in LAYERS:
        group = [a for a in approaches.by_layer(layer) if a.name in res]
        if layer == CERTIFY:
            group.sort(key=lambda a: a.cost)
        if not group:
            continue
        print(f"\n{LAYER_TITLES[layer]}")
        for ap in group:
            a = res[ap.name]
            mark = "yes" if a.feasible else "no "
            notes = a.notes or [""]
            print(f"  {ap.name:<{w}}  {mark}  {notes[0]}")
            for n in notes[1:]:
                print(f"  {'':<{w}}       {n}")
    nxt = []
    cert_ok = [a.name for a in sorted(approaches.by_layer(CERTIFY), key=lambda a: a.cost)
               if res.get(a.name) and res[a.name].feasible]
    if cert_ok:
        nxt.append((f"dynacert {mo} certify", "portfolio: " + ", ".join(cert_ok)))
    val_ok = [a.name for a in approaches.by_layer(VALIDATE) if res.get(a.name) and
              res[a.name].feasible]
    if val_ok:
        nxt.append((f"dynacert {mo} validate", ", ".join(val_ok)))
    view_ok = [a.name for a in approaches.by_layer(VIEW) if res.get(a.name) and
               res[a.name].feasible]
    for n in view_ok:
        nxt.append((f"dynacert {mo} view {n}", ""))
    if prob.certificate() is not None:
        nxt.append((f"dynacert {mo} view plots", "figures of the current certificate"))
    if nxt:
        wc = max(len(c) for c, _ in nxt)
        print("\nnext:")
        for c, why in nxt:
            print(f"  {c:<{wc}}  {why}".rstrip())
        print(f"  (options: dynacert {mo} VERB -h)")
    return EXIT_OK


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv and argv[0] == "timings":
        return _timings(argv[1:])
    timing.start(["dynacert", *argv])
    code = EXIT_FAILED
    try:
        code = _main(argv)
        return code
    finally:
        timing.finish(code)


def _timings(rest: list) -> int:
    """`dynacert timings [--model M] [--run lmi] [--phases] [--json]`: compare recorded runs."""
    ap = argparse.ArgumentParser(prog="dynacert timings",
                                 description="run times recorded in bench/timings.jsonl")
    ap.add_argument("--model")
    ap.add_argument("--run", help="approach or verb (lmi, montecarlo, certify, assess, ...)")
    ap.add_argument("--phases", action="store_true", help="phase breakdown of each latest run")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args(rest)
    recs = timing.load()
    if a.json:
        print(json.dumps([r for r in recs if (not a.model or r.get("model") == a.model)],
                         indent=1))
    else:
        print(timing.report(recs, a.model, a.run, a.phases))
    return EXIT_OK


def _main(argv: list) -> int:
    if not argv or argv[0] in ("-h", "--help"):
        _usage()
        return EXIT_OK if argv else EXIT_USAGE
    if argv[0] == "--list":
        _list()
        return EXIT_OK
    mo, rest = argv[0], argv[1:]
    if rest and rest[0] in VERBS and rest[0] not in approaches.REGISTRY:
        return _verb(mo, rest[0], rest[1:])
    return _legacy(mo, rest)


# --- the legacy form: dynacert MODEL.mo [APPROACH] [options] -------------------------------------

def _legacy(mo: str, rest: list) -> int:
    name = rest.pop(0) if rest and not rest[0].startswith("-") else None
    common, leftover = _common().parse_known_args(rest)
    if name is not None and name not in approaches.REGISTRY:
        print(f"dynacert: unknown approach {name!r}", file=sys.stderr)
        _list(lambda s: print(s, file=sys.stderr))
        return EXIT_USAGE
    opts = None
    if name is not None:
        ap = argparse.ArgumentParser(prog=f"dynacert {mo} {name}",
                                     description=approaches.get(name).summary,
                                     parents=[_common()])
        approaches.get(name).add_arguments(ap)
        opts = ap.parse_args(rest)            # handles -h for the approach
        timing.context(approach=name, options=_options(opts))
    elif leftover:
        if "-h" in leftover or "--help" in leftover:
            _usage()
            return EXIT_OK
        print(f"dynacert: unexpected arguments {leftover} (give an approach first)",
              file=sys.stderr)
        return EXIT_USAGE
    say = (lambda *a: None) if (common.quiet or common.json) else (
        lambda *a: print(*a, file=sys.stderr))
    try:
        prob = problem.load(mo, common.model, common.root, verbose=say)
        if prob.inferred:
            say(f"model: {prob.model_name} (inferred; use --model to choose)")
        if name is None:
            return _assess(prob, mo, common.json)
        a = approaches.get(name)
        verdict = approaches.assess(name, prob)
        if not verdict.feasible:
            print(f"{name}: not applicable to {prob.model.name}", file=sys.stderr)
            for n in verdict.notes:
                print(f"  {n}", file=sys.stderr)
            return EXIT_INFEASIBLE
        with timing.phase(f"run:{name}"):
            out = a.run(prob, opts, verbose=say)
        timing.context(ok=out.ok, status=out.status)
    except (CertError, ValueError, OSError) as e:
        print(f"dynacert: {e}", file=sys.stderr)
        return EXIT_FAILED
    if out.ok and a.layer == CERTIFY:
        try:                                  # keep the index current; never fails the run
            _record(prob, a, out)
        except Exception as e:  # noqa: BLE001
            say(f"index: not updated ({type(e).__name__}: {e})")
    if not common.json:
        print(out.text)
    try:
        out.files += _figures(a, prob, out, opts, say)
    except ValueError as e:
        print(f"dynacert: {e}", file=sys.stderr)
        return EXIT_USAGE
    if common.json:
        print(json.dumps({"approach": out.approach, "kind": out.kind, "ok": out.ok,
                          "status": out.status, "data": out.data,
                          "files": [str(f) for f in out.files]}, indent=1, default=str))
    return EXIT_OK if out.ok else EXIT_FAILED


# --- the layered form: dynacert MODEL.mo certify|validate|view ... ------------------------------

def _parser(mo, verb, a) -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(prog=f"dynacert {mo} {verb} {a.name}",
                                 description=a.summary,
                                 parents=[_common(), _verb_options(verb)])
    a.add_arguments(ap)
    return ap


def _parse(mo, verb, cands, tokens):
    """Parse `tokens` once per candidate approach (each keeps its own defaults); an option no
    parser knows is a usage error. Returns ({name: opts}, common opts, unknown options)."""
    per, unknown = {}, None
    for a in cands:
        opts, left = _parser(mo, verb, a).parse_known_args(tokens)
        per[a.name] = opts
        bad = {t.split("=")[0] for t in left if t.startswith("-")}
        unknown = bad if unknown is None else unknown & bad
    common, left = argparse.ArgumentParser(parents=[_common(), _verb_options(verb)],
                                           add_help=False).parse_known_args(tokens)
    if unknown is None:
        unknown = {t.split("=")[0] for t in left if t.startswith("-")}
    return per, common, sorted(unknown)


def _verb_help(mo, verb, cands):
    head = {"certify": f"dynacert {mo} certify [METHOD ...] [options]\n\n"
                       "L3: run the named certify methods, or with none the portfolio (every "
                       "feasible certify method, cheapest first); keeps the tightest bound per "
                       "output in certificates.json.",
            "validate": f"dynacert {mo} validate [--sample] [--search] [NAME ...] [options]\n\n"
                        "L4: --sample = montecarlo, --search = falsify (default: every validate "
                        "approach, sampling first). Untrusted evidence, never a certificate.",
            "view": f"dynacert {mo} view tube|plots|report [options]\n\n"
                    "L5: `tube` runs the tube approach; `plots` writes the lmi certificate figure "
                    "and the tube figures (default <certificate dir>/plots); `report` puts them "
                    "in one PDF (default <certificate dir>/report.pdf)."}[verb]
    print(head)
    print("\nmethods: " + ", ".join(a.name for a in cands))
    for a in cands:
        print("\n" + "=" * 8 + f" {a.name} " + "=" * 8)
        print(_parser(mo, verb, a).format_help())
    return EXIT_OK


def _select(verb, names, tokens):
    """The candidate approaches for a verb; raises ValueError on a bad name."""
    layer = {"certify": CERTIFY, "validate": VALIDATE, "view": VIEW}[verb]
    group = approaches.by_layer(layer)
    if verb == "certify":
        group = sorted(group, key=lambda a: a.cost)
    if verb == "view":
        if not names:
            raise ValueError("view needs a product: " + ", ".join(
                [a.name for a in group] + list(VIEW_PRODUCTS)))
        if len(names) > 1:
            raise ValueError(f"view takes one product, got {names}")
        if names[0] in VIEW_PRODUCTS:
            return [a for a in group if a.name == "tube"]
    if verb == "validate":
        flagged = [n for n, f in VALIDATE_FLAGS.items() if f in tokens]
        names = names + [n for n in flagged if n not in names]
        if not names:
            return sorted(group, key=lambda a: a.cost)
    if not names:
        return group
    by = {a.name: a for a in group}
    bad = [n for n in names if n not in by]
    if bad:
        raise ValueError(f"not a {verb} method: {', '.join(bad)} (choose from "
                         f"{', '.join(by) or 'none'})")
    order = [n for n in names]
    if verb == "validate":   # sampling first, then search, then the rest as given
        order.sort(key=lambda n: by[n].cost if n in VALIDATE_FLAGS else 1000)
    return [by[n] for n in order]


def _verb(mo: str, verb: str, rest: list) -> int:
    names = []
    while rest and not rest[0].startswith("-"):
        names.append(rest.pop(0))
    try:
        if verb == "view" and not names and ("-h" in rest or "--help" in rest):
            return _verb_help(mo, verb, approaches.by_layer(VIEW))
        cands = _select(verb, names, rest)
    except ValueError as e:
        print(f"dynacert: {e}", file=sys.stderr)
        return EXIT_USAGE
    if "-h" in rest or "--help" in rest:
        return _verb_help(mo, verb, cands)
    per, common, unknown = _parse(mo, verb, cands, rest)
    timing.context(verb=verb, approach=",".join(names) or None,
                   options={n: _options(o) for n, o in per.items()})
    if unknown:
        print(f"dynacert: unknown options for {verb}: {', '.join(unknown)} "
              f"(see dynacert {mo} {verb} -h)", file=sys.stderr)
        return EXIT_USAGE
    say = (lambda *a: None) if (common.quiet or common.json) else (
        lambda *a: print(*a, file=sys.stderr))
    try:
        prob = problem.load(mo, common.model, common.root, verbose=say)
    except (CertError, ValueError, OSError) as e:
        print(f"dynacert: {e}", file=sys.stderr)
        return EXIT_FAILED
    if prob.inferred:
        say(f"model: {prob.model_name} (inferred; use --model to choose)")
    if verb == "certify":
        return _certify(prob, cands, per, common, named=bool(names), say=say)
    product = names[0] if verb == "view" else None
    return _run_group(prob, verb, cands, per, common, say, product=product)


def _run_one(prob, a, opts, say, results):
    """Assess and run one approach; appends (approach, verdict, outcome|None, error|None)."""
    try:
        with timing.phase(f"assess:{a.name}"):
            v = a.assess(prob)
    except Exception as e:  # noqa: BLE001 - as approaches.assess
        v = approaches.Assessment.no(f"assessment failed: {type(e).__name__}: {e}")
    if not v.feasible:
        say(f"{a.name}: not applicable: " + "; ".join(v.notes))
        results.append((a, v, None, None))
        return None
    say(f"── {a.name} ──")
    try:
        with timing.phase(f"run:{a.name}"):
            out = a.run(prob, opts, verbose=say)
    except Exception as e:  # noqa: BLE001 - one failing method must not stop the others
        msg = str(e) if isinstance(e, (CertError, ValueError, OSError)) else \
            f"{type(e).__name__}: {e}"
        print(f"dynacert: {a.name} failed: {msg}", file=sys.stderr)
        results.append((a, v, None, msg))
        return None
    results.append((a, v, out, None))
    return out


def _record(prob, a, out) -> dict:
    d = prob.cert_dir
    h = prob.source_hash
    e = certindex.entry(a, out, d, h)
    return certindex.record(d, prob.model.ns, e, h)


def _certify(prob, cands, per, common, named, say) -> int:
    d = prob.cert_dir
    spec_file = d / "Spec.lean"
    old_spec = spec_file.read_text() if spec_file.exists() else None
    results, built, checked = [], [], False
    for a in cands:
        out = _run_one(prob, a, per[a.name], say, results)
        if out is None or not out.ok:
            continue
        e = _record(prob, a, out)["certificates"][-1]
        built.append(e.get("file"))
        if not common.json:
            print(out.text)
        if not checked:
            checked = True
            new_spec = spec_file.read_text() if spec_file.exists() else None
            if old_spec is not None and new_spec is not None and new_spec != old_spec:
                loud = lambda s: print(s, file=sys.stderr)  # noqa: E731
                loud(f"!! Spec.lean of {prob.model.ns} changed (the model or its annotations "
                     "changed): removing certificates of the old claim")
                gone = certindex.invalidate(d, prob.model.ns, {f for f in built if f}, say=loud)
                if not gone:
                    loud("!! (no other certificate files imported the old Spec)")
    if checked is False and old_spec is not None and spec_file.exists() \
            and spec_file.read_text() != old_spec:
        print(f"!! Spec.lean of {prob.model.ns} changed but no method built: the other "
              f"certificates in {d} were proved against the old Spec", file=sys.stderr)
    idx = certindex.load(d, prob.model.ns) if d.exists() else {"certificates": []}
    best = certindex.kept(idx["certificates"], prob.source_hash)
    ok = any(o is not None and o.ok for _, _, o, _ in results)
    if common.json:
        print(json.dumps({"verb": "certify", "ok": ok, "results": [
            {"method": a.name, "feasible": v.feasible, "notes": v.notes,
             "ok": bool(o and o.ok), "status": o.status if o else ("failed" if err else
                                                                   "infeasible"),
             "error": err, "data": o.data if o else None} for a, v, o, err in results],
            "kept": best, "index": str(d / certindex.INDEX)}, indent=1, default=str))
    else:
        _certify_table(prob, results, idx, best)
    runs = [(a, o) for a, _, o, _ in results if o is not None]
    try:
        _figures_multi(runs, per[cands[0].name] if cands else common, prob, say)
    except ValueError as e:
        print(f"dynacert: {e}", file=sys.stderr)
        return EXIT_USAGE
    if ok:
        return EXIT_OK
    return EXIT_INFEASIBLE if all(o is None and err is None for _, _, o, err in results) \
        else EXIT_FAILED


def _certify_table(prob, results, idx, best):
    current = prob.source_hash
    entries = {e["method"]: e for e in idx["certificates"] if e.get("source_hash") == current}
    try:
        certify = list(prob.scalar[1].certify)   # array outputs: one column per component
    except ValueError:
        certify = list(prob.spec.certify)
    outputs = certify or sorted({o for e in entries.values() for o in e["bounds"]})
    rows = []
    for a, v, o, err in results:
        if o is not None and o.ok and a.name in entries:
            continue
        why = (err or "; ".join(v.notes) or "") if o is None else o.status
        rows.append((a.name, None, "failed: " + why if err else
                     ("not applicable: " + why if o is None else why)))
    ran = {a.name for a, _, o, _ in results if o is not None and o.ok}
    table = [(m, e, "" if m in ran else "(earlier run)") for m, e in entries.items()]
    print(f"\ncertify {prob.model.name}: method × output bound   (* = kept, tightest)")
    w = max([len(m) for m, _, _ in table + rows] + [6])
    cw = max([len(o) for o in outputs] + [12])
    print(f"  {'method':<{w}}  " + "  ".join(f"{'|' + o + '|':>{cw}}" for o in outputs))
    for m, e, note in table:
        cells = []
        for o in outputs:
            b = e["bounds"].get(o)
            if b is None:
                cells.append(f"{'—':>{cw}}")
                continue
            star = "*" if best.get(o, {}).get("method") == m else " "
            cells.append(f"{float(Fraction(b)):>{cw - 1}.6g}{star}")
        print(f"  {m:<{w}}  " + "  ".join(cells) + (f"  {note}" if note else ""))
    for m, _, why in rows:
        print(f"  {m:<{w}}  {why}")
    if best:
        print("  kept: " + ", ".join(f"|{o}| ≤ {k['bound']} ({k['method']})"
                                     for o, k in best.items()))
        print(f"  index: {prob.cert_dir / certindex.INDEX}")
    else:
        print("  no certificate built")


def _run_group(prob, verb, cands, per, common, say, product=None) -> int:
    results = []
    for a in cands:
        out = _run_one(prob, a, per[a.name], say, results)
        if out is not None and not common.json:
            print(out.text)
            print()
    opts = per[cands[0].name] if cands else common
    runs = [(a, o) for a, _, o, _ in results if o is not None]
    if product in VIEW_PRODUCTS:
        lmi = approaches.REGISTRY.get("lmi")
        if prob.certificate() is None and not runs:
            print(f"dynacert: no current certificate for {prob.model.name}: run "
                  f"`dynacert {prob.mo.name} certify` first", file=sys.stderr)
            return EXIT_INFEASIBLE
        if lmi is not None and prob.certificate() is not None:
            runs.insert(0, (lmi, lmi.outcome(True, "certified", "")))
        if product == "plots" and opts.plot is None and not opts.report and not opts.show \
                and not opts.figures:
            opts.plot = ""
        if product == "report" and not opts.report and opts.figures != "list":
            opts.report = str(prob.cert_dir / "report.pdf")
    if common.json:
        print(json.dumps({"verb": verb, "results": [
            {"approach": a.name, "feasible": v.feasible, "notes": v.notes,
             "ok": bool(o and o.ok), "status": o.status if o else ("failed" if err else
                                                                   "infeasible"),
             "error": err, "data": o.data if o else None} for a, v, o, err in results]},
            indent=1, default=str))
    try:
        _figures_multi(runs, opts, prob, say)
    except ValueError as e:
        print(f"dynacert: {e}", file=sys.stderr)
        return EXIT_USAGE
    ran = [o for _, _, o, _ in results if o is not None]
    errors = [err for *_, err in results if err is not None]
    if product in VIEW_PRODUCTS:      # figures of whatever exists (tube may not apply)
        return EXIT_OK if runs and not errors and all(o.ok for o in ran) else EXIT_FAILED
    if not ran:
        return EXIT_FAILED if errors else EXIT_INFEASIBLE
    return EXIT_OK if not errors and all(o.ok for o in ran) else EXIT_FAILED


# --- figures ------------------------------------------------------------------------------------

def _figures(approach, prob, out, opts, say) -> list:
    """Build, write and show the figures the options ask for; returns the files written."""
    return _figures_multi([(approach, out)], opts, prob, say)


def _figures_multi(runs, opts, prob, say) -> list:
    """Figures of several runs [(approach, outcome)]; names are `figure` (or `approach:figure`
    when two runs draw the same name); files are prefixed with the approach name."""
    wanted = opts.plot is not None or opts.report or opts.show or opts.figures
    if not wanted or not runs:
        return []
    import matplotlib

    if not opts.show:
        matplotlib.use("Agg")
    from . import figures

    per = [(a, a.figures(prob, out, opts)) for a, out in runs]
    counts = {}
    for _, mk in per:
        for n in mk:
            counts[n] = counts.get(n, 0) + 1
    makers, owner = {}, {}
    for a, mk in per:
        for n, f in mk.items():
            key = n if counts[n] == 1 else f"{a.name}:{n}"
            makers[key], owner[key] = f, (a, n)
    label = runs[0][0].name if len(runs) == 1 else "this run"
    if opts.figures == "list":
        if len(per) == 1:
            print(f"figures for {label}: " + (", ".join(makers) or "none"))
        else:
            for a, mk in per:
                print(f"figures for {a.name}: " + (", ".join(
                    k for k, (oa, _) in owner.items() if oa is a) or "none"))
        return []
    names = list(makers)
    if opts.figures:
        names = [n.strip() for n in opts.figures.split(",") if n.strip()]
        unknown = [n for n in names if n not in makers]
        if unknown:
            raise ValueError(f"unknown figures {unknown}; {label} draws: "
                             f"{', '.join(makers) or 'none'}")
    if not names:
        say(f"{label}: no figures for this run")
        return []
    figs = {}
    with figures.theme(opts.theme):
        for n in names:
            say(f"figure: {n}")
            try:
                with timing.phase(f"figure:{n}"):
                    figs[n] = makers[n]()
            except Exception as e:  # noqa: BLE001 - one failing figure must not lose the rest
                print(f"dynacert: figure {n} failed: {type(e).__name__}: {e}", file=sys.stderr)
    files = []
    if opts.plot is not None:
        d = Path(opts.plot) if opts.plot else (
            prob.cert_dir / "plots" if prob.certificate() is not None
            else Path.cwd() / f"{prob.name}_plots")
        fmts = [f.strip() for f in opts.format.split(",") if f.strip()]
        # a directory given by the user may be shared by several models: name files by model
        model = f"{prob.model.ns}-" if opts.plot else ""
        for a, _ in per:
            mine = {owner[n][1]: f for n, f in figs.items() if owner[n][0] is a}
            if mine:
                files += figures.save(mine, d, fmts, opts.dpi, prefix=f"{model}{a.name}-")
    if opts.report:
        files.append(figures.report(figs, opts.report))
    for f in files:
        print(f"  wrote {f}")
    if opts.show:
        import matplotlib.pyplot as plt

        plt.show()
    figures.close(figs)
    return files


if __name__ == "__main__":
    sys.exit(main())
