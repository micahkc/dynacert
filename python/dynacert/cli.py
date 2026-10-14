"""Command line: assess a Modelica model, then run an approach on it.

    dynacert MODEL.mo                       which approaches apply to the model, and why (not)
    dynacert MODEL.mo APPROACH [options]    run one approach
    dynacert MODEL.mo APPROACH -h           that approach's options
    dynacert --list                         every registered approach

Common options (before or after APPROACH): --model NAME (default: the last model in the file),
--root DIR (the dynacert project), --json (print the result as JSON), -q (quiet progress).

Figures (after a run): --plot [DIR] writes them, --report FILE.pdf collects them in one PDF,
--show opens them; --figures a,b selects some (--figures list shows them), --theme
light|dark|paper, --format png,svg,pdf, --dpi N.
"""

from __future__ import annotations

import argparse
import json
import sys

from . import approaches, problem
from .pipeline import CertError

EXIT_OK, EXIT_FAILED, EXIT_INFEASIBLE, EXIT_USAGE = 0, 1, 2, 64


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


def _list(out=print):
    w = max(len(n) for n in approaches.REGISTRY)
    out("approaches:")
    for name, a in approaches.REGISTRY.items():
        out(f"  {name:<{w}}  {a.kind:<11}  {a.summary}")


def _usage(out=print):
    out(__doc__.strip())
    out("")
    _list(out)


def _assess(prob, mo: str, as_json: bool) -> int:
    res = approaches.assess_all(prob)
    if as_json:
        print(json.dumps({n: {"feasible": a.feasible, "kind": approaches.get(n).kind,
                              "notes": a.notes, "details": a.details}
                          for n, a in res.items()}, indent=1, default=str))
        return EXIT_OK
    print(prob.describe())
    print()
    w = max(len(n) for n in res)
    for name, a in res.items():
        kind = approaches.get(name).kind
        mark = "yes" if a.feasible else "no "
        notes = a.notes or [""]
        print(f"  {name:<{w}}  {kind:<11}  {mark}  {notes[0]}")
        for n in notes[1:]:
            print(f"  {'':<{w}}  {'':<11}       {n}")
    ok = [n for n, a in res.items() if a.feasible]
    if ok:
        print(f"\nrun one:  dynacert {mo} {ok[0]}    (options: dynacert {mo} {ok[0]} -h)")
    return EXIT_OK


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv or argv[0] in ("-h", "--help"):
        _usage()
        return EXIT_OK if argv else EXIT_USAGE
    if argv[0] == "--list":
        _list()
        return EXIT_OK
    mo, rest = argv[0], argv[1:]
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
        out = a.run(prob, opts, verbose=say)
    except (CertError, ValueError, OSError) as e:
        print(f"dynacert: {e}", file=sys.stderr)
        return EXIT_FAILED
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


def _figures(approach, prob, out, opts, say) -> list:
    """Build, write and show the figures the options ask for; returns the files written."""
    wanted = opts.plot is not None or opts.report or opts.show or opts.figures
    if not wanted:
        return []
    import matplotlib

    if not opts.show:
        matplotlib.use("Agg")
    from . import figures

    makers = approach.figures(prob, out, opts)
    if opts.figures == "list":
        print(f"figures for {approach.name}: " + (", ".join(makers) or "none"))
        return []
    names = list(makers)
    if opts.figures:
        names = [n.strip() for n in opts.figures.split(",") if n.strip()]
        unknown = [n for n in names if n not in makers]
        if unknown:
            raise ValueError(f"unknown figures {unknown}; {approach.name} draws: "
                             f"{', '.join(makers) or 'none'}")
    if not names:
        say(f"{approach.name}: no figures for this run")
        return []
    figs = {}
    with figures.theme(opts.theme):
        for n in names:
            say(f"figure: {n}")
            try:
                figs[n] = makers[n]()
            except Exception as e:  # noqa: BLE001 - one failing figure must not lose the rest
                print(f"dynacert: figure {n} failed: {type(e).__name__}: {e}", file=sys.stderr)
    files = []
    if opts.plot is not None:
        from pathlib import Path

        d = Path(opts.plot) if opts.plot else (
            prob.cert_dir / "plots" if prob.certificate() is not None
            else Path.cwd() / f"{prob.name}_plots")
        fmts = [f.strip() for f in opts.format.split(",") if f.strip()]
        files += figures.save(figs, d, fmts, opts.dpi, prefix=f"{approach.name}-")
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
