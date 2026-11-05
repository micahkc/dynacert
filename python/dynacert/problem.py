"""A Modelica model loaded for analysis: one rumoca compilation, shared by every approach.

    prob = problem.load("examples/ClosedLoop.mo")          # model name inferred
    prob.model, prob.spec                                  # sympy view + __Dynacert spec
    prob.lean_src                                          # rumoca's Lean transcription
    prob.certificate()                                     # existing certificate, if current
"""

from __future__ import annotations

import re
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

from . import model as model_mod
from . import pipeline
from . import spec as spec_mod
from .certindex import source_hash  # noqa: F401  (sha256 of source text + model name)


def model_names(mo: Path) -> list[str]:
    """Classes declared with `model` in a Modelica file, in order."""
    src = re.sub(r"//[^\n]*|/\*.*?\*/", "", Path(mo).read_text(), flags=re.S)
    return re.findall(r"(?m)^\s*(?:partial\s+)?model\s+([A-Za-z_]\w*)", src)


def infer_model(mo: Path) -> str:
    """The last model in the file (Modelica files conventionally end with the system that
    composes the earlier ones)."""
    names = model_names(mo)
    if not names:
        raise pipeline.CertError(f"{mo}: no `model` declarations")
    return names[-1]


@dataclass
class Problem:
    mo: Path
    model_name: str
    model: model_mod.Model
    spec: spec_mod.Spec
    lean_src: str | None          # None when rumoca's Lean export failed (see cache['lean_error'])
    py_file: Path
    root: Path
    inferred: bool = False
    cache: dict = field(default_factory=dict, repr=False)   # approaches share search results
    _tmp: object = field(default=None, repr=False)

    # the interface `montecarlo` expects from a simulation target
    @property
    def name(self) -> str:
        return self.model.ns

    @property
    def source(self) -> Path:
        return self.mo

    @property
    def scalar(self):
        """`(model, spec)` with array variables as scalar components (`scalarize.view`): what
        the linear methods and the Monte Carlo harness work on. Unchanged without arrays."""
        if "scalar" not in self.cache:
            from . import scalarize

            self.cache["scalar"] = scalarize.view(self.model, self.spec)
        return self.cache["scalar"]

    @property
    def cert_dir(self) -> Path:
        return self.root / "certs" / "Certs" / self.model.ns

    def certificate(self):
        """The certificate under `certs/Certs/<Model>` if it was built from this exact source,
        else None (missing or stale)."""
        if "certificate" not in self.cache:
            from . import api

            d, cert = self.cert_dir, None
            if (d / "certified.json").exists() and self.is_current(d / "certified.json"):
                cert = api.load(self.model.ns, self.root)
            self.cache["certificate"] = cert
        return self.cache["certificate"]

    @property
    def source_hash(self) -> str:
        """sha256 of this model's source text and name (recorded in every sidecar)."""
        return source_hash(self.mo.read_text(), self.model.name)

    def is_current(self, sidecar: Path) -> bool:
        """Was the sidecar's certificate built from this exact source and model? Uses its
        `source_hash`; sidecars written before the hash existed fall back to comparing
        `source.mo` with the source text."""
        import json

        try:
            side = json.loads(Path(sidecar).read_text())
        except (OSError, ValueError):
            return False
        if side.get("source_hash"):
            return side["source_hash"] == self.source_hash
        src = Path(sidecar).parent / "source.mo"
        return src.exists() and src.read_text() == self.mo.read_text()

    def describe(self) -> str:
        m, s = self.model, self.spec
        parts = [f"{len(m.states)} states", f"{len(m.inputs)} inputs",
                 f"{len(m.params)} parameters"]
        lines = [f"{m.name} ({self.mo.name}{', inferred' if self.inferred else ''}): "
                 + ", ".join(parts)]
        spec = []
        if s.certify:
            spec.append("certify " + ", ".join(s.certify))
        arr = {v.name for v in m.variables if not v.scalar}

        def num(x):
            return "{" + ", ".join(f"{float(v):g}" for v in x) + "}" if isinstance(x, list) \
                else f"{float(x):g}"

        def dist(d):
            if d.name not in arr:
                return f"|{d.name}| ≤ {num(d.bound)}"
            if d.norm == "2":
                return f"‖{d.name}‖₂ ≤ {num(d.bound)}"
            return f"|{d.name}[i]| ≤ {num(d.bound)}"

        if s.disturbances:
            spec.append("disturbances " + ", ".join(dist(d) for d in s.disturbances))
        if s.uncertain:
            spec.append("uncertain " + ", ".join(
                f"{u.name}{'[i]' * (u.name in arr)} ∈ [{num(u.lo)}, {num(u.hi)}]"
                for u in s.uncertain))
        if s.references:
            spec.append("references " + ", ".join(r.name for r in s.references))
        lines.append("  spec: " + ("; ".join(spec) if spec else "no __Dynacert annotations"))
        return "\n".join(lines)


def load(mo: str | Path, model: str | None = None, root: str | Path | None = None,
         verbose=None) -> Problem:
    """Compile `mo` with rumoca (lean-dae and sympy-dae targets) and read its specification."""
    from .api import find_root

    mo = Path(mo).resolve()
    if not mo.exists():
        raise pipeline.CertError(f"{mo}: no such file")
    inferred = model is None
    model = model or infer_model(mo)
    root = Path(root).resolve() if root else find_root(mo)
    tmp = tempfile.TemporaryDirectory(prefix="dynacert-")
    if verbose:
        verbose(f"rumoca: compiling {model} from {mo.name}")
    from . import timing

    try:
        with timing.phase("rumoca export"):
            prob = _load(mo, model, root, tmp, inferred, verbose)
        try:
            rel = str(mo.relative_to(root))
        except ValueError:
            rel = str(mo)
        timing.context(model=prob.model.name, source=rel, size=timing.model_size(prob),
                       root=str(root))
        return prob
    except pipeline.CertError as e:
        if "unsupported-feature:events" in str(e):
            raise pipeline.CertError(
                f"{mo.name}: {model} uses events (if/when/sample conditions). rumoca's lean_dae "
                "and sympy_dae targets do not support events yet, so dynacert cannot analyze "
                "it; for validation, write switching with min/max or smooth functions") from None
        raise


def _load(mo, model, root, tmp, inferred, verbose) -> Problem:
    lean_error = None
    try:
        lean_file, py_file = pipeline.export(mo, model, Path(tmp.name), root=root, verbose=verbose or (lambda _: None))
        lean_src = lean_file.read_text()
    except pipeline.CertError as e:
        if "lean_dae" not in str(e):
            raise
        # The Lean transcription is needed only to certify. Simulation-based approaches still
        # run on the sympy export (e.g. models with events, which lean-dae does not support).
        lean_error = " ".join(str(e).split())[:300]
        out = Path(tmp.name) / "py"
        pipeline.run_rumoca(mo, model, pipeline.DEFAULT_TARGETS / "sympy_dae", out)
        py_file, lean_src = next(out.glob("*.py")), None
        if verbose:
            verbose(f"rumoca: no Lean export ({lean_error}); certification is unavailable")
    m = model_mod.load(py_file)
    prob = Problem(mo, model, m, spec_mod.from_model(m), lean_src, py_file, root, inferred,
                   _tmp=tmp)
    prob.cache["lean_error"] = lean_error
    return prob
