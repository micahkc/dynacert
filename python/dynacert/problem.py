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
    lean_src: str
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
    def cert_dir(self) -> Path:
        return self.root / "certs" / "Certs" / self.model.ns

    def certificate(self):
        """The certificate under `certs/Certs/<Model>` if it was built from this exact source,
        else None (missing or stale)."""
        if "certificate" not in self.cache:
            from . import api

            d, cert = self.cert_dir, None
            src = d / "source.mo"
            if (d / "certified.json").exists() and src.exists() \
                    and src.read_text() == self.mo.read_text():
                cert = api.load(self.model.ns, self.root)
            self.cache["certificate"] = cert
        return self.cache["certificate"]

    def describe(self) -> str:
        m, s = self.model, self.spec
        parts = [f"{len(m.states)} states", f"{len(m.inputs)} inputs",
                 f"{len(m.params)} parameters"]
        lines = [f"{m.name} ({self.mo.name}{', inferred' if self.inferred else ''}): "
                 + ", ".join(parts)]
        spec = []
        if s.certify:
            spec.append("certify " + ", ".join(s.certify))
        if s.disturbances:
            spec.append("disturbances " + ", ".join(f"|{d.name}| ≤ {float(d.bound):g}"
                                                     for d in s.disturbances))
        if s.uncertain:
            spec.append("uncertain " + ", ".join(f"{u.name} ∈ [{float(u.lo):g}, {float(u.hi):g}]"
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
    lean_file, py_file = pipeline.export(mo, model, Path(tmp.name), root=root)
    m = model_mod.load(py_file)
    return Problem(mo, model, m, spec_mod.from_model(m), lean_file.read_text(), py_file, root,
                   inferred, _tmp=tmp)
