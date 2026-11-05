"""The approach interface: what every analysis of a Modelica model provides.

An approach has two steps:

* `assess(prob)`: can it run on this model, and if so what does it expect? Cheap and
  side-effect free: structural checks, and a fast numeric search where one exists (the LMI
  approach solves its LMI here, so "feasible" means a candidate certificate was found).
* `run(prob, opts)`: do it and return an `Outcome`. Certificate approaches end with the Lean
  kernel's check; validation approaches (simulation, search) are untrusted and say so.

To add an approach, subclass `Approach` in a new module under `dynacert/approaches/` and decorate
it with `@register`; every module in the package is imported automatically.

Each approach belongs to one layer of docs/architecture.md, which decides the CLI verb it runs
under:

* `layer`: "analyze" (L2, shown by `dynacert MODEL.mo`), "certify" (L3, `certify`), "validate"
  (L4, `validate`) or "view" (L5, `view`). Left empty, it follows `kind`: certificate → certify,
  validation → validate, anything else → analyze.
* `classes`: model classes a certify method accepts ("lti", "lpv", "layered", "lie-se23",
  "nonlinear"); informational, empty = unrestricted / decided by `assess`.
* `claims`: claim shapes it proves or uses ("peak", "tube", ...).
* `cost`: portfolio order under `certify` with no method named (lower runs first).
* `cert_file` / `sidecar`: the Lean file and JSON sidecar a certify method writes under
  `certs/Certs/<Model>/` (empty: derived from the theorem name / not known).
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field

CERTIFICATE = "certificate"   # result is a theorem checked by the Lean kernel
VALIDATION = "validation"     # result is evidence from simulation or search (untrusted)
ANALYSIS = "analysis"         # result is a description of the model (untrusted, decides routing)

# layers (docs/architecture.md §1): L2 analyze, L3 certify, L4 validate, L5 view
ANALYZE, CERTIFY, VALIDATE, VIEW = "analyze", "certify", "validate", "view"
LAYERS = (ANALYZE, CERTIFY, VALIDATE, VIEW)
LAYER_TITLES = {ANALYZE: "L2 analyze (structure)", CERTIFY: "L3 certify (Lean-checked methods)",
                VALIDATE: "L4 validate (evidence, untrusted)", VIEW: "L5 view (products)"}
KIND_LAYER = {CERTIFICATE: CERTIFY, VALIDATION: VALIDATE, ANALYSIS: ANALYZE}


@dataclass
class Assessment:
    feasible: bool
    notes: list[str] = field(default_factory=list)   # why not, or what to expect
    details: dict = field(default_factory=dict)      # machine-readable extras

    @staticmethod
    def no(*why: str, **details) -> "Assessment":
        return Assessment(False, list(why), details)

    @staticmethod
    def yes(*notes: str, **details) -> "Assessment":
        return Assessment(True, list(notes), details)


@dataclass
class Outcome:
    approach: str
    kind: str
    ok: bool                 # certified / no counterexample
    status: str              # short word: certified, failed, validated, counterexample, ...
    text: str                # human-readable report
    data: dict = field(default_factory=dict)          # JSON-serializable result
    files: list = field(default_factory=list)         # files written
    artifacts: dict = field(default_factory=dict, repr=False)  # live objects for `figures`


class Approach:
    name: str = ""
    kind: str = VALIDATION
    summary: str = ""
    layer: str = ""                  # "" = from `kind` (set by `register`)
    classes: tuple = ()              # model classes accepted (certify methods)
    claims: tuple = ()               # claim shapes proved / used
    cost: int = 100                  # portfolio order (lower first)
    cert_file: str = ""              # Lean file written under certs/Certs/<Model>/
    sidecar: str = ""                # JSON sidecar written next to it

    def add_arguments(self, parser: argparse.ArgumentParser) -> None:
        """Approach-specific command-line options."""

    def assess(self, prob) -> Assessment:
        raise NotImplementedError

    def run(self, prob, opts: argparse.Namespace, verbose=print) -> Outcome:
        raise NotImplementedError

    def figures(self, prob, outcome: Outcome, opts: argparse.Namespace) -> dict:
        """Figures this run can draw: name -> zero-argument function returning a matplotlib
        Figure (built only when selected). See `dynacert.figures`."""
        return {}

    def outcome(self, ok: bool, status: str, text: str, data=None, files=None,
                artifacts=None) -> Outcome:
        return Outcome(self.name, self.kind, ok, status, text, data or {}, files or [],
                       artifacts or {})
