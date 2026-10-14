"""The approach interface: what every analysis of a Modelica model provides.

An approach has two steps:

* `assess(prob)`: can it run on this model, and if so what does it expect? Cheap and
  side-effect free: structural checks, and a fast numeric search where one exists (the LMI
  approach solves its LMI here, so "feasible" means a candidate certificate was found).
* `run(prob, opts)`: do it and return an `Outcome`. Certificate approaches end with the Lean
  kernel's check; validation approaches (simulation, search) are untrusted and say so.

To add an approach, subclass `Approach` in a new module under `dynacert/approaches/`, decorate it
with `@register`, and import the module in `approaches/__init__.py`.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field

CERTIFICATE = "certificate"   # result is a theorem checked by the Lean kernel
VALIDATION = "validation"     # result is evidence from simulation or search (untrusted)


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
