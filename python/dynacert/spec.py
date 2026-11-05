"""The specification of a certification run, read from `__Dynacert` annotations.

The specification fixes the theorem statement. It is built from the model and its
annotations only, never from a method's output, so a wrong method choice or bad numbers can
only make the proof fail to build.

Annotation vocabulary (component level):

    input Real d    annotation(__Dynacert(disturbance(bound = 1.0)));
    Real e          annotation(__Dynacert(certify));
    parameter Real c = 0.2 annotation(__Dynacert(uncertain(min = 0.1, max = 0.3)));
    input Real x_ref annotation(__Dynacert(reference(derivative = "v_ref")));
    Real x(start = 0, fixed = true) annotation(__Dynacert(initialSet(min = -0.2, max = 0.2)));

`initialSet(min, max)` on a state replaces its start value by the interval `[min, max]` in the
claim (`Spec.InitialSet`). (`initial` itself is a Modelica keyword and cannot name an
annotation modifier; the spelling `initial` is accepted where a parser lets it through.)

Array variables (`input Real d[3]`, `Real e[3]`, `parameter Real K[2, 3]`) are annotated as a
whole and read per component (`scalarize`, used by the linear methods and the Monte Carlo
harness): `disturbance(bound = b)` is `|d[i]| ≤ b` for every `i` (as if each component were
declared as a scalar input); `disturbance(bound = b, norm = "2")` is the Euclidean ball
`‖d‖ ≤ b` instead; `certify` certifies every component (outputs `e[1]`, `e[2]`, ...);
`uncertain(min, max)`, `reference(...)` and `initialSet(min, max)` apply to each component.
A number may also be given per component as an array, e.g. `bound = {0.1, 0.2, 0.1}`.

Model level:

    annotation(__Dynacert(method = "lti", horizon = 10));
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction

VENDOR = "__Dynacert"


def _ann(attrs: dict | None) -> dict:
    if not attrs:
        return {}
    for k, v in attrs.items():
        if k.lower() == VENDOR.lower():
            return v if isinstance(v, dict) else {}
    return {}


def _numv(x):
    """A number, or a list of numbers (one per component of an array variable)."""
    if isinstance(x, (list, tuple)):
        return [_numv(v) for v in x]
    return _num(x)


def _pairs(lo, hi):
    """Componentwise (lo, hi) pairs of numbers or per-component lists (scalars broadcast)."""
    los, his = ([x] if not isinstance(x, list) else x for x in (lo, hi))
    n = max(len(los), len(his))
    return zip(los * n if len(los) == 1 else los, his * n if len(his) == 1 else his)


def _num(x) -> Fraction:
    if isinstance(x, bool):
        raise ValueError("expected a number")
    if isinstance(x, (int, Fraction)):
        return Fraction(x)
    if isinstance(x, float):
        return Fraction(repr(x))  # exact decimal reading, like Lean's OfScientific
    return Fraction(str(x))


@dataclass
class Disturbance:
    name: str
    bound: Fraction  # componentwise peak bound |d(t)| ≤ bound
    norm: str | None = None   # "2": `‖d(t)‖ ≤ bound` for an array input (Euclidean ball)
    group: str | None = None  # per-component entry of this array input (set by `scalarize`)


@dataclass
class Uncertain:
    name: str
    lo: Fraction
    hi: Fraction


@dataclass
class Reference:
    name: str
    derivative: str | None  # name of the input that is its derivative
    start: Fraction | None = None  # value at t = 0


@dataclass
class InitialBox:
    name: str
    lo: Fraction
    hi: Fraction


@dataclass
class Spec:
    disturbances: list[Disturbance] = field(default_factory=list)
    certify: list[str] = field(default_factory=list)
    uncertain: list[Uncertain] = field(default_factory=list)
    references: list[Reference] = field(default_factory=list)
    method: str | None = None
    horizon: Fraction | None = None
    initial: list[InitialBox] = field(default_factory=list)  # states started in a box

    @property
    def disturbance_names(self) -> list[str]:
        return [d.name for d in self.disturbances]


def from_model(model) -> Spec:
    """Collect the `__Dynacert` annotations of a loaded model (see `model.Model`)."""
    spec = Spec()
    for v in model.variables:
        a = _ann(v.annotations)
        if not a:
            continue
        if v.role != "input":
            # `disturbance` / `reference` describe a component's free input; once an enclosing
            # model binds it (e.g. a wrapper fixing the reference) it is no longer an input of
            # the claim, so the annotation does not apply
            a = {k: val for k, val in a.items() if k not in ("disturbance", "reference")}
        if "disturbance" in a:
            d = a["disturbance"]
            if not isinstance(d, dict) or "bound" not in d:
                raise ValueError(f"{v.name}: disturbance(bound = ...) is required")
            norm = d.get("norm")
            norm = None if norm is None else str(norm).strip().strip('"')
            if norm not in (None, "2", "inf"):
                raise ValueError(f'{v.name}: disturbance norm must be "2" (Euclidean ball) or '
                                 f'"inf" (per component, the default), not {norm!r}')
            spec.disturbances.append(Disturbance(v.name, _numv(d["bound"]),
                                                 "2" if norm == "2" else None))
        if "certify" in a:
            spec.certify.append(v.name)
        if "uncertain" in a:
            u = a["uncertain"]
            spec.uncertain.append(Uncertain(v.name, _numv(u["min"]), _numv(u["max"])))
        ini = a.get("initialSet", a.get("initial"))
        if ini is not None:
            if not isinstance(ini, dict) or "min" not in ini or "max" not in ini:
                raise ValueError(f"{v.name}: initialSet(min = ..., max = ...) is required")
            if v.role != "state":
                raise ValueError(f"{v.name}: initialSet applies to states only")
            lo, hi = _numv(ini["min"]), _numv(ini["max"])
            if any(l_ > h_ for l_, h_ in _pairs(lo, hi)):
                raise ValueError(f"{v.name}: initialSet min > max")
            spec.initial.append(InitialBox(v.name, lo, hi))
        if "reference" in a:
            r = a["reference"]
            der = r.get("derivative") if isinstance(r, dict) else None
            st = r.get("start") if isinstance(r, dict) else None
            spec.references.append(Reference(v.name, der, None if st is None else _numv(st)))
    m = _ann(model.annotations)
    spec.method = m.get("method")
    if "horizon" in m:
        spec.horizon = _num(m["horizon"])
    return spec
