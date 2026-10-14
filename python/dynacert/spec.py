"""The specification of a certification run, read from `__Dynacert` annotations.

The specification fixes the theorem statement. It is built from the model and its
annotations only, never from a method's output, so a wrong method choice or bad numbers can
only make the proof fail to build.

Annotation vocabulary (component level):

    input Real d    annotation(__Dynacert(disturbance(bound = 1.0)));
    Real e          annotation(__Dynacert(certify));
    parameter Real c = 0.2 annotation(__Dynacert(uncertain(min = 0.1, max = 0.3)));
    input Real x_ref annotation(__Dynacert(reference(derivative = "v_ref")));

Model level:

    annotation(__Dynacert(method = "lti", initial(...)));
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
class Spec:
    disturbances: list[Disturbance] = field(default_factory=list)
    certify: list[str] = field(default_factory=list)
    uncertain: list[Uncertain] = field(default_factory=list)
    references: list[Reference] = field(default_factory=list)
    method: str | None = None
    horizon: Fraction | None = None

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
        if "disturbance" in a:
            d = a["disturbance"]
            if not isinstance(d, dict) or "bound" not in d:
                raise ValueError(f"{v.name}: disturbance(bound = ...) is required")
            spec.disturbances.append(Disturbance(v.name, _num(d["bound"])))
        if "certify" in a:
            spec.certify.append(v.name)
        if "uncertain" in a:
            u = a["uncertain"]
            spec.uncertain.append(Uncertain(v.name, _num(u["min"]), _num(u["max"])))
        if "reference" in a:
            r = a["reference"]
            der = r.get("derivative") if isinstance(r, dict) else None
            st = r.get("start") if isinstance(r, dict) else None
            spec.references.append(Reference(v.name, der, None if st is None else _num(st)))
    m = _ann(model.annotations)
    spec.method = m.get("method")
    if "horizon" in m:
        spec.horizon = _num(m["horizon"])
    return spec
