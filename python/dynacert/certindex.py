"""Certificate bookkeeping under `certs/Certs/<Model>/` (docs/architecture.md §8 A1, A2).

* `source_hash(text, model)`: sha256 of the Modelica source and the model name. Every sidecar
  records it, so "is this certificate about this model?" is a hash comparison.
* `certificates.json` (the index): every method that built, with its theorem, Lean file,
  bounds, axioms, source hash and time, plus `kept`: per output the tightest bound among the
  current (same source hash) certificates and the method that proved it. `certified.json`
  stays the lmi sidecar.
* `invalidate(...)`: after `Spec.lean` changed (the model or its annotations changed), delete
  every other generated certificate file that imports the old `Spec`, with its sidecar and its
  index entry. `Model.lean`, `Spec.lean` and `source.mo` are never deleted.
"""

from __future__ import annotations

import hashlib
import json
import re
import time
from fractions import Fraction
from pathlib import Path

INDEX = "certificates.json"
PROTECTED = frozenset({"Model.lean", "Spec.lean", "source.mo"})
# generated certificate file -> (method, sidecar, extra generated files)
KNOWN = {"Cert.lean": ("lmi", "certified.json", ("certificate.png",)),
         "LayeredCert.lean": ("layered", "layered.json", ())}


def source_hash(text: str, model: str) -> str:
    """sha256 of the Modelica source text and the model name."""
    return hashlib.sha256((text + "\0" + model).encode()).hexdigest()


def _read_json(p: Path):
    try:
        return json.loads(p.read_text())
    except (OSError, ValueError):
        return None


def _bounds(side: dict) -> dict:
    if isinstance(side.get("bounds"), dict):
        return {k: str(v) for k, v in side["bounds"].items()}
    return {o["name"]: str(o["bound"]) for o in side.get("outputs", []) if "bound" in o}


def _bootstrap(d: Path, model: str) -> list[dict]:
    """Index entries for sidecars written before the index existed."""
    out = []
    for f, (method, sc, _) in KNOWN.items():
        side = _read_json(d / sc)
        if not side or not (d / f).exists():
            continue
        h = side.get("source_hash")
        if h is None and method == "lmi" and (d / "source.mo").exists():
            h = source_hash((d / "source.mo").read_text(), side.get("model", model))
        out.append({"method": method, "theorem": side.get("theorem"), "file": f,
                    "bounds": _bounds(side), "axioms": side.get("axioms", []),
                    "source_hash": h, "time": None})
    return out


def load(d: Path, model: str = "") -> dict:
    """The index of `d` (built from existing sidecars when there is none yet)."""
    d = Path(d)
    idx = _read_json(d / INDEX)
    if not isinstance(idx, dict) or "certificates" not in idx:
        idx = {"model": model or d.name, "certificates": _bootstrap(d, model or d.name)}
    return idx


def kept(entries: list[dict], current: str | None) -> dict:
    """Per output: the tightest bound among entries with source hash `current` (all entries
    when `current` is None)."""
    best: dict = {}
    for e in entries:
        if current is not None and e.get("source_hash") != current:
            continue
        for o, b in (e.get("bounds") or {}).items():
            try:
                v = Fraction(b)
            except (ValueError, TypeError, ZeroDivisionError):
                continue
            if o not in best or v < Fraction(best[o]["bound"]):
                best[o] = {"bound": str(b), "method": e["method"]}
    return best


def save(d: Path, idx: dict, current: str | None) -> Path:
    idx["source_hash"] = current
    idx["kept"] = kept(idx["certificates"], current)
    p = Path(d) / INDEX
    p.write_text(json.dumps(idx, indent=1))
    return p


def entry(approach, outcome, d: Path, h: str) -> dict:
    """An index entry for a successful run of a certify method; stamps `source_hash` into the
    method's sidecar when the sidecar lacks it."""
    data = outcome.data or {}
    theorem = data.get("theorem")
    f = getattr(approach, "cert_file", "") or (
        theorem.split(".")[-2] + ".lean" if theorem and theorem.count(".") >= 2 else None)
    sc = getattr(approach, "sidecar", "") or (KNOWN.get(f, (None, None))[1] if f else None)
    side = _read_json(d / sc) if sc else None
    if isinstance(side, dict) and side.get("source_hash") != h:
        side["source_hash"] = h
        (d / sc).write_text(json.dumps(side, indent=1))
    axioms = data.get("axioms") or (side or {}).get("axioms") or []
    bounds = {k: str(v) for k, v in (data.get("bounds") or {}).items()} or _bounds(side or {})
    return {"method": approach.name, "theorem": theorem, "file": f, "sidecar": sc,
            "bounds": bounds, "axioms": list(axioms), "source_hash": h,
            "time": time.strftime("%Y-%m-%dT%H:%M:%S")}


def record(d: Path, model: str, e: dict, current: str) -> dict:
    """Replace the entry of `e["method"]` in the index of `d`; returns the saved index."""
    idx = load(d, model)
    idx["certificates"] = [x for x in idx["certificates"] if x["method"] != e["method"]] + [e]
    save(d, idx, current)
    return idx


def imports_spec(f: Path, ns: str) -> bool:
    return re.search(rf"(?m)^\s*import\s+Certs\.{re.escape(ns)}\.Spec\s*$",
                     f.read_text()) is not None


def invalidate(d: Path, ns: str, keep: set, say=print) -> list[Path]:
    """`Spec.lean` changed: delete every generated `.lean` in `d` that imports the old Spec
    (except `keep` and the protected files), its sidecar and generated extras, and its index
    entries. Returns the removed paths."""
    d = Path(d)
    idx = load(d, ns)
    by_file = {e.get("file"): e for e in idx["certificates"]}
    removed = []
    for f in sorted(d.glob("*.lean")):
        if f.name in PROTECTED or f.name in keep or not imports_spec(f, ns):
            continue
        method, sc, extra = KNOWN.get(f.name, (None, None, ()))
        e = by_file.get(f.name)
        sc = sc or (e or {}).get("sidecar")
        for g in [f] + [d / x for x in (sc, *extra) if x]:
            if g.exists() and g.name not in PROTECTED:
                g.unlink()
                removed.append(g)
    gone = {p.name for p in removed}
    idx["certificates"] = [e for e in idx["certificates"] if e.get("file") not in gone]
    if (d / INDEX).exists() or removed:
        save(d, idx, idx.get("source_hash"))
    for p in removed:
        say(f"!! removed stale {p}  (it was built against the old Spec.lean)")
    return removed
