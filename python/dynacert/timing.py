"""Run-time records: how long each model takes in each phase, kept for comparison.

Every `dynacert` command opens a session; code marks phases with

    with timing.phase("lake build"):
        ...

Phases nest (`run:lmi/lake build`). At exit the session is appended as one JSON line to
`<project>/bench/timings.jsonl` with the model's size, the command, the git commit and the
machine, so runs can be compared across models and over time (`dynacert timings`).
Set DYNACERT_TIMINGS=0 to disable, or to a path to write elsewhere.
"""

from __future__ import annotations

import contextlib
import json
import os
import platform
import socket
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

_session: dict | None = None
_stack: list[str] = []


def start(command: list[str]) -> None:
    global _session
    _session = {"started": time.perf_counter(), "command": " ".join(command), "phases": [],
                "context": {}}
    _stack.clear()


def active() -> bool:
    return _session is not None


def context(**kw) -> None:
    """Attach facts about the run (model, size, options) to the current session."""
    if _session is not None:
        _session["context"].update({k: v for k, v in kw.items() if v is not None})


@contextlib.contextmanager
def phase(name: str):
    """Time a block; nested blocks get `outer/inner` names. A no-op outside a session."""
    if _session is None:
        yield
        return
    _stack.append(name)
    path = "/".join(_stack)
    t0 = time.perf_counter()
    ok = True
    try:
        yield
    except BaseException:
        ok = False
        raise
    finally:
        _stack.pop()
        _session["phases"].append({"name": path, "s": round(time.perf_counter() - t0, 4),
                                   **({} if ok else {"failed": True})})


def model_size(prob) -> dict:
    m, s = prob.model, prob.spec
    return {"states": len(m.states), "inputs": len(m.inputs), "params": len(m.params),
            "algebraics": len(m.algebraics), "equations": len(m.equations_flat()),
            "certify": len(s.certify), "disturbances": len(s.disturbances),
            "uncertain": len(s.uncertain), "references": len(s.references)}


def _git(root: Path) -> str | None:
    try:
        r = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=root, capture_output=True,
                           text=True, timeout=5)
        if r.returncode != 0:
            return None
        dirty = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no"],
                               cwd=root, capture_output=True, text=True, timeout=5).stdout.strip()
        return r.stdout.strip() + ("+dirty" if dirty else "")
    except (OSError, subprocess.SubprocessError):
        return None


def log_path(root: Path | None = None) -> Path | None:
    env = os.environ.get("DYNACERT_TIMINGS")
    if env == "0":
        return None
    if env:
        return Path(env)
    if root is None:
        from .api import find_root

        try:
            root = find_root()
        except FileNotFoundError:
            return None
    return Path(root) / "bench" / "timings.jsonl"


def finish(exit_code: int, root: Path | None = None) -> Path | None:
    """Append the session to the log (best effort; never raises)."""
    global _session
    s, _session = _session, None
    if s is None:
        return None
    try:
        path = log_path(root or s["context"].get("root"))
        if path is None:
            return None
        ctx = dict(s["context"])
        root_dir = Path(ctx.pop("root", None) or path.parent.parent)
        rec = {"time": datetime.now(timezone.utc).isoformat(timespec="seconds"),
               "command": s["command"], "exit": exit_code,
               "total_s": round(time.perf_counter() - s["started"], 4),
               **ctx, "phases": s["phases"],
               "git": _git(root_dir), "host": socket.gethostname(),
               "cpu": platform.processor() or platform.machine(),
               "python": sys.version.split()[0]}
        try:
            import rumoca

            rec["rumoca_py"] = rumoca.version()
        except Exception:  # noqa: BLE001 - optional
            pass
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "a") as f:
            f.write(json.dumps(rec, default=str) + "\n")
        return path
    except Exception:  # noqa: BLE001 - timing must never break a run
        return None


# --- reading -----------------------------------------------------------------------------------

def load(path: Path | None = None) -> list[dict]:
    path = path or log_path()
    if path is None or not path.exists():
        return []
    out = []
    for line in path.read_text().splitlines():
        try:
            out.append(json.loads(line))
        except json.JSONDecodeError:
            continue
    return out


def report(records: list[dict], model: str | None = None, approach: str | None = None,
           phases: bool = False) -> str:
    """Per model × command kind: runs, latest and median total, and the slowest phase."""
    import statistics

    rows = {}
    for r in records:
        if model and r.get("model") != model:
            continue
        kind = r.get("approach") or r.get("verb") or "assess"
        if approach and kind != approach:
            continue
        rows.setdefault((r.get("model", "?"), kind), []).append(r)
    if not rows:
        return "no timing records yet (they are written by every dynacert run)"
    lines = [f"{'model':<28} {'run':<12} {'n':>3} {'latest s':>9} {'median s':>9}  slowest phase"]
    for (m, k), rs in sorted(rows.items(), key=lambda kv: -kv[1][-1]["total_s"]):
        last = rs[-1]
        top = [p for p in last.get("phases", []) if "/" in p["name"]] or last.get("phases", [])
        slow = max(top, key=lambda p: p["s"], default=None)
        med = statistics.median(x["total_s"] for x in rs)
        sl = f"{slow['name']} {slow['s']:.1f}s" if slow else ""
        lines.append(f"{m:<28} {k:<12} {len(rs):>3} {last['total_s']:>9.1f} {med:>9.1f}  {sl}")
        if phases:
            for p in last.get("phases", []):
                lines.append(f"{'':<28}   {'  ' * p['name'].count('/')}{p['name'].split('/')[-1]:<28}"
                             f" {p['s']:>8.2f}s")
    return "\n".join(lines)
