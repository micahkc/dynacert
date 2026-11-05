"""Emit `certs/Certs/<Model>/PolyCert.lean`: a polyhedral RPI certificate for an LTI model.

The file imports the model's LMI certificate `Certs.<Model>.Cert` and reuses its link proof
(`Cert.model`, `Cert.vec`, `Cert.dist`, `Cert.link`, `Cert.init`, `Cert.out<k>`), so the
polyhedral method needs a current LMI certificate. The final theorem is
`<Model>.PolyCert.certified : Spec.Claim b` for the same, untouched `Spec.lean`.

The Metzler matrix `M` is stored sparsely (`SparsePolyCert`: a list of `(column, value)` per
row), which keeps the kernel check roughly quadratic in the facet count instead of cubic.
"""

from __future__ import annotations

from fractions import Fraction

from . import lean
from .lean import mat, q, vec


def _sparse_rows(M) -> str:
    rows = []
    for r in M:
        ent = [f"({j}, {q(v)})" for j, v in enumerate(r) if v != 0]
        rows.append("[" + ", ".join(ent) + "]")
    return "![" + ",\n    ".join(rows) + "]"


def cert_supported(cert_src: str) -> str | None:
    """Why the LMI certificate's link cannot be reused, or None if it can."""
    for needle in ("def vec", "def dist", "theorem link", "theorem init_le", "def model : LTIModel"):
        if needle not in cert_src:
            return f"Cert.lean has no `{needle.split()[-1]}` (only point initial conditions and " \
                   "single-model LTI certificates are supported)"
    if "Initial p (x 0)" not in cert_src:
        return "the LMI certificate uses an initial set; v1 supports a fixed initial point"
    return None


def emit(pb, pc) -> str:
    """Lean source of `PolyCert.lean` for the linear problem `pb` and certificate `pc`."""
    ns = pb.ns
    n, m, k = len(pb.coords), len(pb.dists), pc.facets
    bvec = vec([o.bound for o in pc.outputs])
    out = [f"import Certs.{ns}.Cert", "import Dynacert.Linear.Polyhedral", ""]
    out += lean.header(f"Polyhedral certificate for `{ns}`", "dynacert (polyhedral, fixed K)")
    out += [
        "set_option linter.style.setOption false",
        "set_option linter.style.longLine false",
        "set_option linter.unusedSimpArgs false",
        "set_option linter.unusedTactic false",
        "set_option linter.unreachableTactic false",
        "set_option linter.unnecessarySeqFocus false",
        "set_option linter.flexible false",
        "set_option linter.unusedVariables false",
        "set_option linter.style.show false",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "",
        f"namespace {ns}.PolyCert",
        "",
        f"open Matrix Set Dynacert Dynacert.Linear {ns}",
        "",
        f"/-! ### The polytope `{{z | H z ≤ hv}}` ({k} facets) and its Metzler matrix -/",
        "",
        f"def H : Matrix (Fin {k}) (Fin {n}) ℚ := {mat(pc.H)}",
        f"def hv : Fin {k} → ℚ := {vec(pc.h)}",
        "/-- Rows of the Metzler matrix `M` as `(column, value)` lists (other entries zero). -/",
        f"def Msp : Fin {k} → List (Fin {k} × ℚ) :=\n  {_sparse_rows(pc.M)}",
        f"def δ : Fin {m} → ℚ := {vec(pc.delta)}",
        "",
        "/-- `M` Metzler, `H A = M H`, and `M hv + |H B| δ < 0`, checked row by row by the",
        "kernel. -/",
        f"def scert : SparsePolyCert Cert.model {k} :=",
        "  ⟨H, hv, Msp, δ, by decide +kernel, by decide +kernel, by decide +kernel⟩",
        "",
        f"def cert : PolyCert Cert.model {k} := scert.toPolyCert",
        "",
    ]
    for i, o in enumerate(pc.outputs):
        name = pb.outputs[i].name
        out += [
            f"/-- `|{name}| ≤ {q(o.bound)}` on the polytope (LP duality). -/",
            f"def pout{i} : PolyOutputCert H hv {vec(o.row)} ({q(o.bound)}) :=",
            f"  ⟨{vec(o.lp)},",
            f"   {vec(o.lm)},",
            "   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,",
            "   by decide +kernel, by decide +kernel⟩",
            "",
        ]
    x0v = vec(pb.x0)
    out += [
        "theorem init_mem :",
        f"    (fun i => ((({x0v} : Fin {n} → ℚ) i : ℚ) : ℝ)) ∈ polytope H hv :=",
        f"  mem_polytope_cast (v := {x0v}) (by decide +kernel)",
        "",
        "/-- **Tube.** Under the hypotheses of `Spec.Claim`, the error-frame state",
        "`z = Cert.vec (x t) (u t)` stays in the certified polytope `{z | H z ≤ hv}` on `[0, T]`. -/",
        "theorem tube : ∀ (p : Params) (u : ℝ → Inputs) (x : ℝ → States) (y : ℝ → Algebraics)",
        "    (T : ℝ), p.Bound → IsSolutionOn p u x y T → Spec.Admissible u T →",
        "    Spec.References u T → Spec.ReferenceStart u → Initial p (x 0) →",
        "    ∀ t ∈ Icc 0 T, Cert.vec (x t) (u t) ∈ polytope H hv := by",
        "  intro p u x y T hp h hu hr hr0 h0",
        "  have hx := Cert.link hp h hr",
        "  have hw : ∀ t ∈ Ico 0 T, ∀ j, |Cert.dist (u t) j| ≤ (cert.δ j : ℝ) := by",
        "    intro t ht j",
        "    have hut := hu t ht",
        "    fin_cases j <;> simp [Cert.dist, cert, scert, SparsePolyCert.toPolyCert, δ] <;> simp_all",
        "  have h0' : Cert.vec (x 0) (u 0) ∈ polytope cert.H cert.h := by",
        "    rw [Cert.init hp h0 hr0]; exact init_mem",
        "  exact cert.invariant hx hw h0'",
        "",
        f"/-- **Certified.** The claim of `Spec.lean` holds with the bounds `{bvec}`. -/",
        f"theorem certified : Spec.Claim {bvec} := by",
        "  intro p u x y T hp h hu hr hr0 h0",
        "  have hV := tube p u x y T hp h hu hr hr0 h0",
    ]
    groups = []
    for rng, kind in (("Icc", "state"), ("Ico", "algebraic")):
        ks = [i for i, o in enumerate(pb.outputs) if o.kind == kind]
        if ks:
            groups.append((rng, ks))
    if len(groups) > 1:
        out.append("  refine ⟨?_, ?_⟩")
    for rng, ks in groups:
        ind = "    " if len(groups) > 1 else "  "
        pre = "  · " if len(groups) > 1 else "  "
        tt = "ht" if rng == "Icc" else "⟨ht.1, ht.2.le⟩"
        out.append(f"{pre}intro t ht")
        if len(ks) > 1:
            out.append(f"{ind}refine ⟨{', '.join('?_' for _ in ks)}⟩")
        for i in ks:
            b = f"{ind}· " if len(ks) > 1 else ind
            out.append(f"{b}rw [Cert.out{i} hp h ht]; exact pout{i}.abs_le (hV t {tt})")
    out += ["", f"end {ns}.PolyCert", ""]
    return "\n".join(out)


def sidecar(pb, pc, theorem: str, axioms, lmi_bounds: dict | None = None) -> dict:
    return {
        "model": pb.model_name, "ns": pb.ns, "method": "polyhedral",
        "coords": [c.name for c in pb.coords],
        "facets": pc.facets,
        "H": [[q(v) for v in r] for r in pc.H],
        "h": [q(v) for v in pc.h],
        "M": [[q(v) for v in r] for r in pc.M],
        "delta": [q(v) for v in pc.delta],
        "x0": [q(v) for v in pb.x0],
        "outputs": [{"name": po.name, "row": [q(v) for v in o.row], "bound": q(o.bound),
                     **({"lmi_bound": lmi_bounds[po.name]} if lmi_bounds and
                        po.name in lmi_bounds else {})}
                    for po, o in zip(pb.outputs, pc.outputs)],
        "stats": pc.stats,
        "theorem": theorem, "tube_theorem": theorem.rsplit(".", 1)[0] + ".tube",
        "axioms": sorted(axioms),
    }


def bounds(pc) -> list[Fraction]:
    return [o.bound for o in pc.outputs]
