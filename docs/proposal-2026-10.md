# dynacert: proposal for the next phase

Status: draft for review, 2026-10-12. Once the decisions in §5 are made, the result replaces
§7 of [roadmap.md](roadmap.md).

## 1. Summary

dynacert works end to end for linear models: an annotated `.mo` file becomes a kernel-checked
theorem about rumoca's transcription of the model. The Lean library is ahead of the generator.
`Lie/`, `Nonlinear/` and the regional polytopic results are proved, but the Python side can
only emit LTI certificates.

I propose four goals for the next phase, in this order:

1. **Report how tight each bound is.** Every certificate gets a certified upper bound and an
   achieved lower bound from a worst-case disturbance. Today the "simulated peak" comes from
   random inputs and understates the gap. On `ClosedLoop`, the certified bound on |e| is 0.844,
   random simulation reaches 0.734, and the true supremum is 0.756. The certificate is 12%
   conservative, not 15%.
2. **Make the generator independent of the method.** Generate `Spec.lean` from the
   specification alone, and let methods plug in behind it. This is required before any
   non-LTI certificate can be generated.
3. **Certify the quadrotor (flagship).** Finish Phase 2: SE₂(3) log tube, cascade and
   reference envelope, generated from an annotated Modelica model.
4. **Tight linear bounds (research thread).** Certify the peak-to-peak (L1) gain in Lean, so
   the certified bound on linear models becomes the true supremum instead of a Lyapunov
   overestimate. The same matrix-exponential enclosure lemma later supports zonotope sets and
   sampled-data control.

Nonlinear and time-varying models (Phase 3, including cp_reach's polynomial M(t) metric) and sampled-data control follow. They depend on one architectural
decision (D2: deep embedding).

## 2. Where we are

| Area | State |
|---|---|
| Pipeline | `dynacert check` on 3 models (`ClosedLoop`, `ClosedLoopComposed`, `ClosedLoopUncertain`); axiom audit; plots; notebook API |
| Lean library | ~4k lines across Core, Linear, Lie, Nonlinear; no `sorry`, no `native_decide` |
| Generator | One path: `pipeline.linear_problem` → `emit_lti.emit_spec` / `emit_cert`. `Spec.lean` is built from a `LinearProblem`, so the form of the claim currently depends on the linear analysis |
| Methods in Python | `methods/lti.py` only (polytopic vertices are handled inside it) |
| Proved but not generated | SE₂(3) log tube, SO(3) invariance, physical outputs, mean-value enclosures, regional polytopic invariance |
| Validation | Random simulations only; no external benchmarks |
| Repository | No commits yet; CI workflows exist but have never run |

## 3. Milestones

Sizes are relative (S ≈ days, M ≈ 1–3 weeks, L ≈ 1–2 months).

### M0. Baseline (S)
- First commit and push. CI builds the library and every certificate under `certs/`, and runs
  pytest.
- Pin the rumoca `dynacert-lean` commit in a file that CI reads.

**Exit:** CI passes on `main`.

### M1. Tightness report (S)
- `sim.py`: for LTI models, a worst-case input per certified output. It is bang-bang,
  w = w̄·sign(Bᵀe^{Aᵀ(t−s)}cᵢ), from the adjoint. For uncertain or nonlinear models, use
  gradient ascent on the peak through the simulation. Piecewise-constant inputs are
  admissible under `IsSolutionOn`, so these runs stay inside the claim's semantics.
- Untrusted L1 value Σⱼ w̄ⱼ‖Cᵢe^{As}Bⱼ‖₁ for LTI models (the exact supremum from x₀ = 0).
- `certified.json`, `cert.table()` and the plots show the lower bound, the certified bound and
  the gap. The README's "simulated peak" becomes "achieved worst case".

**Exit:** every certificate reports a lower and an upper bound. For LTI, the lower bound matches
the L1 value to within 0.1%.

### M2. Generator split (M)
- `Spec.lean` is emitted from `spec.Spec` plus the model interface (names, types and
  annotations) only. The claim does not change: for every solution that satisfies the
  specification hypotheses, each certified output stays within its bound.
- Each method is a module with `applies(model, spec)`, `search(...)` and `emit_cert(...)`.
  `emit_lti` becomes the first one.
- Portfolio dispatch: try the applicable methods from cheapest to most expensive; the first
  certificate that builds wins. `certified.json` records which method produced it.
- A `Link.lean` layer for structural facts (error coordinates now; `lieGroup` later).

**Exit:** the three existing certificates regenerate through the new path with the same
`Claim`. Adding a method touches no code that generates the spec.

### M3. Linear parity with cp_reach (M)
- Output feedthrough `D w`, Euclidean disturbance groups (annotation `norm = "2"`).
- HCW and TH-LTV satellite examples.
- Large PSD witnesses: a float Cholesky plus a diagonally dominant rational residual, still
  checked by `decide +kernel`. This is needed before the M4 vertex LMIs.

**Exit:** every linear cp_reach example certified, with plots and tightness. cp_reach can then
be archived (D6).

### M4. Quadrotor (L), flagship
- Lean: a controller-specific supply theorem (vertex LMIs + `control_residual_bounds`), and the
  angular-rate cascade through `CoupledTube`.
- Reference envelope via gnc_lean's Bernstein checker.
- rumoca: `lieGroup(...)` model annotation. Python: algebra controller, vertex P, radius fixed
  point, emission as a method under M2.
- Example: an annotated quadrotor `.mo` that mirrors cp_reach's flowpipe example.

**Exit:** `dynacert check Quadrotor.mo` produces a theorem with no hypotheses beyond the
annotations, plus physical position, velocity and attitude bounds and a tightness report.

### M5. Certified L1 bounds for LTI (M–L), research thread, in parallel with M4
- Lean, proved once:
  - variation of constants for `IsSolutionOn` (right derivatives);
  - rational enclosures of e^{As} on an interval (Taylor terms plus remainder);
  - a tail bound ‖e^{As}‖ ≤ κe^{−αs} from an existing `PSDWitness`.
- Certificate data: a partition of [0, T₀], enclosures of |Cᵢe^{As}Bⱼ| on each subinterval, and
  the tail constants. A new method under M2; the portfolio keeps whichever bound is tighter.
- The same enclosure lemma later supports a discretized zonotope robust-invariant set and
  sampled-data control (M7).

**Exit:** `ClosedLoop` with |e| certified at ≤ 0.76 (currently 0.844).

### M6. Nonlinear and time-varying models (L)

cp_reach's pendulum (paper Table I) and both layers of its cascade use a time-varying
polynomial metric M(t) = Σ tʳMᵣ (`reachability/polytopic.py`). cp_reach checks it with
`certify_lipschitz_grid`, which is not sound:
- the LMI is imposed only at sample times;
- the Lipschitz constant of F(t) is estimated from 100 samples, then multiplied by 1.5;
- the Jacobian vertices are θ_ref(t) ± ε, found by substituting the corners, which does not
  enclose cos;
- nothing proves that the ε box is invariant.

dynacert's version:
- **Lean, proved once:**
  - a dissipation/Grönwall lemma for V(t, x) = xᵀM(t)x with right derivatives;
  - a lemma that a matrix polynomial on [a, b] is PSD if every one of its Bernstein
    coefficient matrices is PSD. This is a convex-combination argument; gnc_lean has the
    scalar Bernstein checker.
- **Certificate per subinterval [tₐ, t_b]:**
  - a polytope that encloses J over (t ∈ [tₐ, t_b], error in the region), from mean-value
    gains (`Nonlinear/Enclosure`);
  - for each vertex, a `PSDWitness` on each Bernstein coefficient of the block LMI, which is
    polynomial in t and affine in J;
  - the region closed by `regional_invariant`, so the ε box is part of the conclusion and not
    an assumption.
- **Reference:** θ_ref must be polynomial on each segment (min-snap already produces this), or
  enclosed by Bernstein.
- **Second nonlinear method:** interval / mixed-monotone embeddings. These need D2 so the kernel
  can evaluate the model's expressions.

The claim then holds on [0, T_ref], so this milestone needs the `horizon` annotation (D4).

**Exit:** the cp_reach pendulum example certified with a time-varying metric. Report its bound
next to cp_reach's published Table I value.

### M7. Sampled-data control (L)
- Modelica clocked controllers, using the zero-order-hold step from M5's e^{Ah} enclosure plus
  intersample bounds.

**Exit:** the quadrotor from M4 with a discrete-time controller at a fixed rate.

### Continuous: external validation
- Compare against CORA on the same models, and run the linear ARCH-COMP benchmarks once M3 is
  done. Tightness from M1 makes these comparisons quantitative.

## 4. Dependencies

```
M0 ─► M1
M0 ─► M2 ─► M3 ─► M4 ─► M7
      M2 ─► M5 ─────────► M7   (e^{Ah} enclosure)
      D2 ─► M6
```

## 5. Decisions for you

| # | Question | My recommendation |
|---|---|---|
| D1 | Flagship for this phase: quadrotor (M4) or tight linear bounds (M5)? | Quadrotor first; M5 in parallel as the research thread |
| D2 | Add a deep embedding (expression tree + `eval`) to rumoca's `lean-dae`, next to the current equations? | Yes, before M6. Emit both, plus a per-model lemma (`eval tree = equations`, by `simp`/`rfl`), so the trusted transcription stays readable |
| D3 | Default disturbance norm | Keep componentwise peak; `norm = "2"` opt-in per group |
| D4 | Add `horizon` and `unsafe` annotations (finite-horizon and reach-avoid claims)? | Add `horizon` in M6, where time-varying metrics need it (the reference trajectory ends); defer `unsafe` |
| D5 | Upstream rumoca's vendor-annotation pass-through | Propose after M2, once the vocabulary is stable |
| D6 | cp_reach | Archive after M3 |
| D7 | Trust policy | Keep it: kernel only, no `native_decide`. Results that are not checked are reported as non-results, never as weaker certificates |
| D8 | Venue or deadline? | Your call. It decides whether M1+M5 (tightness, smaller scope) or M4 (quadrotor, bigger scope) is the paper |

## 6. Not doing in this phase

- Hamilton–Jacobi or learned barriers.
- Wrapping CORA or JuliaReach flowpipes (revisit after M5, which provides the enclosure lemmas
  their certificates would need).
- LeanCert, unless its axioms pass our audit.

## 7. Risks

| Risk | Mitigation |
|---|---|
| `decide +kernel` too slow on SE₂(3) vertex LMIs | Diagonally dominant residual witnesses (M3); split vertices into separate declarations |
| rumoca fork drifts from upstream | Pin in CI (M0); upstream after M2 (D5) |
| gnc_lean's Mathlib pin falls behind | Follow gnc_lean's pin; bump together |
| Variation of constants for right-derivative solutions is harder than expected | Reuse the right-derivative Grönwall in `Core/Dissipation`; if it stalls, M5 waits and M4 proceeds unaffected |
| Generator split (M2) changes generated claims | Exit criterion: identical `Claim` for the existing certificates |
