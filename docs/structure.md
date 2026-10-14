# Structure discovery

dynacert looks for structure in a model before choosing how to bound it: Lie-group kinematics,
the gravity model, vehicle/reference pairs, layers of sub-components, linearity. A finding
only selects which proof is attempted. Each one that a certificate uses is re-proved in Lean
from rumoca's `Equations`, so a wrong finding makes the build fail and cannot weaken the claim.

```
Model.mo ─rumoca─► Model.lean (trusted)  +  model.py (same IR)
                                             │
             structure.py (untrusted): findings + witnesses
               se23 (p, v, R; a, ω, g) · log-error pair · layers · linear · integrators
                                             │
             link (Lean, generated): Equations ⇒ the structure      lie_link.py, emit_layered.py
                                             │
             bound on the structure (Lean, proved once)              Lie/, Compose/, Linear/
                                             │
             Spec.Claim on the model's own outputs (unchanged)
```

```bash
dynacert examples/QuadrotorTracking.mo structure          # findings
dynacert examples/QuadrotorTracking.mo structure --lean   # + build the SE₂(3) link
dynacert examples/TwoMassLayered.mo layered               # layered certificate
```

## What is detected

Discovery uses rumoca's sympy view with parameter values substituted (uncertain parameters
stay symbolic). Two forms of the dynamics are used:

- **As written.** Each derivative is solved from its own equation, and algebraic variables are
  kept as signals. Lie kinematics are tested on this form. A closed-loop attitude controller
  makes ω depend on R, which would hide `Ṙ = R·skew(ω)` in the fully eliminated form.
- **Fully eliminated** to `der(x) = f(x, u)`. Dependencies (layers, "is this block driven by
  feedback") and gravity classification use this form.

| Finding | Test | Lean that uses it | Status |
|---|---|---|---|
| `so3` | `Ṙ = R·skew(ω)` (or `skew(ω)·R`), ω free of R: `∂Ṙ[i,j]/∂R[i,k]` independent of `i`, skew | `Lie.SO3.rotation_mem_SO3` | proved (right-invariant) |
| `se23` | `ṗ = v`, `v̇ = R a + g`, with a and g free of R, a ≠ 0 | `Lie.spacecraft_of_components` → `ofScalars_solution` | proved, link generated |
| gravity class | g constant / exogenous / isotropic-linear / inverse-square (`-μp/‖p‖³`) / other | `group_affine_iff`, `affine_defect` (gnc) | constant and isotropic-linear are group-affine |
| `log-error` | a feedback-driven SE₂(3) block paired with an open-loop one in the same field | `Lie.log_tube_of_residuals` + residual lemmas | see below |
| `layers` | strongly connected components of the state-dependency graph; Modelica components coupled inside one component | `Compose.assume_guarantee` | proved, layered LTI certificate generated |
| `linear` | `f` linear in states and inputs | `Linear.Channels`, `Linear.Polytopic` | proved |
| `error-coordinates` | certified outputs linear in states and references | linear link | proved |
| `quaternion` | `q̇ = Ω q`, Ω skew | none | report-only |
| `se3` | `ṗ = R u`, `Ṙ = R·skew(ω)` | none (gnc has SE₂(3)) | report-only |
| `integrator` | a state that no derivative reads | none | report-only |

Array states (`Real R[3,3]`, `Real p[3]`) are detected directly, since rumoca keeps arrays in
both targets. Scalar states named like `R11 … R33` or `p_x, p_y, p_z` are grouped by name.

## The Lie-group route

For a vehicle `X` and a reference `Y`, the log error `ξ = log(Y⁻¹X)` has the exact right
derivative `logErrorField` (gnc Proposition 1, `Lie.principal_proposition1_within`). It has
three terms:

```
logDrift(controlInput a ω) ξ  +  J⁻¹(ξ)·controlInput(a − ā, ω − ω̄)  +  J_r⁻¹(ξ)·Ad_{X⁻¹}(0, g − ḡ, 0)
```

`Lie.log_tube_of_residuals` (in `Lie/Supply.lean`) proves the chart-closing tube from three
ingredients:

- vertex LMIs;
- the decomposition `flat(field) = Σ wᵢ Aᵢ ξ + B d + Σₖ rₖ`;
- sector bounds `‖rₖ‖ ≤ ℓₖ‖ξ‖` on the certified sublevel.

The decay rate it proves is `α − 2‖P‖Σℓ/m`. Models with the same group structure differ only
in their residual list:

| Model | Gravity residual | Lemma |
|---|---|---|
| Quadrotor, constant g | identically zero (group-affine) | `Lie.gravity_residual_const`; the generated `gravity_eq_*` shows g = ḡ from `Params.Bound` |
| Spacecraft, inverse-square | `‖·‖ ≤ (1/(1−Rc²/16))·2μ/(r_min(r_min−D)²)·‖ξ‖` on `‖ξ‖ ≤ D < r_min`, attitude error `≤ Rc ≤ 2` | `Lie.gravity_residual_inverse_square` (from gnc `log_mismatch_bound`); the generated `gravity_field_*` shows g = `Gravity.field3 μ p` |
| Isotropic-linear g = c·p | exactly `c ξ_p`, linear | lemma not written |

The generated `LieLink.lean` takes `a`, `ω` and `g` from rumoca's own Lean equations, so each
kinematic identity closes by `exact`. It proves `SpacecraftSolution` for every block, with
`R ∈ SO(3)` for all time.

**Not yet done.** The control residual depends on the control law: the model's `a − ā` and
`ω − ω̄` have to be written as `K ξ +` (bounded remainder) on the certified set. A body-frame
error such as `R̄ᵀ(p − p̄)` equals `J_l(ξ_R) ξ_p`, not `ξ_p`. Until that decomposition lemma,
the vertex-LMI search and the radius fixed point exist, a `log-error` finding is report-only:
the link is proved, but there is no tube certificate yet.

## The layered route

`emit_layered.py` handles a linear model whose states split by Modelica component. Each
component gets its own LTI certificate, with the states it reads from other components as
extra disturbance channels with assumed bounds `b`. Python iterates `b ← c(b)` until every
layer guarantees `c < b` strictly. Lean checks each layer and closes the loop with
`Compose.assume_guarantee`: at the first time any assumption could fail, every guarantee
still holds strictly, and continuity extends the assumptions a little further. No small-gain
theorem is needed beyond the strict inequalities, which the kernel checks with
`decide +kernel`.

`Spec.lean` is the same file the `lmi` approach emits, so the two certificates prove the same
`Claim` and can be compared directly. The certificate goes to `LayeredCert.lean`, and the
bounds go to `layered.json` along with the monolithic LMI bounds. On `TwoMassLayered`:

| Output | Layered | Monolithic LMI |
|---|---|---|
| \|a.x\| | 1.3602 | 1.3309 |
| \|b.x\| | 0.5490 | 1.0105 |

Each layer gets its own ellipsoid, which can be much tighter for the weakly forced component.
Peak-bound composition fails when the coupling is strong; `layered` then reports that no
consistent bounds exist. gnc's `CoupledTube` (a joint weighted energy) is the alternative for
that case and is not generated yet.

Current limits: linear layers only (a Lie layer would plug into the same composition theorem);
no references or uncertain parameters; outputs and coupling signals must be states.
