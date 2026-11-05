# No new proof per model

Status: in progress, 2026-10-31.

## The rule

A new model must not need a new Lean theorem. Per model, dynacert emits only:

- **data**: rational matrices, multipliers, levels, checked by `decide +kernel`;
- **wiring** in a fixed tactic vocabulary: `simp only [registered lemmas]`, `linear_combination`
  with coefficients computed in Python, `ring`, `norm_num`, and applications of library
  theorems.

The emitter is deterministic Python. If a build fails, either the search failed or the emitter
has a bug; it is never a missing proof. New Lean is written once, as a library addition, and
only for new mathematics:

| Addition | When | Example |
|---|---|---|
| atom lemma | a Modelica function without a bound | `sin_sub_self_gain`, `inputResidual_le`, `enorm_leftAt_sub_le` |
| transform | a new change of coordinates | SE₂(3) log error (`field_split`), error coordinates, scalarization |
| combinator | a new way to join certificates | assume–guarantee, coupled storage, scheduled metric |

`assess` should report a missing atom or transform by name, e.g. "no atom lemma for
`LieGroups.SE23.Jl_inv`", so that the gap is explicit.

## The normal form

`Dynacert/Normal/QC.lean`. On a region, the closed loop in some coordinates `x` reads

```
ẋ = (Σᵢ λᵢ Aᵢ) x + B w,     λ in the simplex,     0 ≤ ζᵀ Mⱼ ζ  (ζ = (x, w)),
```

- the **polytope** `Aᵢ` carries time variation and uncertainty (reference envelopes,
  schedules, parameter boxes);
- `w` holds every non-linear signal: atom residuals, disturbances, interface signals;
- the **quadratic constraints** `Mⱼ` are what atom lemmas prove on the region. A sector atom
  gives `qcSector`, a norm bound `‖r‖ ≤ ℓ‖x‖` gives `qcDiag`, and any S-procedure term is a
  rational matrix.

`QCCert` is one LMI per vertex with a common `P` and multipliers `τⱼ ≥ 0`.
`QCCert.supply` gives `V̇ ≤ -αV + Σγw² + Σσ(rζ)²` on the polytope wherever the constraints hold;
`QCCert.regional_invariant` gives the tube. `SectorCert` is the one-vertex case with sector
constraints, and `PolytopicCert` the case without constraints.

## SE₂(3) without a control law

- `Lie.field_split` (`Dynacert/Lie/Field.lean`): for **any** inputs, the exact log-error field
  is
  `refDrift ā ω̄ ξ + (0, ã, ω̃) + inputResidual ξ ã ω̃ + gravity term`.
  `refDrift` is linear in `ξ` with coefficients linear in `(ā, ω̄)`, so an envelope on the
  reference is a polytope.
- `Lie.inputResidual_le`: on `‖ξ‖ ≤ D ≤ 2` with `‖ã‖ ≤ A`, `‖ω̃‖ ≤ W`,
  `‖inputResidual‖ ≤ inputGain D A W · ‖ξ‖`, i.e. one `qcDiag` constraint.
- `Lie.log_tube_qc` (`Dynacert/Lie/NormalTube.lean`): if the field has the normal form of a
  `QCCert` on the certified sublevel, the log error stays in the principal domain and in the
  sublevel, and the storage decays to `budget/α`.

A controller enters only through `ũ = (ã, ω̃)`:

- written in **log coordinates** (L3QR, log-linear backstepping): `ũ = Kξ` up to Jacobian
  factors, which are atoms;
- written in **group-error coordinates** (body-frame PD, geometric laws): `ũ = Kξ +` coordinate
  residuals bounded by `enorm_leftAt_sub_le`, `enorm_attErr_sub_le`.

Gravity enters through `gravity_residual_const` (constant gravity: zero) or
`gravity_residual_inverse_square` (a norm bound).

## Where each method stands

| Method | Per-model Lean | Status |
|---|---|---|
| `lmi`, `polyhedral`, `switched` | data + generated link | general |
| `sector`, `compose` | data + link + atom facts | general for registered atoms |
| `layered` | composes per-layer certificates | general |
| `lie` | `pd_spacecraft_tube`: one theorem per controller and gravity model | **to migrate** |

## Next steps

1. Re-certify `SpacecraftTracking` through `log_tube_qc`. The per-model link proves
   `hnormal`: `field_split`, then the PD law as `Kξ` plus coordinate residuals, then one
   constraint per atom (coordinate residuals, `inputResidual_le`, gravity). Then delete
   `pd_spacecraft_tube` and `emit_lie.recognize`.
2. Recognize the inputs `ũ` generically from the model's equations instead of matching a PD
   pattern. The link only needs the controller's equations to normalize to `Kξ + atoms`.
3. Reference envelopes: a lemma giving simplex weights for `(ā, ω̄)` in a box, so that moving
   references use `refDrift` vertices.
4. Port `emit_sector` to emit `QCCert`, so that one emitter serves both paths.
5. Atoms the two SE₂(3) papers need: `J(ξ)⁻¹` and `Q(ρ, ϕ)` blocks, the dead-zone generalized
   sector condition, and projection.
