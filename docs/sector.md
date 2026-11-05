# Sector multipliers and where to tear

dynacert's `sector` and `compose` methods implement the paper *Where to Tear: Compositional
Invariant-Tube Certificates for a Nonlinear Quadrotor* (Condie) as Lean-checked certificates.
Python finds the certificate; the Lean kernel checks every number, including the sector and
peak bounds of the nonlinear residuals, which the paper evaluated on a grid (its "rigorous
bounds" direction).

```bash
dynacert examples/aerospace/PlanarQuadrotor.mo sector        # joint certificate (§V)
dynacert examples/aerospace/PlanarQuadrotor.mo compose       # cut chosen + ADMM (§VI, §VIII)
dynacert examples/aerospace/PlanarQuadrotor.mo compose --cut "e_x,e_z,v_x,v_z | theta,q"
dynacert examples/aerospace/PlanarQuadrotor.mo validate --sample --n 500
```

## 1. Exact linear part plus residual channels

The closed loop is written exactly as `ż = A z + B_p p + B_w w`, with `A` the Jacobian at the
operating point and each residual `pᵢ` either a **sector** channel `pᵢ = δᵢ(t) qᵢ`,
`δᵢ ∈ [ℓᵢ, uᵢ]`, or a **bounded** channel `|pᵢ| ≤ βᵢ`, on a region box `R`.
`sector.extract` finds the split from rumoca's equations. Each nonlinear atom is its first-order
part plus a remainder:

| Atom | First order | Remainder on `R` | Lean lemma (`Dynacert/Sector/Atoms.lean`) |
|---|---|---|---|
| `sin θ` | `θ` | `sin θ − θ = δ θ`, `δ ∈ [−a²/6, 0]` (sector) | `sin_sub_self_gain` |
| `sin θ` as a factor | | `\|sin θ\| ≤ a` | `abs_sin_le_of` |
| `cos θ` | `1` | `\|cos θ − 1\| ≤ a²/2` (bounded) | `abs_cos_sub_one_le` |
| `√(s² + h²)` | `h` | `0 ≤ √(s²+h²) − h ≤ b²/(2h₀)` (bounded) | `sqrt_sub_mem`, `abs_sqrt_le` |
| `atan2(y, h)` | `y / h(0)` | `atan2(y,h) − y/h(0) = δ y`, `δ ∈ [(1 − b²/3h₀²)/h₁ − 1/h(0), 1/h₀ − 1/h(0)]` (sector) | `atan2_sub_gain` (via `arctan`, `x − x³/3 ≤ arctan x ≤ x`) |

Products follow the paper's Table II: `F·S` with `S(0) = 0` becomes
`F(0)·S` (recursively) `+ F₁·S` (sector, `q = F₁`, `δ = S`) `+ ρ_F·S` (bounded); `F·cos θ`
becomes `F + F·(cos θ − 1)` (bounded). Linear algebraic variables (`s_x = Kp e_x + Kv v_x`)
are substituted; nonlinear ones (`f_norm = √(…)`, `θ_d = atan2(…)`) are the atoms. On the
planar quadrotor this recovers exactly the six channels of the paper's Table II:

| `pᵢ` | `qᵢ` | enters | kind |
|---|---|---|---|
| `sin θ − θ` (×g) | `θ` | `v̇_x` | sector |
| `−s_z sin θ` | `−s_z` | `v̇_x` | sector |
| `(‖f‖ − (g − s_z)) sin θ` | | `v̇_x` | bounded |
| `‖f‖ − (g − s_z)` | | `v̇_z` | bounded |
| `‖f‖ (cos θ − 1)` | | `v̇_z` | bounded |
| `θ_d + s_x/g` (×kθ) | `−s_x` | `q̇` | sector |

## 2. Lean theorems (proved once)

| File | Theorem | Paper |
|---|---|---|
| `Dynacert/Sector/LMI.lean` | `DomWitness`: `M = Lᵀ diag(d) L + R` with `R` diagonally dominant ⇒ `M ⪰ 0` (`quad_nonneg_of_diagDom`); `form`/`quad_form` (sums of products of linear forms); `supply_le`: an LMI witness gives `V̇ ≤ −αV + ζᵀSζ` | LMI (8), (9) |
| `Dynacert/Sector/Cert.lean` | `SectorData`, `SectorCert`, **`SectorCert.supply`**: wherever the sector constraints hold, `V̇ ≤ −αV + Σγⱼwⱼ² + Σσₖ(rₖζ)²`; `energy_le`; `LinearBoxDom` (output bounds by support function) | Theorem 1 |
| `Dynacert/Sector/Invariance.lean` | **`region_invariant`**: storages that dissipate while `{V_j ≤ b_j}` holds stay in `{V_k ≤ c_k}`, `c < b` (first exit via `Compose.assume_guarantee` + Grönwall); `sector_nonneg`; **`compose_storage`**; `supply_pair_le` | Lemma 1, Proposition 1 |
| `Dynacert/Sector/Atoms.lean` | the bounds of §1 | "rigorous bounds" |

The LMI witness is a rounded floating-point `LDLᵀ` plus a diagonally dominant remainder,
checked by `decide +kernel`. Unlike an exact `LDLᵀ`, the data stay small (the denominators do
not blow up), so a 15×15 LMI checks in well under a minute and a few GB.

## 3. Per-model certificate

`certs/Certs/<Model>/`:

| File | Content |
|---|---|
| `SectorLink.lean` | coordinates (the states), the channels as real functions of rumoca's variables, `link` (`ż = A z + B w` by `linear_combination` of the equations), `facts` (on the region every channel satisfies its sector or peak bound, from the atom lemmas) |
| `SectorM<k>.lean` | ellipsoid `k` (one per certified output and region coordinate, Lemma 1): `SectorData`/`SectorCert` per block, `diss` (`V̇ ≤ −αV + αc` wherever the facts hold), box certificates |
| `SectorCert.lean` | `tube` (all ellipsoids invariant, by `region_invariant`) and `certified : Spec.Claim b` |
| `sector.json` | region, channels with their intervals, ellipsoids, fixed-point history, timings |

`compose` writes the same files with prefix `Compose`; each ellipsoid's storage is the sum of
block storages, each block LMI (9) is checked separately, and the interconnection condition
`σ_received ≤ σ_sent` is a rational inequality.

## 4. Region fixed point (Algorithm 1)

Start from a small box; evaluate `ℓ, u, β` on it (exact rationals, rounded outward); for each
objective (the certified outputs and the region coordinates) solve LMI (8) minimizing `cᵀP⁻¹c`
over an α grid; take the smallest projection of every region coordinate over all ellipsoids;
stop when the projections are strictly inside the box (Lemma 1), else enlarge the box to
`max(R, 1.02 r)`. The final LMIs are re-solved with a margin so that rounding to small
rationals keeps them feasible, and the region level `b` is the largest level whose box
projections fit in `R`.

## 5. Where to tear

`cuts.py`:

* **Coupling graph.** An edge `j → i` when `ẋᵢ` depends on `xⱼ`: *strong* if `Aᵢⱼ ≠ 0`
  (first order), *weak* if only through a residual channel.
* **Candidates.** The strongly connected components of the strong graph are the proposed
  blocks. For comparison every bipartition that cuts at most three strong edges (state pairs) is listed too.
* **Proposition 2.** If no block-diagonal `P ≻ 0` has `AᵀP + PA ≺ 0`, no static supply rate
  certifies across the cut, at any disturbance level: one small SDP per candidate.
* **ADMM.** Each block solves its LMI (9) with a proximal term on its interface scalars (the
  supply rates and its share of the disturbance budget); the coordinator projects onto
  `{σ_received ≤ σ_sent, Σ budgets ≤ 1}`; scaled duals are updated. The final scalars are
  fixed and each block re-solved alone, so the certificate is exactly consistent.

## 6. Results on the planar quadrotor

`examples/aerospace/PlanarQuadrotor.mo` (ωn = 10, 5× bandwidth separation) at the paper's 25 %
level (`|w_x|, |w_z| ≤ 0.25`, `|w_q| ≤ 1.25`) is certified in Lean by both methods:

| | `sector` (joint, §V) | `compose` (cut B, ADMM) | paper |
|---|---|---|---|
| `\|e_x\|` | 4011/25000 ≈ 0.16044 m | 0.160473 m | 0.178 m |
| `\|θ\|` | 0.145879 rad | 0.145911 rad | 0.164 rad |
| region `\|s_x\|, \|s_z\|, \|θ\|` | 1.449, 0.681, 0.147 | same | |
| Monte Carlo max (500 runs, 12 s) | 0.0937 m (58 %), 0.0766 rad (53 %) | | 0.093 m (52 %), 0.076 rad |
| theorem | `PlanarQuadrotor.SectorCert.certified` | `PlanarQuadrotor.ComposeCert.certified` | |
| axioms | `propext`, `Classical.choice`, `Quot.sound` | same | |
| time | search 25 s, Lean ≈ 3.5 min (6 modules, < 6 GB each) | search 25 s + ADMM 18 s, Lean ≈ 3.5 min | |

The rigorous (Taylor) bounds are tighter than the paper's grid with a 2 % margin, so the
certified tube is about 10 % smaller. Disturbance sweep (search and exact rounding in Python,
the same code path as the Lean-checked case; Monte Carlo 500 runs each):

| w̄ | lin. ellipsoid | tube \|e_x\| (paper) | MC max \|e_x\| (paper) | ratio | tube \|θ\| (paper) | MC max \|θ\| |
|---|---|---|---|---|---|---|
| 0.05 | 0.0217 | 0.0224 (0.024) | 0.0187 (0.019) | 83 % | 0.0194 (0.023) | 0.0150 |
| 0.10 | 0.0433 | 0.0466 (0.048) | 0.0373 (0.037) | 80 % | 0.0407 (0.042) | 0.0302 |
| 0.15 | 0.0650 | 0.0740 (0.076) | 0.0561 (0.056) | 76 % | 0.0653 (0.067) | 0.0455 |
| 0.20 | 0.0867 | 0.1073 (0.110) | 0.0749 (0.074) | 70 % | 0.0956 (0.098) | 0.0610 |
| 0.25 | 0.1083 | 0.1604 (0.178) | 0.0937 (0.093) | 58 % | 0.1459 (0.164) | 0.0766 |
| 0.26 | 0.1126 | fails (fails above 25–26 %) | | | | |
| 1.00 | 0.4333 | fails (fails) | | | | |

At 26 % the region iteration grows until `h = g − s_z` leaves the domain of the `atan2`/`√`
bounds; at full disturbance it fails after two iterations, for ωn = 53.6 and 60 as well (the
paper's 27× result is for the torn certificate, which is not a certificate method here).

**Cut selection.** The strong-edge graph has two components, `{e_x, v_x, θ, q}` and
`{e_z, v_z}`: the proposed cut is the paper's cut B (lateral + pitch | vertical), which cuts no
strong edge and is accepted by Proposition 2. Every bipartition that cuts strong edges,
including cut A (translation | attitude, three strong edges `θ → v_x`, `e_x, v_x → q`), is
rejected by Proposition 2. The only interface of cut B is `s_z` (from the vertical block into
the lateral sector channel `−s_z sin θ`), with supply rates `σ_lat s_z²` and `−σ_vert s_z²`,
`σ_lat ≤ σ_vert` (e.g. 0.486 ≤ 0.4861). Composition is lossless: `compose` proves the same
bounds as `sector` to four digits. ADMM (80 iterations, ρ = 1 on normalized objectives) is
within 0.4 % of the central SDP on every objective (≈ 4.5 s per objective, interconnection
residual ≤ 2·10⁻³ before the final block-wise polish that makes the scalars exactly consistent).

**Loop tearing** (`dynacert … tearing`): treating the cut-A interfaces as bounded signals with
peak-to-peak gains fails outright, since the torn translational block (`ė_x = v_x`,
`v̇_x = gθ`) has no feedback of its own. The paper's §IV construction (inner error
`e_θ = θ − θ_d`, input `θ̇_d`) is not implemented.

## 7. The full 3D vehicle

`examples/aerospace/Quadrotor3D.mo` is the 3D version of the planar model: 12 states (position
and velocity errors, quaternion vector part, body rates), the chart `q0 = √(1 − |q_v|²)`, thrust
`T = f · b3`, tilt command `(kR/g)(ẑ × Rᵀf)`, an ideal rate loop, normalized mass and inertia.

**Polynomial residuals.** Algebraics that are polynomials in the states are inlined (and eliminated
outermost first in the Lean identities). With `ρ = q0 − 1` (second order), each product becomes:

| Order | Treatment | Example |
|---|---|---|
| 1 | `A` | `2g qy` in `v̇_x` |
| 2, a factor already in the row's linearization | sector, `q` = that factor, `δ` = sum of the co-factors: a change of that loop's gain | `2(g − s_z) qy` in `v̇_x`: `q = qy`, `δ ∋ −2 s_z` |
| 2, otherwise | sector, products with the same `δ` are merged into one `q = L(z)` | `v̇_z`: `−2 s_x qy − 4g qy² = qy · (−2 s_x − 4g qy)`, a tilt times the pitch tracking error |
| ≥ 3 | one bounded channel per row | `s_x qy²` |

The merge matters: bounding `s_x qy` and `g qy²` separately loses their cancellation, and `|s_z|`
then roughly doubles per fixed-point iteration. The model gives 18 sector and 8 bounded channels.

**The paper's conjecture (§VIII).** The strong-edge components are exactly two tilt–lateral blocks,
a vertical block and a yaw block: `e_x,v_x,qy,q | e_y,v_y,qx,p | e_z,v_z | qz,r`. Proposition 2
accepts the cut, and the block LMIs close at nearly the joint support (`|e_x|` 0.0535 against
0.0537, `|e_z|` 0.0392 against 0.0391; a rough comparison, since the regions differ slightly and the
block figures use a re-solve margin of 10⁻⁴ against 10⁻⁷), so the decomposition appears to cost
almost nothing here. This is one model and one gain set, not a proof of the conjecture in general.

**Result at 10 % of the planar full level** (`|w_a,i| ≤ 0.1`, `|w_ω,i| ≤ 0.5`), theorem
`Quadrotor3D.ComposeCert.certified`, axioms `propext`, `Classical.choice`, `Quot.sound`:

| Output | certified | Monte Carlo max (500 runs, 12 s) | ratio |
|---|---|---|---|
| `e_x` [m] | 0.054672 | 0.0372 | 68 % |
| `e_y` [m] | 0.054671 | 0.0374 | 68 % |
| `e_z` [m] | 0.040495 | 0.0254 | 63 % |
| `qx` | 0.024589 | 0.0152 | 62 % |
| `qy` | 0.02459 | 0.0151 | 61 % |

Search 13 s; Lean about 3 min per ellipsoid module (12 of them, 20×20 or smaller block LMIs) under an
8 GB cap, built one at a time.

**How far it closes.** With the same cut, in Python: an exact certificate at 10, 11 and 12 %
(`|e_x|` 0.0547, 0.0612, 0.0751); at 13 % the search closes but rounding fails; at 14, 15, 20 and
25 % the LMI becomes infeasible as the region runs away. The planar model closes at 25 %.

```bash
dynacert examples/aerospace/Quadrotor3D.mo compose --solver central
```

Known problems on this model: ADMM stalls at an interconnection residual near 10⁻², so `compose`
falls back to the central SDP (Lean still checks each block LMI separately). The joint `sector`
certificate closes in search but is not practical to check: its 44×44 LMI module was killed at a
10 GB cap.

## 8. Limits

* Atoms: `sin`, `cos` of a state, `√(s² + h²)` and `atan2(y, h)` with affine arguments, `h(0) > 0`,
  `√(1 − Σ xₖ²)`, and polynomials in the states and that chart. Products mixing the chart with other
  atoms, and non-polynomial products of more than two factors, are rejected with a message.
* Equilibrium tubes only (no references, uncertain parameters, arrays, initial sets).
* Each ellipsoid is one block-diagonal quadratic storage; outputs and region coordinates must
  lie in one block of the cut.
* `Quadrotor3D` is not `QuadrotorFullStack`: it has no motors or mixer, an ideal rate loop, a reduced
  quaternion chart instead of four quaternion states, and no reference states.
