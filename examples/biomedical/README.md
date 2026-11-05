# Biomedical examples

**All models here are ILLUSTRATIVE, NOT CLINICAL.** The parameter values are
order-of-magnitude illustrations and are not validated patient models. Nothing here may be used
for dosing or device design. The certificates are statements about these equations only.

| Model | What it is | Method | Result |
|---|---|---|---|
| `GlucoseInsulinPI` | linearized Bergman minimal model with PI insulin infusion and a bounded meal | `lmi` | certified |
| `AnesthesiaDepthPKPD` | three-compartment PK and effect site with PI infusion; uncertain clearance and ke0 | `lmi` (polytopic, 4 vertices) | certified |
| `VentilatorPressure` | pressure-controlled ventilation (circuit compliance plus an RC lung) tracking a pressure profile | `lmi` + `tube` | certified |
| `BergmanMinimalModelPI` | the same PI insulin loop on the nonlinear Bergman model, with infusion clipped at zero | `montecarlo`, `falsify` | validation only |

Reproduce, for example:

```
python3 -m dynacert examples/biomedical/GlucoseInsulinPI.mo lmi -q
python3 -m dynacert examples/biomedical/GlucoseInsulinPI.mo montecarlo --n 200 -q
python3 -m dynacert examples/biomedical/GlucoseInsulinPI.mo falsify -q
```

Unless a section says otherwise, Monte Carlo used 200 scenarios and every run used the default
horizon T = 10 (hours for glucose and anesthesia, seconds for the ventilator). Every Monte Carlo
run had **0 violations**, and every falsify worst case is below its certified bound. The ratio
column is falsify worst case ÷ certified bound. Figures are in `figures/<Model>/`.

## GlucoseInsulinPI (certified)

The model is in hours, with deviations from basal: glucose `G` [mg/dL], rescaled remote insulin
action `Xs` [1e-4/min] and plasma insulin `I` [µU/mL]. Insulin infusion above basal is
`u = 60 G + 30 ∫G` [mU/h]. The meal is a glucose appearance rate `|Ra| ≤ 180 mg/dL/h`
(3 mg/dL/min). `X` was rescaled because with the textbook units its coefficients are ~1e-5,
which is badly conditioned for the LMI.

**Claim.** From basal, for every appearance profile within the bound, the glucose deviation stays
within ±155.5 mg/dL.

| Output | Certified | Monte Carlo peak | Falsify worst case | Falsify / certified |
|---|---|---|---|---|
| `G` [mg/dL] | 155.5 | 130.9 | 134.1 | 0.862 |
| `Xs` [1e-4/min] | 499.2 | 403.1 | 419.0 | 0.840 |
| `I` [µU/mL] | 129.2 | 111.1 | 113.7 | 0.880 |
| `xi` [mg/dL·h] | 118.9 | 98.39 | 98.39 | 0.828 |

- **Times:** lmi 62 s, montecarlo 7 s, falsify 20 s.
- **Figures:** `falsify-worstcase-G.png`, `montecarlo-envelope.png`.
- **Caveat:** the linear model lets insulin go below zero (`I ≥ −Ib` is not modelled), which is
  why the nonlinear companion below exists.

## AnesthesiaDepthPKPD (certified, uncertain parameters)

The model is in hours, with deviations from the maintenance steady state: amounts `A1..A3` [mg]
and effect-site concentration `Ce` [µg/mL]. Inter-patient variability makes the elimination rate
uncertain, `k10 ∈ [4.8, 9.6] /h` (0.08–0.16 /min), and likewise `ke0 ∈ [12, 24] /h`. The
disturbance is a pump delivery error `|d_pump| ≤ 30 mg/h` (0.5 mg/min). The controller is PI on
`Ce`.

**Claim.** For every `k10` and `ke0` in range and every pump error within the bound, the
effect-site deviation stays within ±0.301 µg/mL.

| Output | Certified | Monte Carlo peak | Falsify worst case | Falsify / certified |
|---|---|---|---|---|
| `A1` [mg] | 14.30 | 1.176 | 1.928 | 0.135 |
| `A2` [mg] | 4.309 | 0.3488 | 0.3981 | 0.092 |
| `A3` [mg] | 12.32 | 0.1349 | 0.1840 | 0.015 |
| `Ce` [µg/mL] | 0.3009 | 0.02958 | 0.03447 | 0.115 |
| `xi` [µg/mL·h] | 0.01675 | 0.002088 | 0.002088 | 0.125 |

- **Times:** lmi 73 s, montecarlo 8 s, falsify 61 s.
- **Figures:** `falsify-worstcase-Ce.png`, `montecarlo-envelope.png`.
- **Why hours:** in minutes the slow peripheral compartment gives a closed-loop pole at
  −0.0033/min. The lmi search only tries decay rates α ∈ [0.02, 10] per time unit, so it reported
  "no certificate", even for the nominal (certain) model. In hours the pole is at −0.2/h.
- **Conservatism:** the bound is about 10× the worst case (A3 about 70×). One quadratic must work
  at all 4 vertices, and the dynamics span time scales from ~0.2/h to ~50/h. The slow `A3` mode
  also does not reach its peak within the 10 h simulation horizon.

## VentilatorPressure (certified, reference tracking)

The model is in cmH2O, L/s and s. The lung (`R = 20 cmH2O/(L/s)`, `C = 0.05 L/cmH2O`) is filled
through a circuit with compliance `Cc = 0.002 L/cmH2O`. The lung pressure follows a smooth profile
`P_ref → dP_ref → ddP_ref`, where `ddP_ref` is free. The feedforward is computed in the model from
flatness: `Paw_ref = P_ref + RC dP_ref` and blower flow `C dP_ref + Cc dPaw_ref`. The controller
is PI on the circuit-pressure error. The disturbance is a circuit leak `|q_leak| ≤ 0.05 L/s`.

**Claim.** For any such pressure profile and any leak within the bound, the lung pressure stays
within ±0.250 cmH2O of the profile and the circuit pressure within ±1.79 cmH2O of `Paw_ref`.

| Output | Certified | Monte Carlo peak | Falsify worst case | Falsify / certified |
|---|---|---|---|---|
| `e` [cmH2O] | 1.794 | 0.8507 | 0.8520 | 0.475 |
| `el` [cmH2O] | 0.2498 | 0.1465 | 0.1465 | 0.587 |
| `ei` [cmH2O·s] | 0.1357 | 0.1107 | 0.1107 | 0.816 |

- **Tube:** the largest value of zᵀPz/level was 0.81, so every run stayed inside the proved tube.
- **Times:** lmi 26 s, montecarlo 8 s, falsify 22 s, tube 78 s.
- **Figures:** `tube-tube.png`, `falsify-worstcase-e.png`, `montecarlo-phase.png`.
- **Workaround:** `R·C = 1 s` was chosen so that the frame coefficients are integers. With
  `R = 10` the frame has a coefficient of −1/2, and the generated `Cert.lean` failed to compile
  (see the top-level report).

## BergmanMinimalModelPI (validation only)

The same PI controller drives the nonlinear Bergman model, where `dG/dt` contains the bilinear
`−cX·Xs·G`. The total infusion `ub + u` is clipped smoothly at zero:
`(v + √(v² + s²))/2`, with basal `ub = 648 mU/h`. The model is not certifiable by `lmi` because of
the bilinear term and the clip. Monte Carlo used 300 scenarios.

| Output | Monte Carlo peak | Falsify worst case | Linear certificate (GlucoseInsulinPI) |
|---|---|---|---|
| `eG` [mg/dL] | 149.9 | 152.4 | 155.5 |

- **Times:** montecarlo 11 s, falsify 44 s.
- **Figures:** `falsify-worstcase-eG.png`, `montecarlo-envelope.png`, `montecarlo-exceedance.png`.
- **Finding:** the first version did **not** clip the infusion. Falsify then found a destabilizing
  scenario with `|G − Gb| ≈ 703 mg/dL` within 10 h (Monte Carlo found 560). The PI commanded
  negative insulin, `Xs` went far below zero, and `−cX·Xs·G` became exponential glucose growth.
  With the physical clip, the worst case found (152.4) is just under the linear certificate's
  155.5. That is evidence only: the linear certificate does not cover the nonlinear model.
