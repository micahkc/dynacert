# Precision mechatronics and semiconductor examples

All parameters are illustrative, not from a specific drive or tool.

| Model | What it is | Method | Result |
|---|---|---|---|
| `HardDiskTrackFollow` | HDD voice-coil track following: rigid body plus a 5 kHz suspension mode, PID, runout and windage | `lmi` | certified |
| `WaferStageScan` | wafer stage scanning a reference on an isolated metrology frame excited by floor vibration | `lmi` + `tube` | certified |

Reproduce, for example:

```
python3 -m dynacert examples/precision/WaferStageScan.mo lmi -q
python3 -m dynacert examples/precision/WaferStageScan.mo montecarlo --n 200 -q
python3 -m dynacert examples/precision/WaferStageScan.mo falsify -q
python3 -m dynacert examples/precision/WaferStageScan.mo tube -q
```

Monte Carlo used 200 scenarios, and every run used the default horizon T = 10 (ms for the HDD,
s for the wafer stage). Every Monte Carlo run had **0 violations**, and every falsify worst case
is below its certified bound. The ratio column is falsify worst case ÷ certified bound. Figures
are in `figures/<Model>/`.

## HardDiskTrackFollow (certified)

Units are nm and ms (1 nm/ms² = 1 mm/s²). The rigid-body head (`y`, `v`) plus one suspension
mode (`q`, `qd`; 31.4 rad/ms, ζ = 0.02, modal gain 0.3) is under PID on the measured position
`y + q`. Repeatable runout (120 Hz, ~100 nm) is modelled conservatively as any relative
acceleration `|a_ro| ≤ Aω² = 57 nm/ms²`. Windage and flex-cable bias add `|a_w| ≤ 20 nm/ms²`.

**Claim.** From on-track at rest, the head stays within ±5.89 nm of the track centre for every
admissible runout and windage.

| Output | Certified | Monte Carlo peak | Falsify worst case | Falsify / certified |
|---|---|---|---|---|
| `y` [nm] | 5.889 | 4.581 | 4.672 | 0.793 |
| `v` [nm/ms] | 18.75 | 15.29 | 16.15 | 0.862 |
| `q` [nm] | 0.09085 | 0.04113 | 0.07669 | 0.844 |
| `qd` [nm/ms] | 2.422 | 0.7638 | 2.162 | 0.893 |
| `xi` [nm·ms] | 3.883 | 2.852 | 2.852 | 0.734 |

- **Times:** lmi 58 s, montecarlo 11 s, falsify 40 s.
- **Figures:** `falsify-worstcase-y.png` (a bang-bang runout acceleration with one switch at
  t ≈ 7.4 ms), `montecarlo-envelope.png`.
- **Note:** the bounded-acceleration model of runout covers any runout with that acceleration
  bound, including the sinusoid, so it is conservative for a pure sinusoid.

## WaferStageScan (certified, reference tracking)

Units are µm and s. A 20 kg stage carries PID plus acceleration feedforward `m a_ref`, with poles
at a triple −300 rad/s. It is measured relative to a metrology frame on a 5 Hz, ζ = 0.3
isolation. Floor acceleration is bounded by `|a_floor| ≤ 2000 µm/s²` and motor ripple and cable
force by `|F_rip| ≤ 0.2 N`.

**Claim.** For every scan reference with `x_ref' = v_ref` and `v_ref' = a_ref`, and every
admissible floor vibration and force ripple, the stage error relative to the frame stays within
±0.337 µm and the frame motion within ±5.61 µm.

| Output | Certified | Monte Carlo peak | Falsify worst case | Falsify / certified |
|---|---|---|---|---|
| `q` [µm] | 5.610 | 3.546 | 4.432 | 0.790 |
| `qd` [µm/s] | 172.2 | 85.70 | 135.9 | 0.789 |
| `e` [µm] | 0.3371 | 0.05635 | 0.06603 | 0.196 |
| `ev` [µm/s] | 172.1 | 5.811 | 15.54 | 0.090 |
| `ei` [µm] | 0.5973 | 0.1531 | 0.1647 | 0.276 |

- **Tube:** the largest value of zᵀPz/level was 0.714, so every run stayed inside the proved
  tube.
- **Times:** lmi 60 s, montecarlo 14 s, falsify 64 s, tube 153 s.
- **Figures:** `tube-tube.png`, `falsify-worstcase-e.png`, `montecarlo-phase.png`.
- **Workaround (conditioning):** the integrator is scaled, `der(xi) = wi·e` with
  `wi = 300 rad/s`. With the textbook `der(xi) = e` the A matrix has entries up to 2.7e7, and
  the lmi search reported "no certificate" even though the loop is identical.
- **Conservatism:** the bound on the stage error is about 5× the worst case, and the bound on
  `ev` about 11×. One ellipsoid covers both the slow isolation mode (decay 9.4/s) and the fast
  servo (300/s), and α is capped at 10 per time unit. The bound on `ev` equals the bound on `qd`,
  which suggests the ellipsoid is shaped by the frame states.
