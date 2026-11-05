# Energy / power-system examples

Closed loops from power systems and power electronics. All parameters are illustrative. They
have plausible magnitudes but are not taken from any particular plant. Each model is written
in deviation variables around an operating point, except `BuckConverterPI`, which tracks a
declared reference trajectory.

| Model | What it is | Kind |
|---|---|---|
| `GridFrequencyDroopAGC` | One-area load-frequency control: swing equation, governor-turbine with 5 % droop, integral AGC | certified (LTI) |
| `TwoAreaTieLineLFC` | Two areas joined by a tie line, each with droop and AGC on its own ACE (7 states, 2 disturbances) | certified (LTI) |
| `BuckConverterPI` | Averaged buck converter, PI voltage loop with an inner P current loop, tracking a soft-start reference | certified (LTI, reference) + tube |
| `WindTurbinePitchPI` | Above-rated rotor-speed regulation by collective pitch, linearized, with an uncertain pitch sensitivity | certified (polytopic) |
| `BatteryPackThermalFan` | Two-node pack thermal model (cells, air) with a PI-driven cooling fan | certified (LTI) |

## Claims and results

"Certified" is the Lean-checked bound `<Model>.Cert.certified`. It holds for all time, for
every admissible disturbance (each disturbance is bounded componentwise by the value in the
model), and for every value of each uncertain parameter in its range. "MC" is the largest peak
over 200 i.i.d. Monte Carlo scenarios (`montecarlo --n 200`). "Falsify" is the worst case
found by `falsify` (adjoint and switching-time search plus collocation). Both MC and falsify
are lower bounds on the true worst case over the finite horizon `T`. "Ratio" is falsify
divided by certified: the true worst case lies between the falsify value and the certified
bound. Times are wall-clock seconds for `lmi` (search, Lean build and kernel check) / `montecarlo` / `falsify`.

### GridFrequencyDroopAGC

For any load step or load fluctuation with `|dPL(t)| ≤ 0.1 pu`, starting from the scheduled
operating point:

| Output | Certified | MC (T = 30 s) | Falsify | Ratio |
|---|---|---|---|---|
| `df` frequency deviation [pu] | 0.013956 | 0.011551 | 0.011552 | 0.83 |
| `dPm` mechanical power [pu] | 0.18942 | 0.16290 | 0.16529 | 0.87 |
| `dPc` AGC setpoint [pu] | 0.15605 | 0.10000 | 0.10000 | 0.64 |

Times: 68 / 11 / 37 s. At 50 Hz the frequency bound is ±0.70 Hz. The worst `dPc` is the
steady-state value `0.1 pu`, because AGC restores the full load, so the quadratic certificate is
looser for this output.

### TwoAreaTieLineLFC

For any load changes with `|dPL1|, |dPL2| ≤ 0.1 pu`:

| Output | Certified | MC (T = 30 s) | Falsify | Ratio |
|---|---|---|---|---|
| `df1` [pu] | 0.024108 | 0.012651 | 0.013607 | 0.56 |
| `df2` [pu] | 0.027235 | 0.015184 | 0.016885 | 0.62 |
| `dPtie` tie-line flow [pu] | 0.10287 | 0.052221 | 0.063607 | 0.62 |

Times: 56 / 15 / 60 s. The worst cases found by falsify still peak at the end of the
30 s horizon (collocation `t* ≈ 30`). They are resonant, switching disturbances that excite
the lightly damped inter-area mode, so a longer horizon would raise the ratio. The
certificate is a single ellipsoid in 7 dimensions, which is the main source of the
conservatism.

### BuckConverterPI (reference tracking)

The output voltage follows any reference `v_ref` with `v_ref' = dv_ref`, `dv_ref' = ddv_ref`
starting from rest at 0 V (for example a soft-start ramp to 5 V). The inductor-current and
duty-cycle feedforward is computed in the model from the reference and the nominal 1 Ω load.
For any extra load current with `|i_load(t)| ≤ 2 A`, the tracking errors satisfy:

| Output | Certified | MC (T = 10 ms) | Falsify | Ratio |
|---|---|---|---|---|
| `e = v − v_ref` [V] | 0.76100 | 0.65359 | 0.68465 | 0.90 |
| `ei = i − i_ref` [A] | 5.3912 | 4.6320 | 4.8306 | 0.90 |
| `z` integral of `e` [V·ms] | 0.13116 | 0.10902 | 0.11125 | 0.85 |

Times: 23 / 6 / 21 s. `tube`: 83 s. All 30 runs on a random reference and the adjoint worst
cases stay inside the proved set (`max zᵀPz/level = 0.97`).

The claim is about the averaged, unsaturated converter, because the duty cycle is not clipped
to [0, 1]. Time is in ms, L in mH and C in mF. The first version used C = 470 µF and
R = 2 Ω. Its generated `Cert.lean` did not compile (see "Issues" below). The current values
(C = 1 mF, R = 1 Ω) give the error frame integer coefficients.

### WindTurbinePitchPI (uncertain parameter)

The aerodynamic pitch sensitivity `ktheta ∈ [−1.2, −0.5] MN·m/deg` changes across the
above-rated wind range. The pitch PI gains are fixed, and the certificate is a common quadratic
over both vertices. For any wind-speed deviation `|dv_wind| ≤ 2 m/s` and every `ktheta` in the
range:

| Output | Certified | MC (T = 30 s) | Falsify | Ratio |
|---|---|---|---|---|
| `dw` rotor speed [rad/s] | 0.076123 | 0.060679 | 0.060698 | 0.80 |
| `dtheta` pitch [deg] | 3.8681 | 3.1976 | 3.2042 | 0.83 |

Times: 67 / 8 / 60 s. Monte Carlo samples `ktheta` uniformly. Falsify also searches over it.

### BatteryPackThermalFan

For any cell heat-generation deviation `|dQ| ≤ 100 W` and ambient deviation `|dTamb| ≤ 5 K`:

| Output | Certified | MC (T = 120 min) | Falsify | Ratio |
|---|---|---|---|---|
| `dTc` cell temperature [K] | 2.2210 | 1.8325 | 1.9619 | 0.88 |
| `dfan` fan speed [%] | 50.645 | 44.034 | 44.848 | 0.89 |

Times: 58 / 11 / 88 s. The time unit is minutes.

## Figures

`figures/<Model>/` holds the Monte Carlo envelope (quantile fan chart against the certified
bound) and one falsify worst case (`worstcase-<output>`). For `BuckConverterPI` the second
figure is the proved tube along a random soft-start reference.

## Reproduce

```
dynacert examples/energy/GridFrequencyDroopAGC.mo                 # assessment
dynacert examples/energy/GridFrequencyDroopAGC.mo lmi
dynacert examples/energy/GridFrequencyDroopAGC.mo montecarlo --n 200 --T 30
dynacert examples/energy/GridFrequencyDroopAGC.mo falsify --T 30
dynacert examples/energy/BuckConverterPI.mo tube
```

Horizons used: grid and wind `--T 30`, buck `--T 10` (ms), battery `--T 120` (min). The
default `--T 10` is too short for the slower loops.

## Issues found while building these

- **BuckConverterPI with C = 0.47 mF failed in Lean.** The command was
  `dynacert examples/energy/BuckConverterPI.mo lmi -q`. The error was `Cert.lean:29:4: failed to compile definition,
  consider marking it as 'noncomputable' because it depends on 'Real.instDivInvMonoid'`. The
  generated `def vec` has rational coefficients from the reference feedforward
  (`(-1/2 : ℝ) * v.v_ref + (-47/100 : ℝ) * v.dv_ref`) and is not marked `noncomputable`.
  This was worked around with parameter values that make the coefficients integers.
