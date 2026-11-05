# Water examples

All parameters are illustrative: a laboratory-scale two-tank rig, a medium irrigation canal
pool, and a small municipal pressure zone.

| Model | What it is | Kind |
|---|---|---|
| `TwoTankLevelLinearized` | Two gravity-drained tanks in series, with PI pump control of the lower level. Linearized Torricelli outflows; an unmeasured inflow is the disturbance | certified (LTI) |
| `TwoTankLevelNonlinear` | The same rig with `q = a·sqrt(2gh)` outflows | validation only (nonlinear) |
| `CanalPoolLevelPI` | Irrigation canal pool, distant-downstream PI level control. Integrator-delay model with a first-order Padé delay; an offtake is the disturbance | certified (LTI) |
| `WaterTowerPressurePI` | Elevated tank fed by a variable-speed pump (linearized pump curve), PI on zone pressure. Zone demand is the disturbance | certified (LTI) |

Column meanings are as in [../energy/README.md](../energy/README.md). Times are in seconds,
for `lmi` / `montecarlo` / `falsify`.

### TwoTankLevelLinearized

The operating point is `h1 = 0.8 m`, `h2 = 0.9877 m`, `q0 = 0.4754 m³/min`. The outflow
sensitivities are `q0/(2h)`, and time is in minutes. For any unmeasured inflow
`|dqd| ≤ 0.1 m³/min`:

| Output | Certified | MC (T = 30 min) | Falsify | Ratio |
|---|---|---|---|---|
| `dh1` upper level [m] | 0.38266 | 0.33730 | 0.33813 | 0.88 |
| `dh2` lower level [m] | 0.20621 | 0.17215 | 0.17812 | 0.86 |
| `dqp` pump flow [m³/min] | 0.20372 | 0.17970 | 0.17977 | 0.88 |

Times: 35 / 6 / 34 s.

### TwoTankLevelNonlinear (validation only)

`lmi` does not apply because the dynamics are nonlinear in `h1`, `h2` (square-root outflows):

| Output | MC (300, T = 30 min) | Falsify |
|---|---|---|
| `e = h2 − h2sp` [m] | 0.17223 | 0.17844 |

Times: montecarlo 9 s, falsify 57 s. The nonlinear worst case (0.1784 m) is very close to the
linearized one (0.1781 m) and below the linear certificate (0.2062 m). That supports the
linearization at this disturbance size but proves nothing about the nonlinear model.

### CanalPoolLevelPI

Time is in minutes and flows in m³/min. The pool surface is 6000 m² and the transport delay
8 min. For any unscheduled offtake `|dqoff| ≤ 30 m³/min` (0.5 m³/s):

| Output | Certified | MC (T = 200 min) | Falsify | Ratio |
|---|---|---|---|---|
| `dy` downstream level [m] | 0.28698 | 0.19213 | 0.19220 | 0.67 |
| `dqc` gate flow command [m³/min] | 47.597 | 39.514 | 39.733 | 0.83 |

Times: 33 / 6 / 104 s. The Padé approximation is part of the model, so the claim is about
the Padé pool model, not a true delay.

### WaterTowerPressurePI

Time is in minutes. For any demand deviation `|dqdem| ≤ 5 m³/min`:

| Output | Certified | MC (T = 200 min) | Falsify | Ratio |
|---|---|---|---|---|
| `dp` zone pressure [kPa] | 9.1052 | 7.5813 | 7.9867 | 0.88 |
| `dn` pump speed [%] | 38.989 | 32.291 | 32.783 | 0.84 |

Times: 25 / 6 / 110 s.

## Figures

`figures/<Model>/` holds the Monte Carlo envelope and a falsify worst case (certified
models), or the envelope and exceedance plots (`TwoTankLevelNonlinear`).

## Reproduce

```
dynacert examples/water/TwoTankLevelLinearized.mo lmi
dynacert examples/water/TwoTankLevelLinearized.mo montecarlo --n 200 --T 30
dynacert examples/water/TwoTankLevelLinearized.mo falsify --T 30
dynacert examples/water/TwoTankLevelNonlinear.mo montecarlo --n 300 --T 30
dynacert examples/water/CanalPoolLevelPI.mo lmi                  # then --T 200
dynacert examples/water/WaterTowerPressurePI.mo lmi              # then --T 200
```

The canal and water-tower loops settle over hours. The "simulated peak" that `lmi` prints
uses a fixed 10-unit horizon, so it reports 0.013 m for the canal level against a 0.19 m
worst case at `T = 200`.
