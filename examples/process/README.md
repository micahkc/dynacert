# Process and chemical examples

All parameters are illustrative. The CSTR uses textbook-style benchmark numbers for a
first-order exothermic reaction A → B in a cooled, well-mixed reactor.

| Model | What it is | Kind |
|---|---|---|
| `CSTRTemperatureLinearized` | Exothermic CSTR linearized at its operating point, PI on reactor temperature through coolant temperature | certified (LTI) |
| `CSTRArrheniusPI` | The same CSTR with full Arrhenius kinetics `k0·exp(−E/RT)` and the same PI controller | validation only (nonlinear) |
| `HeatExchangerOutletPI` | Lumped heat exchanger with PI outlet-temperature control through a lagged hot-side actuator. UA is uncertain (fouling, ±30 %) | certified (polytopic) |

Column meanings are as in [../energy/README.md](../energy/README.md). Certified bounds are
Lean-checked and hold for all time. MC (200 scenarios; 300 for nonlinear models) and falsify
values are achieved peaks over the horizon `T`, which are lower bounds on the true worst case.
Times are in seconds, for `lmi` / `montecarlo` / `falsify`.

### CSTRTemperatureLinearized

The model is linearized about `Ca = 0.8773 mol/L`, `T = 324.48 K`, `Tc = 300 K`. Its Jacobian
entries are computed from `CSTRArrheniusPI` and rounded to 4 significant figures. Time is in
minutes. The claim holds for any feed-temperature deviation `|dTf| ≤ 5 K` together with any
feed-concentration deviation `|dCaf| ≤ 0.1 mol/L`:

| Output | Certified | MC (T = 20 min) | Falsify | Ratio |
|---|---|---|---|---|
| `dCa` [mol/L] | 0.20558 | 0.097647 | 0.097740 | 0.48 |
| `dT` reactor temperature [K] | 3.4744 | 1.9833 | 2.2199 | 0.64 |
| `dTc` coolant temperature move [K] | 7.2220 | 3.6111 | 3.6171 | 0.50 |

Times: 49 / 12 / 25 s. With two disturbance channels and three outputs the ratios are lower
than in the single-channel examples. The per-channel quadratic bound adds the two channels'
worst cases, but no single disturbance signal realizes both of them at once.

### CSTRArrheniusPI (validation only)

This model is not certifiable by `lmi`, because `der(Ca)` and `der(T)` are nonlinear in
`Ca, T` through the Arrhenius rate. `montecarlo` and `falsify` run on it directly:

| Output | MC (300, T = 20 min) | Falsify |
|---|---|---|
| `e = T − Tsp` [K] | 2.0262 | 2.3314 (adjoint/switch; collocation 2.3313) |

Times: montecarlo 13 s, **falsify 954 s**. Falsify on the nonlinear model runs the adjoint
multistart from the 5 worst Monte Carlo runs and then collocation. This took about 40× longer
than on the linearized model.

The nonlinear worst case (2.33 K) is close to the linearized model's (2.22 K), and below the
linearized certificate (3.47 K). That is evidence, not a proof, that the linearization is
representative for these disturbance sizes. The nonlinear model has no certificate.

### HeatExchangerOutletPI (uncertain parameter)

For any process-inlet temperature deviation `|dTin| ≤ 5 K` and every `UA ∈ [21, 39] kW/K`:

| Output | Certified | MC (T = 120 s) | Falsify | Ratio |
|---|---|---|---|---|
| `dT` outlet temperature [K] | 4.1301 | 2.3308 | 2.5054 | 0.61 |
| `dTh` hot-side temperature [K] | 5.7315 | 4.0174 | 4.3867 | 0.77 |

Times: 26 / 4 / 102 s. The controller is deliberately slow (`ki = 0.05 /s`), so the outlet
deviation reaches about half the inlet step. The ellipsoid covers the whole UA range, which
adds conservatism compared with any single UA.

## Figures

`figures/<Model>/` holds the Monte Carlo envelope and, for the certified models, a falsify
worst case. For `CSTRArrheniusPI` it holds the Monte Carlo envelope and the exceedance
(tail-probability) plot.

## Reproduce

```
dynacert examples/process/CSTRTemperatureLinearized.mo lmi
dynacert examples/process/CSTRTemperatureLinearized.mo montecarlo --n 200 --T 20
dynacert examples/process/CSTRTemperatureLinearized.mo falsify --T 20
dynacert examples/process/CSTRArrheniusPI.mo montecarlo --n 300 --T 20
dynacert examples/process/CSTRArrheniusPI.mo falsify --T 20     # ~16 min
dynacert examples/process/HeatExchangerOutletPI.mo lmi           # then --T 120
```
