# Agriculture examples

All parameters are illustrative, not from a specific greenhouse, soil or crop.

| Model | What it is | Method | Result |
|---|---|---|---|
| `GreenhouseClimate` | greenhouse air and soil temperature, PI on combined heating and ventilation cooling, uncertain air-to-soil coupling | `lmi` (polytopic) | certified |
| `IrrigationSoilMoisture` | two-layer soil moisture with a lagged irrigation actuator, PI, uncertain drainage | `lmi` (polytopic) | certified |
| `GreenhouseVentilation` | greenhouse with physical, bilinear ventilation heat removal `Kv·(Ta − To)` | `montecarlo`, `falsify` | validation only |

Reproduce, for example:

```
python3 -m dynacert examples/agriculture/IrrigationSoilMoisture.mo lmi -q
python3 -m dynacert examples/agriculture/IrrigationSoilMoisture.mo montecarlo --n 200 -q
python3 -m dynacert examples/agriculture/IrrigationSoilMoisture.mo falsify -q
```

Unless a section says otherwise, Monte Carlo used 200 scenarios and every run used the default
horizon T = 10 (hours for the greenhouse, days for irrigation). Every Monte Carlo run had
**0 violations**, and every falsify worst case is below its certified bound. The ratio column is
falsify worst case ÷ certified bound. Figures are in `figures/<Model>/`.

## GreenhouseClimate (certified, uncertain parameter)

The model is in hours, kWh, kW and K, as deviations from the operating point. Air
(`Ca = 1.33 kWh/K`) loses heat through the cover (`UA = 9 kW/K`) and exchanges heat with soil and
structure (`Cs = 20 kWh/K`) through `h ∈ [3, 7] kW/K`, which is uncertain because it depends on
canopy and soil moisture. The controller is PI on air temperature, where negative output means
ventilation cooling. The disturbances are outside temperature `|To| ≤ 5 K` and absorbed solar
power `|Qsun| ≤ 60 kW`.

**Claim.** For every `h ∈ [3, 7]` and every outside-temperature and solar profile within the
bounds, the air temperature stays within ±16.9 K of the set point.

| Output | Certified | Monte Carlo peak | Falsify worst case | Falsify / certified |
|---|---|---|---|---|
| `Ta` [K] | 16.90 | 3.603 | 3.660 | 0.217 |
| `Ts` [K] | 3.537 | 0.4161 | 0.5816 | 0.164 |
| `xi` [K·h] | 2.297 | 1.313 | 1.336 | 0.582 |

- **Times:** lmi 48 s, montecarlo 11 s, falsify 27 s.
- **Figures:** `falsify-worstcase-Ta.png`, `montecarlo-envelope.png`.
- **Conservatism:** the bound is about 4.6× the worst case. The air dynamics are fast (~40/h)
  while the soil is slow (~0.25/h), and one quadratic must hold at both vertices of `h`. The
  falsify worst cases for `Ts` and `xi` peak at the end of the 10 h horizon, so the true supremum
  may be somewhat larger.

## IrrigationSoilMoisture (certified, uncertain parameter)

The model is in days, mm and volumetric %. A 300 mm root zone sits over a 600 mm subsoil.
Irrigation is delivered through a 0.25-day first-order lag. Root-zone drainage
`kperc ∈ [1, 3] mm/day per %` is uncertain because it depends on soil texture. The disturbance is
an evapotranspiration forecast error `|dET| ≤ 3 mm/day`. The controller is PI on root-zone
moisture.

**Claim.** For every drainage coefficient in range and every ET error within the bound,
root-zone moisture stays within ±1.21 % of target and subsoil moisture within ±2.14 %.

| Output | Certified | Monte Carlo peak | Falsify worst case | Falsify / certified |
|---|---|---|---|---|
| `th1` [%] | 1.209 | 0.9611 | 0.9851 | 0.815 |
| `th2` [%] | 2.140 | 0.4634 | 0.5758 | 0.269 |
| `w` [mm/day] | 4.573 | 3.154 | 3.154 | 0.690 |
| `xi` [%·day] | 1.917 | 1.488 | 1.513 | 0.789 |

- **Times:** lmi 53 s, montecarlo 7 s, falsify 28 s.
- **Figures:** `falsify-worstcase-th1.png`, `montecarlo-envelope.png`.
- **Horizon:** several worst cases peak at t = 10 days, so the 10-day horizon may truncate the
  slow subsoil response.

## GreenhouseVentilation (validation only)

This is the same greenhouse in absolute °C, but ventilation heat removal is `Kv·(Ta − To)`, with
the vent conductance `Kv = Kv0 + kv·(Ta − Tset)` opened in proportion to the error. A heater PI
regulates `Ta`. The model is not certifiable by `lmi` because `Kv·(Ta − To)` is bilinear (state ×
state and state × disturbance). Monte Carlo used 300 scenarios.

| Output | Monte Carlo peak | Falsify worst case |
|---|---|---|
| `e = Ta − Tset` [K] | 3.228 | 3.713 |

- **Times:** montecarlo 23 s, falsify 64 s.
- **Figures:** `falsify-worstcase-e.png`, `montecarlo-envelope.png`, `montecarlo-exceedance.png`.
- **Result:** the worst case found (3.71 K) is close to that of the linear `GreenhouseClimate`
  model (3.66 K), which suggests that the linearization is reasonable over this disturbance range.
  `Kv` is not clipped at zero in this model.
