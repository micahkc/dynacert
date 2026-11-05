# HVAC and building examples

All parameters are illustrative, sized roughly for a single office (room) and a mid-size
chilled-water plant. They are not taken from a particular building.

| Model | What it is | Kind |
|---|---|---|
| `RoomThermalPI` | Two-node RC room model (air, envelope) with PI heating. The outdoor temperature is the disturbance, and the air capacitance is uncertain | certified (polytopic) |
| `RoomThermalSaturatedPI` | The same room in absolute °C, with a 0–11 kW heater limit and back-calculation anti-windup | validation only (nonlinear) |
| `ChilledWaterSupplyPI` | Chiller evaporator and distribution-loop thermal nodes, chiller capacity lag, PI on supply temperature. The building load is the disturbance | certified (LTI) |

Column meanings are as in [../energy/README.md](../energy/README.md). Times are in seconds,
for `lmi` / `montecarlo` / `falsify`.

### RoomThermalPI (uncertain parameter)

Time is in hours, heat in kW and capacitance in kWh/K. The air-node capacitance `Ca` (air,
furniture, occupancy) lies between 0.5 and 1.5 kWh/K. `Ca` enters the dynamics as `1/Ca`, and
dynacert needs the state matrix to be affine in each uncertain parameter. The model therefore
declares the inverse capacitance `invCa ∈ [0.6667, 2.0]` as the uncertain parameter. Declaring
`Ca` itself as uncertain is rejected at assessment with
`A depends non-polynomially on uncertain parameters (-6/Ca)`.

For any outdoor-temperature deviation `|dTo| ≤ 10 K` and every `Ca` in the range:

| Output | Certified | MC (T = 48 h) | Falsify | Ratio |
|---|---|---|---|---|
| `dTa` room temperature [K] | 0.45225 | 0.36340 | 0.36340 | 0.80 |
| `dQ` heater power deviation [kW] | 4.2307 | 4.0000 | 4.0000 | 0.95 |

Times: 26 / 5 / 50 s. The worst `dQ` is the steady-state value `10 K / (Rae + Reo) = 4 kW`.

The heater power `dQ` is written out inside the air-node equation rather than referenced
there. With `der(dTa) = invCa*((dTe - dTa)/Rae + dQ)` the generated link proof fails (see
"Issues").

### RoomThermalSaturatedPI (validation only)

The heater total `Q = min(max(Q0 − kp·e − ki·z, 0), Qmax)` with `Qmax = 11 kW` cannot supply
the 12 kW that a 10 K cold snap needs. `lmi` does not apply because `der(Ta)` and `der(z)` are
nonlinear (piecewise) in `Ta, z`:

| Output | MC (300, T = 48 h) | Falsify |
|---|---|---|
| `e = Ta − Tsp` [K] | 2.2789 | 2.2789 |

Times: montecarlo 8 s, falsify 172 s. The envelope is still falling at 48 h. The steady-state
shortfall is 1 kW × (Rae + Reo) = 2.5 K, so a longer horizon would find a larger error. The
unsaturated loop is certified to stay within
0.45 K (`RoomThermalPI`). Saturation lets the room drift 2.3 K below setpoint. This is a
useful demonstration that the linear certificate says nothing about the saturated plant.

Conditional anti-windup written as `der(z) = if Qcmd > Qmax and e < 0 then 0 else e` is
rejected by rumoca's `lean-dae` target, which has no event support. Every approach then
fails, including Monte Carlo. The model uses smooth back-calculation through `min`/`max`
instead.

### ChilledWaterSupplyPI

Time is in minutes and heat in kW. For any building cooling-load deviation
`|dQload| ≤ 200 kW`:

| Output | Certified | MC (T = 60 min) | Falsify | Ratio |
|---|---|---|---|---|
| `dTs` supply temperature [K] | 0.42563 | 0.38935 | 0.38955 | 0.92 |
| `dTr` return temperature [K] | 1.0558 | 1.0045 | 1.0045 | 0.95 |
| `dQch` chiller capacity [kW] | 230.82 | 200.70 | 200.70 | 0.87 |

Times: 29 / 6 / 82 s.

## Figures

`figures/<Model>/` holds the Monte Carlo envelope and a falsify worst case (certified
models), or the envelope and exceedance plots (`RoomThermalSaturatedPI`).

## Reproduce

```
dynacert examples/buildings/RoomThermalPI.mo lmi
dynacert examples/buildings/RoomThermalPI.mo montecarlo --n 200 --T 48
dynacert examples/buildings/RoomThermalPI.mo falsify --T 48
dynacert examples/buildings/RoomThermalSaturatedPI.mo montecarlo --n 300 --T 48
dynacert examples/buildings/ChilledWaterSupplyPI.mo lmi          # then --T 60
```

## Issues found while building these

- **Lean link proof failure with an uncertain parameter multiplying an algebraic variable.**
  The original equation was `der(dTa) = invCa*((dTe - dTa)/Rae + dQ)` with
  `dQ = -kp*dTa - ki*z`. Running `dynacert examples/buildings/RoomThermalPI.mo lmi -q` gave
  `Cert.lean:96:6: ring failed, ring expressions not equal`. The generated step is
  `linear_combination (1 : ℝ) * e2`, but it needs `e2 + p.invCa * e0`: the substitution of the
  `dQ` equation has to be scaled by the uncertain parameter. Inlining `dQ` works around it.
- **`if` expressions block every approach.** rumoca's `lean-dae` target rejects event
  partitions (`unsupported-feature:events`). dynacert stops with `rumoca failed (lean_dae)` even
  for `montecarlo`, which does not need the Lean export.
