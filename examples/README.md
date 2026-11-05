# Examples

42 models: 34 certified, 8 validation only.

Annotated Modelica models from twelve industries. A *certified* model has a Lean-checked
theorem in `certs/Certs/<Model>/` (bounds below are the kept certified bounds). A
*validation only* model is nonlinear: `montecarlo` and `falsify` run on it, but no
certificate method applies yet. Parameter values are illustrative. Each industry README has the
claims in words, Monte Carlo and worst-case results, tightness, and run times.

```
dynacert examples/automotive/QuarterCarSuspension.mo            # what applies, and why
dynacert examples/automotive/QuarterCarSuspension.mo certify    # Lean certificate
dynacert examples/automotive/QuarterCarSuspension.mo validate   # Monte Carlo + worst-case search
dynacert timings                                               # run times of everything run so far
```


## [Automotive](automotive/README.md)

| Model | Status | Certified bounds |
|---|---|---|
| [`AdaptiveCruiseGap`](automotive/AdaptiveCruiseGap.mo) | certified (lmi) | \|e\| ≤ 3.203, \|dv\| ≤ 3.433, \|a_ego\| ≤ 2.951 |
| [`LaneKeepingLateral`](automotive/LaneKeepingLateral.mo) | certified (lmi) | \|e_y\| ≤ 0.2564, \|e_psi\| ≤ 0.03675 |
| [`QuarterCarSuspension`](automotive/QuarterCarSuspension.mo) | certified (lmi) | \|susp_defl\| ≤ 0.08267, \|tire_defl\| ≤ 0.01825 |

## [Aerospace](aerospace/README.md)

| Model | Status | Certified bounds |
|---|---|---|
| [`AircraftPitchShortPeriod`](aerospace/AircraftPitchShortPeriod.mo) | certified (lmi) | \|alpha\| ≤ 0.03407, \|q\| ≤ 0.04141, \|theta\| ≤ 0.01303, \|de\| ≤ 0.0361 |
| [`QuadcopterAltitude`](aerospace/QuadcopterAltitude.mo) | certified (lmi) | \|xi\| ≤ 0.6065, \|e_z\| ≤ 0.3201, \|e_w\| ≤ 0.657 |
| [`RollAutopilot`](aerospace/RollAutopilot.mo) | certified (lmi) | \|phi\| ≤ 0.04456, \|p\| ≤ 0.1878, \|da\| ≤ 0.1193 |
| [`SatelliteAttitudeFlexible`](aerospace/SatelliteAttitudeFlexible.mo) | certified (lmi) | \|th_hub\| ≤ 0.002886, \|w_hub\| ≤ 0.002034, \|twist\| ≤ 0.001875 |

## [Marine](marine/README.md)

| Model | Status | Certified bounds |
|---|---|---|
| [`DynamicPositioningSurge`](marine/DynamicPositioningSurge.mo) | certified (lmi) | \|x\| ≤ 0.9692, \|u\| ≤ 0.1672, \|xi\| ≤ 27.22 |
| [`ShipHeadingNomoto`](marine/ShipHeadingNomoto.mo) | certified (lmi) | \|xi\| ≤ 0.4172, \|e_psi\| ≤ 0.01812, \|e_r\| ≤ 0.001933 |
| [`ShipHeadingNorrbin`](marine/ShipHeadingNorrbin.mo) | validation only | — |

## [Rail](rail/README.md)

| Model | Status | Certified bounds |
|---|---|---|
| [`TrainCouplerForce`](rail/TrainCouplerForce.mo) | certified (lmi) | \|dv_loco\| ≤ 0.4026, \|s\| ≤ 0.06081, \|F_c\| ≤ 305.2 |
| [`TrainSpeedDavis`](rail/TrainSpeedDavis.mo) | validation only | — |
| [`TrainSpeedGrade`](rail/TrainSpeedGrade.mo) | certified (lmi) | \|xi\| ≤ 12.82, \|e_x\| ≤ 1.659, \|e_v\| ≤ 0.5478 |

## [Energy and power](energy/README.md)

| Model | Status | Certified bounds |
|---|---|---|
| [`BatteryPackThermalFan`](energy/BatteryPackThermalFan.mo) | certified (lmi) | \|dTc\| ≤ 2.221, \|dfan\| ≤ 50.64 |
| [`BuckConverterPI`](energy/BuckConverterPI.mo) | certified (lmi) | \|z\| ≤ 0.1312, \|e\| ≤ 0.761, \|ei\| ≤ 5.391 |
| [`GridFrequencyDroopAGC`](energy/GridFrequencyDroopAGC.mo) | certified (lmi) | \|df\| ≤ 0.01396, \|dPm\| ≤ 0.1894, \|dPc\| ≤ 0.1561 |
| [`TwoAreaTieLineLFC`](energy/TwoAreaTieLineLFC.mo) | certified (lmi) | \|df1\| ≤ 0.02411, \|df2\| ≤ 0.02723, \|dPtie\| ≤ 0.1029 |
| [`WindTurbinePitchPI`](energy/WindTurbinePitchPI.mo) | certified (lmi) | \|dw\| ≤ 0.07612, \|dtheta\| ≤ 3.868 |

## [Process and chemical](process/README.md)

| Model | Status | Certified bounds |
|---|---|---|
| [`CSTRArrheniusPI`](process/CSTRArrheniusPI.mo) | validation only | — |
| [`CSTRTemperatureLinearized`](process/CSTRTemperatureLinearized.mo) | certified (lmi) | \|dCa\| ≤ 0.2056, \|dT\| ≤ 3.474, \|dTc\| ≤ 7.222 |
| [`HeatExchangerOutletPI`](process/HeatExchangerOutletPI.mo) | certified (lmi) | \|dT\| ≤ 4.13, \|dTh\| ≤ 5.731 |

## [Buildings and HVAC](buildings/README.md)

| Model | Status | Certified bounds |
|---|---|---|
| [`ChilledWaterSupplyPI`](buildings/ChilledWaterSupplyPI.mo) | certified (lmi) | \|dTs\| ≤ 0.4256, \|dTr\| ≤ 1.056, \|dQch\| ≤ 230.8 |
| [`RoomThermalPI`](buildings/RoomThermalPI.mo) | certified (lmi) | \|dTa\| ≤ 0.4522, \|dQ\| ≤ 4.231 |
| [`RoomThermalSaturatedPI`](buildings/RoomThermalSaturatedPI.mo) | validation only | — |

## [Water](water/README.md)

| Model | Status | Certified bounds |
|---|---|---|
| [`CanalPoolLevelPI`](water/CanalPoolLevelPI.mo) | certified (lmi) | \|dy\| ≤ 0.287, \|dqc\| ≤ 47.6 |
| [`TwoTankLevelLinearized`](water/TwoTankLevelLinearized.mo) | certified (lmi) | \|dh1\| ≤ 0.3827, \|dh2\| ≤ 0.2062, \|dqp\| ≤ 0.2037 |
| [`TwoTankLevelNonlinear`](water/TwoTankLevelNonlinear.mo) | validation only | — |
| [`WaterTowerPressurePI`](water/WaterTowerPressurePI.mo) | certified (lmi) | \|dn\| ≤ 38.99, \|dp\| ≤ 9.105 |

## [Robotics and manufacturing](robotics/README.md)

| Model | Status | Certified bounds |
|---|---|---|
| [`CNCFeedAxis`](robotics/CNCFeedAxis.mo) | certified (lmi) | \|e\| ≤ 0.3158, \|ev\| ≤ 41.41, \|ei\| ≤ 0.00578 |
| [`CartPoleLQR`](robotics/CartPoleLQR.mo) | validation only | — |
| [`FlexibleJointServo`](robotics/FlexibleJointServo.mo) | certified (lmi) | \|e_l\| ≤ 0.05879, \|ev_l\| ≤ 0.4643, \|e_s\| ≤ 4.817, \|ev_s\| ≤ 103.8 |
| [`GantryPayload`](robotics/GantryPayload.mo) | certified (lmi) | \|x\| ≤ 0.005147, \|v\| ≤ 0.0575, \|xi\| ≤ 0.001365 |
| [`WebTensionControl`](robotics/WebTensionControl.mo) | certified (lmi) | \|T\| ≤ 4.045, \|v_f\| ≤ 0.03349, \|xi\| ≤ 0.2878 |

## [Biomedical (illustrative, not clinical)](biomedical/README.md)

| Model | Status | Certified bounds |
|---|---|---|
| [`AnesthesiaDepthPKPD`](biomedical/AnesthesiaDepthPKPD.mo) | certified (lmi) | \|A1\| ≤ 14.3, \|A2\| ≤ 4.309, \|A3\| ≤ 12.32, \|Ce\| ≤ 0.3009, \|xi\| ≤ 0.01675 |
| [`BergmanMinimalModelPI`](biomedical/BergmanMinimalModelPI.mo) | validation only | — |
| [`GlucoseInsulinPI`](biomedical/GlucoseInsulinPI.mo) | certified (lmi) | \|G\| ≤ 155.5, \|Xs\| ≤ 499.2, \|I\| ≤ 129.2, \|xi\| ≤ 118.9 |
| [`VentilatorPressure`](biomedical/VentilatorPressure.mo) | certified (lmi) | \|e\| ≤ 1.794, \|el\| ≤ 0.2498, \|ei\| ≤ 0.1357 |

## [Precision mechatronics](precision/README.md)

| Model | Status | Certified bounds |
|---|---|---|
| [`HardDiskTrackFollow`](precision/HardDiskTrackFollow.mo) | certified (lmi) | \|y\| ≤ 5.889, \|v\| ≤ 18.75, \|q\| ≤ 0.09085, \|qd\| ≤ 2.422, \|xi\| ≤ 3.883 |
| [`WaferStageScan`](precision/WaferStageScan.mo) | certified (lmi) | \|q\| ≤ 5.61, \|qd\| ≤ 172.1, \|e\| ≤ 0.3371, \|ev\| ≤ 172.1, \|ei\| ≤ 0.5973 |

## [Agriculture](agriculture/README.md)

| Model | Status | Certified bounds |
|---|---|---|
| [`GreenhouseClimate`](agriculture/GreenhouseClimate.mo) | certified (lmi) | \|Ta\| ≤ 16.9, \|Ts\| ≤ 3.537, \|xi\| ≤ 2.297 |
| [`GreenhouseVentilation`](agriculture/GreenhouseVentilation.mo) | validation only | — |
| [`IrrigationSoilMoisture`](agriculture/IrrigationSoilMoisture.mo) | certified (lmi) | \|th1\| ≤ 1.209, \|th2\| ≤ 2.14, \|w\| ≤ 4.573, \|xi\| ≤ 1.917 |

[capabilities/](capabilities/README.md) has more models, organized by capability rather than industry.

The original examples (`ClosedLoop*.mo`, `PendulumPD.mo`, `TwoMassLayered.mo`,
`QuadrotorTracking.mo`, `SpacecraftTracking.mo`) are in this directory; see the top-level README.
