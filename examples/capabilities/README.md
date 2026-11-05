# Capability examples

Small models, one per capability, including the ones the industry folders barely cover: arrays,
polytopes, layers, nonlinear methods, funnels, and the cases dynacert refuses. Parameter values are
illustrative. See [docs/capabilities.md](../../docs/capabilities.md) for the full picture.

"Worst found" is the largest peak from `falsify`, or from Monte Carlo (200 runs) when marked MC. It is
a lower bound on the true worst case. Bounds are the Lean-checked kept bounds from 2026-11-02.

## Linear (`lmi`)

| Model | Shows | Certified | Worst found |
|---|---|---|---|
| [`GimbalThreeAxis`](GimbalThreeAxis.mo) | Arrays, coupled matrix, per-axis bounds | \|th[1]\| ≤ 0.0712, \|th[2]\| ≤ 0.0576, \|th[3]\| ≤ 0.0627 | 0.0534, 0.0191, 0.0227 (MC) |
| [`PlotterXYTracking`](PlotterXYTracking.mo) | Array reference chain | \|e[1]\| ≤ 0.0762, \|e[2]\| ≤ 0.0578, \|ev[1]\| ≤ 0.2185, \|ev[2]\| ≤ 0.2207 | 0.0625, 0.0200, 0.1766, 0.0712 |
| [`PayloadLiftUncertain`](PayloadLiftUncertain.mo) | Two uncertain parameters, 4 corners | \|z\| ≤ 0.0708, \|w\| ≤ 0.2115 | 0.0625, 0.1817 |
| [`OvenWarmStartFunnel`](OvenWarmStartFunnel.mo) | Initial box, shrinking funnel | \|T\| ≤ 2.418 | Validators skip the box (see below) |
| [`DockingAllAnnotations`](DockingAllAnnotations.mo) | Reference, disturbance, uncertain parameter and initial box together | \|e\| ≤ 0.1195, \|ev\| ≤ 0.1646 | Validators skip the box (see below) |
| [`MotorCommandOutput`](MotorCommandOutput.mo) | Algebraic certified output | \|w\| ≤ 1.160, \|u\| ≤ 2.321 | 1.047, 2.094 |

## Polytopes (`polyhedral`) and layers (`layered`)

Both are run after `lmi` by the portfolio, which keeps the tighter bound per output.

| Model | Shows | `lmi` | Kept | Worst found |
|---|---|---|---|---|
| [`ReservoirCascadePoly`](ReservoirCascadePoly.mo) | Polytope near the exact peaks (1 and 3) | 1.471, 3.209 | \|h1\| ≤ 1.0002, \|h2\| ≤ 3.0005 | 0.99995, 2.966 |
| [`TrackedPolyhedral`](TrackedPolyhedral.mo) | Polytope in a tracking error frame | 0.1819, 0.3407 | \|e\| ≤ 0.1668, \|ev\| ≤ 0.3012 | 0.1667, 0.2963 |
| [`ThreeZoneRadiant`](ThreeZoneRadiant.mo) | Three layers around a coupling cycle | 1.112, 0.859, 1.104 | \|z1.T\| ≤ 0.7885, \|z2.T\| ≤ 0.4101, \|z3.T\| ≤ 0.7523 | 0.7858, 0.4056, 0.7485 |
| [`TwinDriveShaft`](TwinDriveShaft.mo) | Layers help the lightly disturbed drive | 0.5721, 0.3680 | \|a.th\| ≤ 0.5721 (`lmi`), \|b.th\| ≤ 0.0473 (`layered`) | 0.5029, 0.0381 |

## Switching (`switched`)

| Model | Shows | Certified | Worst found |
|---|---|---|---|
| [`ValveGainTwoSwitches`](ValveGainTwoSwitches.mo) | Two switches, 4 modes | \|x\| ≤ 0.1610, \|v\| ≤ 0.3176 | Validators timed out at 500 s |
| [`GearshiftElseifChain`](GearshiftElseifChain.mo) | `elseif` chain, 3 modes, mode-dependent output | \|w\| ≤ 0.4521, \|u\| ≤ 3.591 | 0.1624, 0.6736 |
| [`SwitchedTrackingFunnel`](SwitchedTrackingFunnel.mo) | Switching with a reference and an initial box | \|xi\| ≤ 0.2537, \|e\| ≤ 0.1219, \|ev\| ≤ 0.1810 | Validators skip the box (see below) |

## Nonlinear (`sector`, `funnel`, `lie`)

| Model | Shows | Certified | Worst found |
|---|---|---|---|
| [`TwinPendulumHold`](TwinPendulumHold.mo) | `sin` atoms, linear coupling | \|th1\| ≤ 0.0704, \|th2\| ≤ 0.0394 | 0.0639, 0.0348 |
| [`PathFollowScheduled`](PathFollowScheduled.mo) | `atan2` and `sin`, scheduled lookahead | \|y\| ≤ 0.0504, \|psi\| ≤ 0.0306 | 0.0491, 0.0274 |
| [`LunarHopperHover`](LunarHopperHover.mo) | All of `sin`, `cos`, `√`, `atan2` | \|ex\| ≤ 0.0335, \|th\| ≤ 0.0446 | 0.0266, 0.0351 |
| [`RobotArmSwingFunnel`](RobotArmSwingFunnel.mo) | Finite-horizon funnel on [0, 2] s (`certify funnel --segments 8`) | \|e\| ≤ 0.0253 | 0.0056 (MC on [0, 2]) |
| [`GeoServicerTracking`](GeoServicerTracking.mo) | SE₂(3) log tube (`lie`) | pos, vel, att errors each ≤ 0.00166 | 0.00077, 0.00101, 0 (MC; falsify timed out) |

## Where dynacert stops, by design

Each is rejected with a named reason. Most have a certifiable twin above.

| Model | What it shows |
|---|---|
| [`UnstablePlantRejected`](UnstablePlantRejected.mo) | Unstable, so no LMI; Monte Carlo shows growth (falsify peak 6.36 at `t = 10`) |
| [`DiodeClampExp`](DiodeClampExp.mo) | `exp` has no atom; validation only (peak 0.991) |
| [`ConstantLookaheadGap`](ConstantLookaheadGap.mo) | `atan2(y, constant)` becomes `atan`, which has no atom |
| [`FeedthroughOutputRejected`](FeedthroughOutputRejected.mo) | Output reads a disturbance directly |
| [`UncertainInputRejected`](UncertainInputRejected.mo) | Uncertain parameter in the input matrix |
| [`EuclideanBallRejected`](EuclideanBallRejected.mo) | `norm = "2"` isn't supported yet |
| [`BouncingBallEvents`](BouncingBallEvents.mo) | `when` / `reinit` rejected by rumoca's export |
| [`QuaternionAttitudeReport`](QuaternionAttitudeReport.mo) | `structure` finds the quaternion form, but no method certifies it; validation only |

## [Known failures](known-failures/)

These look as if they should certify, but hit bugs in the sector and compose emitters. They're kept as
repros, each with the cause in its header. See "Known defects" in
[docs/capabilities.md](../../docs/capabilities.md).

| Model | Failure |
|---|---|
| `InvertedPendulumHold` | `reduced() failed without generators`: no algebraic variables |
| `CraneHoistSwing` | `Unknown identifier hR0`: one region coordinate. `compose`: ADMM failed |
| `TiltedThrustHeave` | Accepted at assessment, then rejected at run time |
| `TwoAxisTiltHeave` | `Type mismatch` in the generated certificate |
| `CraneTwoAxisSwing` | The same `Type mismatch`. `compose`: ADMM failed |

**About the initial-box rows:** the validators don't sample `initialSet` boxes, so their peaks say
nothing about the box and aren't quoted. `view tube` does simulate from the box.

**To reproduce:** `dynacert examples/capabilities/<Model>.mo certify`, with the method named in the
model's header. Build one at a time on a shared machine, as Lean checks peak at several GB.
