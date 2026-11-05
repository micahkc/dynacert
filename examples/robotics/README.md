# Robotics and manufacturing examples

All parameters are illustrative, not taken from a specific machine. Each model is a closed loop
written entirely in Modelica: plant, controller, and any feedforward. Each `.mo` file starts
with a header comment that explains the model.

| Model | What it is | Method | Result |
|---|---|---|---|
| `FlexibleJointServo` | robot joint with an elastic transmission (two-mass), link angle following a smooth reference with flatness feedforward up to snap | `lmi` + `tube` | certified |
| `CNCFeedAxis` | ball-screw feed axis following a tool path under cutting force, PID + model feedforward | `lmi` + `tube` | certified |
| `GantryPayload` | pick-and-place gantry axis settling at the place position with an unknown payload (0–20 kg) and frame vibration | `lmi` (polytopic) | certified |
| `WebTensionControl` | web tension between a leader and a follower roller, PI + speed damping | `lmi` | certified |
| `CartPoleLQR` | nonlinear cart-pole held upright by LQR | `montecarlo`, `falsify` | validation only |

Reproduce, for example:

```
python3 -m dynacert examples/robotics/CNCFeedAxis.mo                     # assessment
python3 -m dynacert examples/robotics/CNCFeedAxis.mo lmi -q              # certificate (Lean)
python3 -m dynacert examples/robotics/CNCFeedAxis.mo montecarlo --n 200 -q
python3 -m dynacert examples/robotics/CNCFeedAxis.mo falsify -q
python3 -m dynacert examples/robotics/CNCFeedAxis.mo tube -q
```

Unless a section says otherwise, Monte Carlo used 200 scenarios and every run used the default
horizon T = 10 (in the model's time unit). Every Monte Carlo run had **0 violations**, and every
falsify worst case is below its certified bound. The ratio column is falsify worst case ÷
certified bound: near 1 the certificate is tight, near 0 it is conservative. Run times are
wall-clock on the development machine. Figures are in `figures/<Model>/`. Certificates are in
`certs/Certs/<Model>/`.

## FlexibleJointServo (certified, reference tracking)

The motor drives the link through a spring `k = 200 N·m/rad` (`Jm = 0.05`, `Jl = 1 kg·m²`). The link
follows the reference chain `q_ref → w_ref → a_ref → j_ref → s_ref`, where the snap `s_ref` is free.
The model computes the feedforward from that chain using the flatness of the link angle. Feedback
is PD on the motor error plus link-rate damping. The disturbances are load torque `|τ_load| ≤ 2 N·m`
and motor torque ripple `|τ_rip| ≤ 0.5 N·m`.

**Claim.** From rest, for every reference trajectory of this form (any snap profile) and every
admissible disturbance:
- the link angle error stays within ±0.0588 rad;
- the link rate error stays within ±0.464 rad/s;
- the transmission-torque error `k(qm − ql) − (Jl a_ref + bl w_ref)` stays within ±4.82 N·m.

The tube theorem also bounds the motor angle about its reference value by ±0.0526 rad.

| Output | Certified | Monte Carlo peak | Falsify worst case | Falsify / certified |
|---|---|---|---|---|
| `e_l` [rad] | 0.05879 | 0.03854 | 0.03856 | 0.656 |
| `ev_l` [rad/s] | 0.4643 | 0.3059 | 0.3072 | 0.662 |
| `e_s` [N·m] | 4.817 | 3.625 | 3.667 | 0.761 |
| `ev_s` [N·m/s] | 103.8 | 50.50 | 75.16 | 0.724 |

- **Tube:** 30 runs on a random reference plus the adjoint worst cases. The largest value of
  zᵀPz/level was 0.708, so every run stayed inside the proved tube.
- **Times:** lmi 28 s, montecarlo 13 s, falsify 37 s, tube 127 s.
- **Figures:** `tube-tube.png`, `falsify-worstcase-e_l.png`, `montecarlo-phase.png`.
- **Workaround:** the certified motor-side coordinates are transmission-torque errors, not the
  motor-angle error `qm − qm_ref`. The motor-angle error has the coefficients `Jl/k` and `bl/k` in
  the references, and fractional frame coefficients broke the generated Lean (see the
  dynacert issues in the top-level report). `Jl = bl = 1` keeps the coefficients integers.

## CNCFeedAxis (certified, reference tracking)

A 200 kg table with 1000 N·s/m friction. Units are mm, mm/s, N and s. A PID on position (the
integrator is a state, poles at a triple −150 rad/s) is combined with the feedforward
`(m a_ref + c v_ref)/1000`. The cutting force is bounded by `|F_cut| ≤ 500 N`.

**Claim.** For any commanded path `x_ref` with `x_ref' = v_ref` and `v_ref' = a_ref`, starting at
rest, the contouring error stays within ±0.316 mm and the feed-rate error stays within ±41.4 mm/s.

| Output | Certified | Monte Carlo peak | Falsify worst case | Falsify / certified |
|---|---|---|---|---|
| `e` [mm] | 0.3158 | 0.05914 | 0.05994 | 0.190 |
| `ev` [mm/s] | 41.41 | 7.336 | 8.987 | 0.217 |
| `ei` [mm·s] | 0.00578 | 0.000741 | 0.000741 | 0.128 |

- **Tube:** the largest value of zᵀPz/level was 0.126.
- **Times:** lmi 60 s, montecarlo 11 s, falsify 38 s, tube 90 s.
- **Figures:** `tube-tube.png`, `falsify-worstcase-e.png`.
- **Conservatism:** the bound is about 5× the worst case. The closed loop is fast (150 rad/s),
  but the lmi search's decay rate α is capped at 10 per time unit, and the certified level scales
  as γ/α.

## GantryPayload (certified, uncertain parameter)

A 30 kg carriage carries an unknown 0–20 kg payload, which enters as the inverse moving mass
`winv ∈ [1/50, 1/30] 1/kg`. Because A must be affine in uncertain parameters, the uncertain
parameter is `1/m` rather than `m`. The disturbances are expressed as accelerations, so B does not
depend on `winv`: frame vibration `|a_vib| ≤ 0.5 m/s²` and cable-carrier drag
`|a_drag| ≤ 0.2 m/s²`. A PID holds the place position. The axis starts with a 2 mm residual error
from the preceding move.

**Claim.** For every payload in 0–20 kg and every admissible disturbance, the position error stays
within ±5.15 mm and the speed within ±57.5 mm/s.

| Output | Certified | Monte Carlo peak | Falsify worst case | Falsify / certified |
|---|---|---|---|---|
| `x` [m] | 0.005147 | 0.003973 | 0.003977 | 0.773 |
| `v` [m/s] | 0.0575 | 0.0426 | 0.04607 | 0.801 |
| `xi` [m·s] | 0.001365 | 0.000875 | 0.000875 | 0.641 |

- **Times:** lmi 28 s, montecarlo 11 s, falsify 25 s.
- **Figures:** `falsify-worstcase-x.png`, `montecarlo-envelope.png`.
- **Workaround:** the motor force is substituted directly into `der(v)`. When it went through an
  algebraic `F` multiplied by the uncertain `winv`, the generated Lean link proof failed with
  `ring failed` (see the top-level report).

## WebTensionControl (certified)

A linearized web span with `EA = 5000 N`, `L = 1 m` and a line speed of 2 m/s. The follower
roller has an equivalent mass of 5 kg. The controller is PI on tension plus speed damping. The
disturbances are leader-roller speed fluctuation `|v_lead| ≤ 0.01 m/s` and a follower torque
disturbance `|F_d| ≤ 2 N`.

**Claim.** The tension deviation stays within ±4.04 N and the follower speed deviation within
±0.0335 m/s.

| Output | Certified | Monte Carlo peak | Falsify worst case | Falsify / certified |
|---|---|---|---|---|
| `T` [N] | 4.045 | 3.414 | 3.529 | 0.872 |
| `v_f` [m/s] | 0.03349 | 0.01811 | 0.02465 | 0.736 |
| `xi` [N·s] | 0.2878 | 0.2510 | 0.2510 | 0.872 |

- **Times:** lmi 80 s, montecarlo 13 s, falsify 19 s.
- **Figures:** `falsify-worstcase-T.png`, `montecarlo-envelope.png`.

## CartPoleLQR (validation only)

A nonlinear cart-pole (`M = 1 kg`, a 0.2 kg tip mass, `l = 0.5 m`) with an LQR designed on the
upright linearization. It starts at 0.1 rad, and the push on the cart is bounded by
`|F_d| ≤ 4 N`. The model is not certifiable by `lmi` because the dynamics contain `sin` and `cos`
terms and a state-dependent mass matrix. Monte Carlo used 300 scenarios.

| Output | Monte Carlo peak | Falsify worst case |
|---|---|---|
| `x` [m] | 0.4591 | 0.4594 |
| `th` [rad] | 0.1532 | 0.1561 |

- **Result:** the pole never exceeds about 9°, so the linearization is a fair approximation over
  this disturbance range. This is evidence, not a proof.
- **Times:** montecarlo 8 s, falsify 57 s.
- **Figures:** `falsify-worstcase-th.png`, `montecarlo-envelope.png`, `montecarlo-exceedance.png`.
