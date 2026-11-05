# Switching examples (`if`-expressions)

Models whose equations switch, in continuous time, between linear modes. The `switched`
certify method proves peak bounds with one quadratic storage common to every mode
(see [docs/switching.md](../../docs/switching.md)).

| Model | What switches | `switched` |
|---|---|---|
| [SwitchedPILeak.mo](SwitchedPILeak.mo) | PI anti-windup: while the actuator demand exceeds its limit the integrator bleeds off instead of integrating | certified |
| [GainScheduledPI.mo](GainScheduledPI.mo) | speed loop, proportional gain scheduled on the load estimate (integrator state); the motor torque `u` has a mode-dependent row | certified |
| [AsymmetricDamper.mo](AsymmetricDamper.mo) | quarter-car body mode, damper stiffer in rebound than in compression | certified |
| [BumpStopSuspension.mo](BumpStopSuspension.mo) | three-stage damper (`if … elseif … else`) and a bump stop: 2 switches, 6 modes | certified |
| [SwitchedPI.mo](SwitchedPI.mo) | PI with pure conditional integration (`der(z) = 0` while saturated) | **not certifiable**: the frozen mode is not asymptotically stable |
| [SwitchedUnstable.mo](SwitchedUnstable.mo) | two stable oscillators switched by quadrant | **not certifiable**: no common quadratic Lyapunov function; the switched system is unstable |

```
python3 -m dynacert examples/switching/AsymmetricDamper.mo                   # assess
python3 -m dynacert examples/switching/AsymmetricDamper.mo certify switched  # Lean-checked
python3 -m dynacert examples/switching/AsymmetricDamper.mo validate --n 200  # Monte Carlo + falsify
```

Results (certified bound vs best simulated peak):

| Model | Output | Certified | Monte Carlo (200) | Falsify |
|---|---|---|---|---|
| SwitchedPILeak | x / z | 0.1637 / 0.2075 | 0.1069 / 0.1949 | 0.1080 / 0.1949 |
| GainScheduledPI | w / z / u | 0.3240 / 0.1925 / 1.2508 | 0.1707 / 0.1492 / 0.7071 | 0.1707 / 0.1492 / 0.7070 |
| AsymmetricDamper | x / v | 0.4516 / 0.8942 | 0.2861 / 0.4625 | 0.2921 / 0.4799 |
| BumpStopSuspension | x / v | 0.8327 / 2.0216 | 0.2168 / 0.3727 | 0.2179 / 0.3706 |

The claim covers classical solutions of the equations as written; sliding motions on a
switching surface are not covered (docs/switching.md explains why the same certificate would
hold for them, and why it is not claimed).
