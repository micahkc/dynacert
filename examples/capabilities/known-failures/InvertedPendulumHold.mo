// KNOWN FAILURE (repro, 2026-11-02): `certify sector` stops in emit_sector._lin_comb with sympy's
// "reduced() failed without generators", because this model has no algebraic variables. It also
// has one region coordinate, which hits the bug described in CraneHoistSwing.mo.
// TwinPendulumHold is a certifiable variant.
//
// Inverted pendulum held upright by PD: the first nonlinear example, with one `sin` atom. The
// exact linear part plus the residual sin θ - θ (a sector channel, proved in Lean on the region
// that the fixed point finds).
//
//   dynacert examples/capabilities/known-failures/InvertedPendulumHold.mo certify sector
model InvertedPendulumHold
  parameter Real a = 9.81 "g/l [1/s2]";
  parameter Real kp = 25.0 "Angle gain [1/s2]";
  parameter Real kd = 8.0 "Rate gain [1/s]";
  input Real d "Torque disturbance [rad/s2]" annotation(__Dynacert(disturbance(bound = 1.0)));
  Real th(start = 0, fixed = true) "Angle from upright [rad]" annotation(__Dynacert(certify));
  Real w(start = 0, fixed = true) "Rate [rad/s]" annotation(__Dynacert(certify));
equation
  der(th) = w;
  der(w) = a*sin(th) - kp*th - kd*w + d;
end InvertedPendulumHold;
