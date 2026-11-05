// KNOWN FAILURE (repro, 2026-11-02): assessment accepts this, then the run stops with "linear
// factors in bounded channels need a region coordinate" on s*(cos(th) - 1). TwoAxisTiltHeave is a
// certifiable variant.
//
// Height hold through a tilting rotor, with a `cos` atom in a product: thrust (g - s) cos θ. The
// tilt loop is independent, and the height loop reads it through a bounded residual channel.
//
//   dynacert examples/capabilities/known-failures/TiltedThrustHeave.mo certify sector
model TiltedThrustHeave
  parameter Real g = 9.81 "Gravity [m/s2]";
  parameter Real kz = 9.0 "Height gain [1/s2]";
  parameter Real kw = 6.0 "Climb-rate gain [1/s]";
  parameter Real kt = 100.0 "Tilt gain [1/s2]";
  parameter Real kq = 20.0 "Tilt-rate gain [1/s]";
  input Real dz "Vertical gust [m/s2]" annotation(__Dynacert(disturbance(bound = 0.5)));
  input Real dq "Tilt torque [rad/s2]" annotation(__Dynacert(disturbance(bound = 2.0)));
  Real z(start = 0, fixed = true) "Height error [m]" annotation(__Dynacert(certify));
  Real vz(start = 0, fixed = true) "Climb-rate error [m/s]";
  Real th(start = 0, fixed = true) "Tilt [rad]" annotation(__Dynacert(certify));
  Real q(start = 0, fixed = true) "Tilt rate [rad/s]";
  Real s "Height command [m/s2]";
equation
  s = kz*z + kw*vz;
  der(z) = vz;
  der(vz) = (g - s)*cos(th) - g + dz;
  der(th) = q;
  der(q) = -kt*th - kq*q + dq;
end TiltedThrustHeave;
