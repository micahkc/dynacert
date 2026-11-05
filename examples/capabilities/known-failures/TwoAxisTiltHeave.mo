// KNOWN FAILURE (repro, 2026-11-02): `certify sector` and `certify compose` both fail to build, with
// "Type mismatch" at line 94 of the generated SectorCert.lean / ComposeCert.lean. Cause not diagnosed.
//
// Height hold with thrust tilted about two axes, which adds `cos` atoms as bounded residual
// channels. The tilt loops are independent and the height loop reads them only through those
// residuals, so `compose` can split the model at weak edges.
//
//   dynacert examples/capabilities/known-failures/TwoAxisTiltHeave.mo certify sector
//   dynacert examples/capabilities/known-failures/TwoAxisTiltHeave.mo certify compose
model TwoAxisTiltHeave
  parameter Real g = 9.81 "Gravity [m/s2]";
  parameter Real kz = 9.0 "Height gain [1/s2]";
  parameter Real kw = 6.0 "Climb-rate gain [1/s]";
  parameter Real kt = 100.0 "Tilt gain [1/s2]";
  parameter Real kq = 20.0 "Tilt-rate gain [1/s]";
  input Real dz "Vertical gust [m/s2]" annotation(__Dynacert(disturbance(bound = 0.5)));
  input Real d1 "Roll torque [rad/s2]" annotation(__Dynacert(disturbance(bound = 2.0)));
  input Real d2 "Pitch torque [rad/s2]" annotation(__Dynacert(disturbance(bound = 2.0)));
  Real z(start = 0, fixed = true) "Height error [m]" annotation(__Dynacert(certify));
  Real vz(start = 0, fixed = true) "Climb-rate error [m/s]";
  Real t1(start = 0, fixed = true) "Roll [rad]" annotation(__Dynacert(certify));
  Real q1(start = 0, fixed = true) "Roll rate [rad/s]";
  Real t2(start = 0, fixed = true) "Pitch [rad]" annotation(__Dynacert(certify));
  Real q2(start = 0, fixed = true) "Pitch rate [rad/s]";
  Real s "Height command [m/s2]";
equation
  s = kz*z + kw*vz;
  der(z) = vz;
  der(vz) = g*(cos(t1) - 1) + g*(cos(t2) - 1) - s + dz;
  der(t1) = q1;
  der(q1) = -kt*t1 - kq*q1 + d1;
  der(t2) = q2;
  der(q2) = -kt*t2 - kq*q2 + d2;
end TwoAxisTiltHeave;
