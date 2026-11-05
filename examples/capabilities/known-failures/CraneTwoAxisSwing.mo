// KNOWN FAILURE (repro, 2026-11-02): `certify sector` fails to build, with "Type mismatch" at line 94
// of the generated SectorCert.lean. `certify compose` stops with "ADMM failed for objective e".
//
// A hoist accelerating a load that swings on two axes. The hoist command `s_h` modulates each
// swing's stiffness through the product s_h·sin φ, the only link between the blocks. `sector` gives
// one joint ellipsoid; `compose` cuts along those weak residual edges and proves supply rates.
//
//   dynacert examples/capabilities/known-failures/CraneTwoAxisSwing.mo certify sector
//   dynacert examples/capabilities/known-failures/CraneTwoAxisSwing.mo certify compose
model CraneTwoAxisSwing
  parameter Real g = 9.81 "g/l [1/s2]";
  parameter Real kp = 9.0 "Swing angle feedback [1/s2]";
  parameter Real kd = 6.0 "Swing rate feedback [1/s]";
  parameter Real ke = 16.0 "Hoist position gain [1/s2]";
  parameter Real kv = 8.0 "Hoist velocity gain [1/s]";
  input Real d1 "Wind, axis 1 [rad/s2]" annotation(__Dynacert(disturbance(bound = 0.5)));
  input Real d2 "Wind, axis 2 [rad/s2]" annotation(__Dynacert(disturbance(bound = 0.3)));
  input Real d_h "Hoist force error [m/s2]" annotation(__Dynacert(disturbance(bound = 0.5)));
  Real phi1(start = 0, fixed = true) "Swing, axis 1 [rad]" annotation(__Dynacert(certify));
  Real w1(start = 0, fixed = true) "Swing rate, axis 1 [rad/s]";
  Real phi2(start = 0, fixed = true) "Swing, axis 2 [rad]" annotation(__Dynacert(certify));
  Real w2(start = 0, fixed = true) "Swing rate, axis 2 [rad/s]";
  Real e(start = 0, fixed = true) "Hoist position error [m]" annotation(__Dynacert(certify));
  Real v(start = 0, fixed = true) "Hoist velocity error [m/s]";
  Real s_h "Hoist acceleration command [m/s2]";
equation
  s_h = ke*e + kv*v;
  der(phi1) = w1;
  der(w1) = -g*sin(phi1) + s_h*sin(phi1) - kp*phi1 - kd*w1 + d1;
  der(phi2) = w2;
  der(w2) = -g*sin(phi2) + s_h*sin(phi2) - kp*phi2 - kd*w2 + d2;
  der(e) = v;
  der(v) = -s_h + d_h;
end CraneTwoAxisSwing;
