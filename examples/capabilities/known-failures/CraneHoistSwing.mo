// KNOWN FAILURE (repro, 2026-11-02): with one region coordinate the generated SectorLink.lean has
// `obtain hR0 := hR`, which does not bind hR0, so the build fails with "Unknown identifier hR0".
// `compose` stops separately with "ADMM failed for objective e". CraneTwoAxisSwing is a
// certifiable variant.
//
// A hoist accelerating a swinging load. The swing stiffness is modulated by the hoist command
// `s_h`, the product term s_h·sin φ. The hoist and the swing share only this weak residual
// channel, so `compose` splits them at the cut {phi, w} | {e, v}, solves one LMI per block by
// ADMM, and proves the interconnection condition on supply rates.
//
//   dynacert examples/capabilities/known-failures/CraneHoistSwing.mo certify sector
//   dynacert examples/capabilities/known-failures/CraneHoistSwing.mo certify compose
model CraneHoistSwing
  parameter Real g = 9.81 "g/l [1/s2]";
  parameter Real kp = 9.0 "Swing damping feedback, angle [1/s2]";
  parameter Real kd = 6.0 "Swing damping feedback, rate [1/s]";
  parameter Real ke = 16.0 "Hoist position gain [1/s2]";
  parameter Real kv = 8.0 "Hoist velocity gain [1/s]";
  input Real d_phi "Wind on the load [rad/s2]" annotation(__Dynacert(disturbance(bound = 0.5)));
  input Real d_h "Hoist force error [m/s2]" annotation(__Dynacert(disturbance(bound = 0.5)));
  Real phi(start = 0, fixed = true) "Swing angle [rad]" annotation(__Dynacert(certify));
  Real w(start = 0, fixed = true) "Swing rate [rad/s]";
  Real e(start = 0, fixed = true) "Hoist position error [m]" annotation(__Dynacert(certify));
  Real v(start = 0, fixed = true) "Hoist velocity error [m/s]";
  Real s_h "Hoist acceleration command [m/s2]";
equation
  s_h = ke*e + kv*v;
  der(phi) = w;
  der(w) = -g*sin(phi) + s_h*sin(phi) - kp*phi - kd*w + d_phi;
  der(e) = v;
  der(v) = -s_h + d_h;
end CraneHoistSwing;
