// atan2 with a constant second argument: rumoca's sympy view simplifies it to atan(s/L), and the
// sector method has no atan atom, so it stops and names the gap. PathFollowScheduled keeps atan2
// in its supported form by scheduling the lookahead on a state.
//
//   dynacert examples/capabilities/ConstantLookaheadGap.mo
model ConstantLookaheadGap
  parameter Real ky = 1.0 "Cross-track gain";
  parameter Real L = 2.0 "Lookahead";
  parameter Real kt = 25.0 "Heading gain [1/s2]";
  parameter Real kr = 10.0 "Rate gain [1/s]";
  input Real dy "Crosswind" annotation(__Dynacert(disturbance(bound = 0.05)));
  Real y(start = 0, fixed = true) "Cross-track error" annotation(__Dynacert(certify));
  Real psi(start = 0, fixed = true) "Heading error [rad]";
  Real r(start = 0, fixed = true) "Yaw rate [rad/s]";
  Real s "Guidance signal";
  Real psi_d "Heading command [rad]";
equation
  s = ky*y;
  psi_d = atan2(-s, L);
  der(y) = sin(psi) + dy;
  der(psi) = r;
  der(r) = -kt*(psi - psi_d) - kr*r;
end ConstantLookaheadGap;
