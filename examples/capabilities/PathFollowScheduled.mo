// Fixed-wing path following with vector-field guidance whose lookahead is scheduled on an airspeed
// deviation dV: heading command atan2(-s, L + tau dV), kinematics V sin ψ. Two atoms (`atan2`,
// `sin`), and the speed loop is an independent block read through a residual channel.
//
//   dynacert examples/capabilities/PathFollowScheduled.mo certify sector
model PathFollowScheduled
  parameter Real V = 1.0 "Normalized airspeed";
  parameter Real ky = 1.0 "Cross-track gain";
  parameter Real L = 2.0 "Nominal lookahead";
  parameter Real tau = 1.0 "Lookahead per unit airspeed deviation";
  parameter Real ku = 2.0 "Airspeed loop rate [1/s]";
  parameter Real kt = 25.0 "Heading gain [1/s2]";
  parameter Real kr = 10.0 "Rate gain [1/s]";
  input Real dy "Crosswind" annotation(__Dynacert(disturbance(bound = 0.02)));
  input Real dr "Yaw gust [rad/s2]" annotation(__Dynacert(disturbance(bound = 0.1)));
  input Real du "Headwind change" annotation(__Dynacert(disturbance(bound = 0.1)));
  Real y(start = 0, fixed = true) "Cross-track error" annotation(__Dynacert(certify));
  Real psi(start = 0, fixed = true) "Heading error [rad]" annotation(__Dynacert(certify));
  Real r(start = 0, fixed = true) "Yaw rate [rad/s]";
  Real dV(start = 0, fixed = true) "Airspeed deviation";
  Real s "Guidance signal";
  Real psi_d "Heading command [rad]";
equation
  s = ky*y;
  psi_d = atan2(-s, L + tau*dV);
  der(y) = V*sin(psi) + dy;
  der(psi) = r;
  der(r) = -kt*(psi - psi_d) - kr*r + dr;
  der(dV) = -ku*dV + du;
end PathFollowScheduled;
