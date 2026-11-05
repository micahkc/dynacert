// Nonlinear ship heading autopilot: Norrbin model with rudder saturation (validation only).
//
//   T*r' + r + alpha*r^3 = K*(rudder + d_wave),   psi' = r
// The cubic term (Norrbin) models the nonlinear yaw damping of a course-unstable or
// large-turn regime, and the rudder is limited to +-35 deg by a hard saturation
// rudder = max(-rmax, min(rmax, rudder_cmd)). (A smooth tanh saturation was tried first, but
// dynacert's assessment hangs in sympy.solve on tanh; see README.) The heading setpoint is a constant 30 deg course change
// (start at psi = 0), so the run includes a large initial error that saturates the rudder.
//
// The r^3 and saturation terms make the dynamics nonlinear, so the LMI certificate does not apply;
// montecarlo and falsify still give achieved peaks of the yaw rate during the turn. The
// heading error and rudder command are not annotated: their peaks are set by the initial
// 30 deg error at t = 0. Run with a long horizon (--T 300): the ship responds in minutes.
// Values are illustrative.
model ShipHeadingNorrbin
  parameter Real K = 0.1 "Nomoto gain [1/s]";
  parameter Real T = 20.0 "Nomoto time constant [s]";
  parameter Real alpha = 30.0 "Norrbin cubic damping coefficient [s2]";
  parameter Real rmax = 0.61 "Rudder limit [rad] (35 deg)";
  parameter Real psi_set = 0.5236 "Heading setpoint [rad] (30 deg)";
  parameter Real kp = 3.6 "Heading gain [rad/rad]";
  parameter Real kd = 32.0 "Yaw-rate gain [rad*s/rad]";

  input Real d_wave "Wave yaw moment as equivalent rudder [rad]"
    annotation(__Dynacert(disturbance(bound = 0.035)));

  Real psi(start = 0, fixed = true) "Heading [rad]";
  Real r(start = 0, fixed = true) "Yaw rate [rad/s]" annotation(__Dynacert(certify));
  Real e_psi "Heading error [rad]";
  Real rudder_cmd "Commanded rudder [rad]";
  Real rudder "Actual (saturated) rudder [rad]";
equation
  e_psi = psi - psi_set;
  rudder_cmd = -kp*e_psi - kd*r;
  rudder = max(-rmax, min(rmax, rudder_cmd));
  der(psi) = r;
  T*der(r) = -r - alpha*r^3 + K*(rudder + d_wave);
end ShipHeadingNorrbin;
