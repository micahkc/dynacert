// Planar (x-z) quadrotor holding hover under a cascaded controller, from "Where to Tear:
// Compositional Invariant-Tube Certificates for a Nonlinear Quadrotor", Section III.
//
// States: position errors e_x, e_z, velocity errors v_x, v_z, pitch theta, pitch rate q
// (mass and inertia normalized, hover reference at the origin).
// Outer loop: s = Kp*e_p + Kv*e_v, thrust f = -s + g*z_hat, commanded pitch
//   theta_d = atan2(-s_x, g - s_z), thrust acceleration |f|.
// Inner loop: q' = -k_theta*(theta - theta_d) - k_q*q + w_q, k_theta = wn^2, k_q = 2*wn.
// Disturbances: gusts |w_x|, |w_z| <= wbar and torque |w_q| <= 5*wbar.
//
// The linearization is benign (exact peak-to-peak gain 0.373 m to e_x at wbar = 1), but the
// model is nonlinear: `dynacert ... certify sector` treats the six residual channels of the
// paper's Table II with sector multipliers on a region found by a fixed point, and proves
// every sector/peak bound of the residuals in Lean. With wn = 10 (5x bandwidth separation)
// the joint certificate closes up to about 25% of the full disturbance level, the default
// here; `compose` certifies the same tube through the lateral+pitch | vertical cut.
model PlanarQuadrotor
  parameter Real g = 9.81 "Gravity [m/s2]";
  parameter Real Kp = 4.0 "Outer-loop position gain [1/s2]";
  parameter Real Kv = 4.0 "Outer-loop velocity gain [1/s]";
  parameter Real wn = 10.0 "Inner-loop natural frequency [rad/s]";
  parameter Real k_theta = wn^2 "Pitch gain [1/s2]";
  parameter Real k_q = 2*wn "Pitch-rate gain [1/s]";
  parameter Real wbar = 0.25 "Gust bound [m/s2] (1 = the paper's full level)";

  input Real w_x "Lateral gust [m/s2]" annotation(__Dynacert(disturbance(bound = 0.25)));
  input Real w_z "Vertical gust [m/s2]" annotation(__Dynacert(disturbance(bound = 0.25)));
  input Real w_q "Pitch torque disturbance [rad/s2]"
    annotation(__Dynacert(disturbance(bound = 1.25)));

  Real e_x(start = 0, fixed = true) "Lateral position error [m]" annotation(__Dynacert(certify));
  Real e_z(start = 0, fixed = true) "Vertical position error [m]";
  Real v_x(start = 0, fixed = true) "Lateral velocity error [m/s]";
  Real v_z(start = 0, fixed = true) "Vertical velocity error [m/s]";
  Real theta(start = 0, fixed = true) "Pitch [rad]" annotation(__Dynacert(certify));
  Real q(start = 0, fixed = true) "Pitch rate [rad/s]";
  Real s_x "Outer-loop command, lateral [m/s2]";
  Real s_z "Outer-loop command, vertical [m/s2]";
  Real f_norm "Thrust acceleration |f| [m/s2]";
  Real theta_d "Commanded pitch [rad]";
equation
  s_x = Kp*e_x + Kv*v_x;
  s_z = Kp*e_z + Kv*v_z;
  f_norm = sqrt(s_x^2 + (g - s_z)^2);
  theta_d = atan2(-s_x, g - s_z);
  der(e_x) = v_x;
  der(e_z) = v_z;
  der(v_x) = f_norm*sin(theta) + w_x;
  der(v_z) = f_norm*cos(theta) - g + w_z;
  der(theta) = q;
  der(q) = -k_theta*(theta - theta_d) - k_q*q + w_q;
end PlanarQuadrotor;
