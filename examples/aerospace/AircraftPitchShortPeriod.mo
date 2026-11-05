// Aircraft pitch-attitude hold on the short-period approximation, with an elevator actuator.
//
// Short-period dynamics (stability axes, linearized about trimmed cruise) with a vertical
// gust entering as an angle-of-attack perturbation alpha_g = w_gust / V:
//   alpha' = Z_a*(alpha + alpha_g) + q + Z_de*de
//   q'     = M_a*(alpha + alpha_g) + M_q*q + M_de*de
//   theta' = q
// Elevator servo: first-order lag with time constant tau_act.
// Autopilot: pitch-attitude hold with rate damping, de_cmd = k_theta*theta + k_q*q
// (positive elevator is trailing-edge down, pitching the nose down, so M_de < 0).
// All variables are perturbations from trim.
//
// Certified: pitch-attitude deviation, angle-of-attack deviation and elevator deflection stay
// bounded for every gust with |alpha_g| <= 0.03 rad (about 7 m/s at 230 m/s), plus the pitch
// rate. All derivative values are illustrative, not from a specific aircraft.
model AircraftPitchShortPeriod
  parameter Real Z_a = -1.0 "Z_alpha / V [1/s]";
  parameter Real Z_de = -0.1 "Z_delta_e / V [1/s]";
  parameter Real M_a = -4.0 "Pitch stiffness M_alpha [1/s2]";
  parameter Real M_q = -1.5 "Pitch damping M_q [1/s]";
  parameter Real M_de = -6.0 "Elevator effectiveness M_delta_e [1/s2]";
  parameter Real tau_act = 0.05 "Elevator actuator time constant [s]";
  parameter Real k_theta = 2.0 "Pitch attitude gain [rad/rad]";
  parameter Real k_q = 0.8 "Pitch rate gain [rad*s/rad]";

  input Real alpha_g "Gust angle of attack w_gust/V [rad]"
    annotation(__Dynacert(disturbance(bound = 0.03)));

  Real alpha(start = 0, fixed = true) "Angle-of-attack deviation [rad]"
    annotation(__Dynacert(certify));
  Real q(start = 0, fixed = true) "Pitch rate [rad/s]" annotation(__Dynacert(certify));
  Real theta(start = 0, fixed = true) "Pitch attitude deviation [rad]"
    annotation(__Dynacert(certify));
  Real de(start = 0, fixed = true) "Elevator deflection [rad]"
    annotation(__Dynacert(certify));
  Real de_cmd "Elevator command [rad]";
equation
  de_cmd = k_theta*theta + k_q*q;
  der(alpha) = Z_a*(alpha + alpha_g) + q + Z_de*de;
  der(q) = M_a*(alpha + alpha_g) + M_q*q + M_de*de;
  der(theta) = q;
  tau_act*der(de) = de_cmd - de;
end AircraftPitchShortPeriod;
