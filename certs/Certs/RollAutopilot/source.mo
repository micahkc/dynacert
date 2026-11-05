// Roll-attitude autopilot (single-axis roll approximation) with an aileron servo.
//   p'   = L_p*p + L_da*da + L_dist     (roll rate; L_dist = turbulence rolling acceleration)
//   phi' = p
//   da'  = (da_cmd - da)/tau_act
// Autopilot: da_cmd = -k_phi*phi - k_p*p (bank-angle hold with roll-rate damping).
//
// The roll damping derivative L_p varies strongly with dynamic pressure and configuration,
// so it is declared uncertain over [-2.5, -0.8] 1/s; A is affine in L_p.
//
// Certified: bank-angle deviation, roll rate and aileron deflection stay bounded for every
// turbulence rolling acceleration within +-0.5 rad/s^2 and every L_p in the range.
// All values are illustrative.
model RollAutopilot
  parameter Real L_p = -1.5 "Roll damping derivative [1/s]"
    annotation(__Dynacert(uncertain(min = -2.5, max = -0.8)));
  parameter Real L_da = 8.0 "Aileron effectiveness [1/s2]";
  parameter Real tau_act = 0.08 "Aileron servo time constant [s]";
  parameter Real k_phi = 2.0 "Bank-angle gain [rad/rad]";
  parameter Real k_p = 0.6 "Roll-rate gain [rad*s/rad]";

  input Real L_dist "Turbulence rolling acceleration [rad/s2]"
    annotation(__Dynacert(disturbance(bound = 0.5)));

  Real phi(start = 0, fixed = true) "Bank angle deviation [rad]"
    annotation(__Dynacert(certify));
  Real p(start = 0, fixed = true) "Roll rate [rad/s]" annotation(__Dynacert(certify));
  Real da(start = 0, fixed = true) "Aileron deflection [rad]"
    annotation(__Dynacert(certify));
  Real da_cmd "Aileron command [rad]";
equation
  da_cmd = -k_phi*phi - k_p*p;
  der(phi) = p;
  der(p) = L_p*p + L_da*da + L_dist;
  tau_act*der(da) = da_cmd - da;
end RollAutopilot;
