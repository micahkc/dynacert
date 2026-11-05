// Adaptive cruise control: constant-time-headway gap keeping behind a lead vehicle.
//
// The ego vehicle's acceleration follows the commanded acceleration through a first-order
// powertrain/brake lag with bandwidth w_pt, which is uncertain (it varies with gear, load
// and brake temperature). The lead vehicle's acceleration is an unknown bounded disturbance.
//   spacing error  e  = gap - (s0 + h*v_ego), s0 the standstill spacing
//   relative speed dv = v_lead - v_ego
// Controller: a_cmd = kp*e + kd*dv (standard CTH ACC law).
//
// The model is written directly in the error coordinates (e, dv, a_ego): dynacert does not
// yet extract an error frame from absolute states (gap, v_ego, v_lead) when no reference is
// declared, and rejects the constant offset s0 in an output (see README).
//   e'  = dv - h*a_ego,   dv' = a_lead - a_ego
//
// Certified: |e|, |dv| and |a_ego| stay bounded for every lead-vehicle acceleration within
// +-2 m/s^2 and every powertrain bandwidth in [2, 5] rad/s.
// All parameter values are illustrative.
model AdaptiveCruiseGap
  parameter Real h = 1.5 "Time headway [s]";
  parameter Real kp = 0.4 "Spacing-error gain [1/s2]";
  parameter Real kd = 0.9 "Relative-speed gain [1/s]";
  parameter Real w_pt = 3.0 "Powertrain bandwidth [rad/s]"
    annotation(__Dynacert(uncertain(min = 2.0, max = 5.0)));

  input Real a_lead "Lead vehicle acceleration [m/s2]"
    annotation(__Dynacert(disturbance(bound = 2.0)));

  Real e(start = 0, fixed = true) "Spacing error gap - (s0 + h*v_ego) [m]"
    annotation(__Dynacert(certify));
  Real dv(start = 0, fixed = true) "Relative speed v_lead - v_ego [m/s]"
    annotation(__Dynacert(certify));
  Real a_ego(start = 0, fixed = true) "Ego acceleration [m/s2]"
    annotation(__Dynacert(certify));
  Real a_cmd "Commanded acceleration [m/s2]";
equation
  a_cmd = kp*e + kd*dv;
  der(e) = dv - h*a_ego;
  der(dv) = a_lead - a_ego;
  // a_cmd is written out here: dynacert's link proof fails (`ring failed`) when an uncertain
  // parameter multiplies an algebraic variable (see README).
  der(a_ego) = w_pt*(kp*e + kd*dv - a_ego);
end AdaptiveCruiseGap;
