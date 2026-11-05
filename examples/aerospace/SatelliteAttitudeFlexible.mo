// Single-axis spacecraft attitude control with a flexible appendage (two-inertia model).
//
// A rigid hub (inertia J_hub) carries a solar array (inertia J_arr) through a torsional
// spring/damper representing the array's first bending mode:
//   J_hub*w_hub' = u + tau_d - k_f*(th_hub - th_arr) - c_f*(w_hub - w_arr)
//   J_arr*w_arr' =             k_f*(th_hub - th_arr) + c_f*(w_hub - w_arr)
// The attitude controller is a collocated PD on the hub (star tracker + gyro on the hub):
//   u = -kp*th_hub - kd*w_hub.
// tau_d is an external disturbance torque (thruster misalignment during a burn).
//
// Certified: hub pointing error, hub rate and array twist (th_hub - th_arr, a structural
// load proxy) stay bounded for every disturbance torque within +-1 N*m.
// Values are illustrative.
model SatelliteAttitudeFlexible
  parameter Real J_hub = 500.0 "Hub inertia [kg*m2]";
  parameter Real J_arr = 150.0 "Array inertia about the axis [kg*m2]";
  parameter Real k_f = 800.0 "Array torsional stiffness [N*m/rad]";
  parameter Real c_f = 20.0 "Array structural damping [N*m*s/rad]";
  parameter Real kp = 400.0 "Attitude gain [N*m/rad]";
  parameter Real kd = 1200.0 "Rate gain [N*m*s/rad]";

  input Real tau_d "Disturbance torque [N*m]" annotation(__Dynacert(disturbance(bound = 1.0)));

  Real th_hub(start = 0, fixed = true) "Hub attitude error [rad]"
    annotation(__Dynacert(certify));
  Real w_hub(start = 0, fixed = true) "Hub rate [rad/s]" annotation(__Dynacert(certify));
  Real th_arr(start = 0, fixed = true) "Array angle [rad]";
  Real w_arr(start = 0, fixed = true) "Array rate [rad/s]";
  Real twist "Array twist th_hub - th_arr [rad]" annotation(__Dynacert(certify));
  Real u "Control torque [N*m]";
  Real tau_f "Flexible coupling torque [N*m]";
equation
  u = -kp*th_hub - kd*w_hub;
  twist = th_hub - th_arr;
  tau_f = k_f*twist + c_f*(w_hub - w_arr);
  der(th_hub) = w_hub;
  der(th_arr) = w_arr;
  J_hub*der(w_hub) = u + tau_d - tau_f;
  J_arr*der(w_arr) = tau_f;
end SatelliteAttitudeFlexible;
