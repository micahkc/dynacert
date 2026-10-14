// A nonlinear example: a pendulum held near a reference angle by a PD controller with
// gravity compensation at the reference only. The sin(theta) term makes the error dynamics
// nonlinear, so the LMI approach does not apply; the simulation approaches still do.
model PendulumPD
  parameter Real m = 1.0 "Mass [kg]";
  parameter Real l = 1.0 "Length [m]";
  parameter Real g = 9.81 "Gravity [m/s2]";
  parameter Real b = 0.1 "Damping [N*m*s/rad]";
  parameter Real kp = 20.0 "Proportional gain";
  parameter Real kd = 6.0 "Derivative gain";
  parameter Real theta_ref = 0.5 "Reference angle [rad]";

  input Real tau_d "Disturbance torque [N*m]" annotation(__Dynacert(disturbance(bound = 1.0)));

  Real theta(start = 0.5, fixed = true) "Angle [rad]";
  Real omega(start = 0, fixed = true) "Angular rate [rad/s]";
  Real tau "Control torque [N*m]";
  Real e "Angle error [rad]" annotation(__Dynacert(certify));
equation
  e = theta - theta_ref;
  tau = m*g*l*sin(theta_ref) - kp*e - kd*omega;
  der(theta) = omega;
  m*l^2*der(omega) = tau + tau_d - b*omega - m*g*l*sin(theta);
end PendulumPD;
