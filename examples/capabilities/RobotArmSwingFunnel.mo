// One-link robot arm on a large rest-to-rest swing. Far from any equilibrium, so the certificate
// is a finite-horizon funnel: a piecewise-polynomial P(t) checked by univariate SOS on [0, 2] s.
// The feedforward makes the polynomial reference an exact undisturbed solution.
//
//   dynacert examples/capabilities/RobotArmSwingFunnel.mo certify funnel --segments 8
model RobotArmSwingFunnel
  parameter Real G = 2.0 "m g l / I [1/s2]";
  parameter Real kp = 16.0 "Angle gain [1/s2]";
  parameter Real kd = 8.0 "Rate gain [1/s]";
  parameter Real A = 0.5 "Reference peak [rad]";
  parameter Real Tf = 2 "Reference duration [s]";
  input Real w "Disturbance torque [rad/s2]" annotation(__Dynacert(disturbance(bound = 0.1)));
  Real theta(start = 0, fixed = true) annotation(__Dynacert(nominal = "theta_ref"));
  Real omega(start = 0, fixed = true) annotation(__Dynacert(nominal = "omega_ref"));
  Real s "Normalized time";
  Real theta_ref;
  Real omega_ref;
  Real a_ref;
  Real u "Control torque [rad/s2]";
  Real e "Angle error [rad]" annotation(__Dynacert(certify));
equation
  s = time/Tf;
  theta_ref = 64*A*s^3*(1 - s)^3;
  omega_ref = 64*A*(3*s^2*(1 - s)^3 - 3*s^3*(1 - s)^2)/Tf;
  a_ref = 64*A*(6*s*(1 - s)^3 - 18*s^2*(1 - s)^2 + 6*s^3*(1 - s))/Tf^2;
  u = a_ref + G*sin(theta_ref) + kp*(theta_ref - theta) + kd*(omega_ref - omega);
  der(theta) = omega;
  der(omega) = -G*sin(theta) + u + w;
  e = theta - theta_ref;
  annotation(__Dynacert(horizon = 2), experiment(StopTime = 2));
end RobotArmSwingFunnel;
