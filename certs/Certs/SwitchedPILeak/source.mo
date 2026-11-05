model SwitchedPILeak "PI loop with conditional integration and integrator bleed-off: while the actuator demand exceeds its limit the integrator leaks instead of integrating"
  parameter Real a = 1.0 "plant pole";
  parameter Real kp = 2.0 "proportional gain";
  parameter Real ki = 1.0 "integral gain";
  parameter Real ulim = 0.8 "actuator demand above which integration stops";
  parameter Real lam = 0.5 "bleed-off rate of the integrator while saturated";
  input Real d annotation(__Dynacert(disturbance(bound = 0.2)));
  Real x(start = 0, fixed = true) annotation(__Dynacert(certify));
  Real z(start = 0, fixed = true) annotation(__Dynacert(certify));
  Real u "controller demand";
equation
  u = -kp*x - ki*z;
  der(x) = -a*x + u + d;
  der(z) = if abs(u) > ulim then -lam*z else x;
end SwitchedPILeak;
