model SwitchedPI "PI loop with conditional integration (anti-windup), switching between two linear modes"
  parameter Real a = 1.0;
  parameter Real kp = 2.0;
  parameter Real ki = 1.0;
  parameter Real ulim = 0.8;
  input Real d annotation(__Dynacert(disturbance(bound = 0.2)));
  Real x(start = 0, fixed = true) annotation(__Dynacert(certify));
  Real z(start = 0, fixed = true) annotation(__Dynacert(certify));
  Real u;
equation
  u = -kp*x - ki*z;
  der(x) = -a*x + u + d;
  der(z) = if abs(u) > ulim then 0 else x;
end SwitchedPI;
