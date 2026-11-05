model ArrayTracking "Two-axis PD tracking with array references (scalarization fixture)"
  parameter Real m = 1.0;
  parameter Real c = 0.2;
  parameter Real Kp[2,2] = {{2.0, 0}, {0, 3.0}} "Proportional gain matrix";
  parameter Real kd[2] = {0.8, 1.2} "Derivative gains";
  input Real x_ref[2] annotation(__Dynacert(reference(derivative = "v_ref", start = 0)));
  input Real v_ref[2] annotation(__Dynacert(reference(derivative = "a_ref", start = {0, 0})));
  input Real a_ref[2] annotation(__Dynacert(reference));
  input Real d[2] annotation(__Dynacert(disturbance(bound = {1.0, 0.5})));
  Real x[2](each start = 0, each fixed = true);
  Real v[2](each start = 0, each fixed = true);
  Real F[2];
  Real e[2] annotation(__Dynacert(certify));
  Real ev[2] annotation(__Dynacert(certify));
equation
  e = x - x_ref;
  ev = v - v_ref;
  F = m * a_ref + c * v_ref - Kp * e - {kd[1] * ev[1], kd[2] * ev[2]};
  der(x) = v;
  m * der(v) = F + d - c * v;
end ArrayTracking;
