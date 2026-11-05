model GainScheduledPI "Speed loop with a gain schedule on the load estimate: the integrator state estimates the load torque, and the proportional gain is raised while the estimated load is large"
  parameter Real J = 0.5 "inertia";
  parameter Real b = 0.2 "viscous friction";
  parameter Real kpHigh = 4.0 "proportional gain under large load";
  parameter Real kpLow = 1.5 "proportional gain under small load";
  parameter Real ki = 2.0 "integral gain";
  parameter Real zLoad = 0.05 "load-estimate threshold of the schedule";
  input Real tau "load torque" annotation(__Dynacert(disturbance(bound = 0.3)));
  Real w(start = 0, fixed = true) "speed error" annotation(__Dynacert(certify));
  Real z(start = 0, fixed = true) "integrated error (load estimate)" annotation(__Dynacert(certify));
  Real u "motor torque" annotation(__Dynacert(certify));
equation
  u = -(if abs(z) > zLoad then kpHigh else kpLow)*w - ki*z;
  J*der(w) = -b*w + u + tau;
  der(z) = w;
end GainScheduledPI;
