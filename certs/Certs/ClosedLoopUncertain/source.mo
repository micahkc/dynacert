// cp_reach examples/general/models/closed_loop.mo, with the feedforward computed in the
// model (u_ff = m a_ref + c v_ref + k x_ref) instead of supplied as a free input, and the
// reference trajectory declared: x_ref' = v_ref, v_ref' = a_ref, starting at rest.
model ClosedLoopUncertain
  parameter Real m = 1.0 "Mass [kg]";
  parameter Real c = 0.2 "Damping coefficient [N*s/m]"
    annotation(__Dynacert(uncertain(min = 0.1, max = 0.3)));
  parameter Real k = 1.0 "Spring constant [N/m]";
  parameter Real kp = 2.0 "Proportional gain";
  parameter Real kd = 0.8 "Derivative gain";

  input Real x_ref "Reference position [m]"
    annotation(__Dynacert(reference(derivative = "v_ref", start = 0)));
  input Real v_ref "Reference velocity [m/s]"
    annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref "Reference acceleration [m/s2]" annotation(__Dynacert(reference));
  input Real d "Disturbance force [N]" annotation(__Dynacert(disturbance(bound = 1.0)));

  Real x(start = 0, fixed = true) "Position [m]";
  Real v(start = 0, fixed = true) "Velocity [m/s]";

  Real u_ff "Feedforward force [N]";
  Real F "Control force [N]";
  Real e "Position error [m]" annotation(__Dynacert(certify));
  Real ev "Velocity error [m/s]" annotation(__Dynacert(certify));
equation
  e = x - x_ref;
  ev = v - v_ref;
  u_ff = m*a_ref + c*v_ref + k*x_ref;
  F = u_ff - kp*e - kd*ev;
  der(x) = v;
  der(v) = (F + d - c*v - k*x) / m;
end ClosedLoopUncertain;
