// ClosedLoop (see ClosedLoop.mo) started anywhere in an initial box: x(0), v(0) ∈ [-1, 1]
// instead of at rest. The certificate proves the invariant tube covering the box and a
// shrinking funnel V(z(t)) ≤ V₀e^{-αt} + (γμ/α)(1 - e^{-αt}) (`Cert.funnel`).
model ClosedLoopInitial
  parameter Real m = 1.0 "Mass [kg]";
  parameter Real c = 0.2 "Damping coefficient [N*s/m]";
  parameter Real k = 1.0 "Spring constant [N/m]";
  parameter Real kp = 2.0 "Proportional gain";
  parameter Real kd = 0.8 "Derivative gain";

  input Real x_ref "Reference position [m]"
    annotation(__Dynacert(reference(derivative = "v_ref", start = 0)));
  input Real v_ref "Reference velocity [m/s]"
    annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref "Reference acceleration [m/s2]" annotation(__Dynacert(reference));
  input Real d "Disturbance force [N]" annotation(__Dynacert(disturbance(bound = 1.0)));

  Real x(start = 0, fixed = true) "Position [m]"
    annotation(__Dynacert(initialSet(min = -1, max = 1)));
  Real v(start = 0, fixed = true) "Velocity [m/s]"
    annotation(__Dynacert(initialSet(min = -1, max = 1)));

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
end ClosedLoopInitial;
