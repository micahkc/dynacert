// Two-axis pen plotter tracking any trajectory with bounded acceleration data. The references are
// arrays: x_ref' = v_ref and v_ref' = a_ref hold per axis, and a_ref is free. The proof changes
// to the error frame (e, ev), so the bound holds along every reference.
//
//   dynacert examples/capabilities/PlotterXYTracking.mo certify lmi
//   dynacert examples/capabilities/PlotterXYTracking.mo view tube
model PlotterXYTracking
  parameter Real m = 1.0 "Carriage mass [kg]";
  parameter Real c = 0.5 "Viscous friction [N s/m]";
  parameter Real Kp[2,2] = {{16.0, 0}, {0, 25.0}} "Position gain [N/m]";
  parameter Real kd[2] = {8.0, 10.0} "Velocity gain [N s/m]";
  input Real x_ref[2] "Pen path [m]"
    annotation(__Dynacert(reference(derivative = "v_ref", start = 0)));
  input Real v_ref[2] "Path velocity [m/s]"
    annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref[2] "Path acceleration [m/s2]" annotation(__Dynacert(reference));
  input Real d[2] "Belt disturbance [N]" annotation(__Dynacert(disturbance(bound = {1.0, 0.5})));
  Real x[2](each start = 0, each fixed = true) "Carriage position [m]";
  Real v[2](each start = 0, each fixed = true) "Carriage velocity [m/s]";
  Real F[2] "Motor force [N]";
  Real e[2] "Position error [m]" annotation(__Dynacert(certify));
  Real ev[2] "Velocity error [m/s]" annotation(__Dynacert(certify));
equation
  e = x - x_ref;
  ev = v - v_ref;
  F = m * a_ref + c * v_ref - Kp * e - {kd[1] * ev[1], kd[2] * ev[2]};
  der(x) = v;
  m * der(v) = F + d - c * v;
end PlotterXYTracking;
