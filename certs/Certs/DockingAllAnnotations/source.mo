// Every linear annotation at once: a reference chain, a disturbance, an uncertain parameter and
// an initial box. The claim covers every drag value, every admissible approach trajectory and
// every start in the box.
//
//   dynacert examples/capabilities/DockingAllAnnotations.mo certify lmi
//   dynacert examples/capabilities/DockingAllAnnotations.mo view tube
model DockingAllAnnotations
  parameter Real m = 1.0 "Normalized mass";
  parameter Real c = 0.4 "Plume and drag coefficient"
    annotation(__Dynacert(uncertain(min = 0.2, max = 0.6)));
  parameter Real kp = 4.0 "Position gain";
  parameter Real kd = 4.0 "Velocity gain";
  input Real x_ref "Approach path [m]"
    annotation(__Dynacert(reference(derivative = "v_ref", start = 0)));
  input Real v_ref "Approach speed [m/s]"
    annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref "Approach acceleration [m/s2]" annotation(__Dynacert(reference));
  input Real d "Thruster error [N]" annotation(__Dynacert(disturbance(bound = 0.2)));
  Real x(start = 0, fixed = true) "Position [m]"
    annotation(__Dynacert(initialSet(min = -0.1, max = 0.1)));
  Real v(start = 0, fixed = true) "Velocity [m/s]"
    annotation(__Dynacert(initialSet(min = -0.05, max = 0.05)));
  Real e "Position error [m]" annotation(__Dynacert(certify));
  Real ev "Velocity error [m/s]" annotation(__Dynacert(certify));
equation
  e = x - x_ref;
  ev = v - v_ref;
  der(x) = v;
  m*der(v) = m*a_ref + c*v_ref - kp*e - kd*ev - c*v + d;
end DockingAllAnnotations;
