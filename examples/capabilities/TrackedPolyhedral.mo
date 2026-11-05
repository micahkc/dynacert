// A polytope in the error frame of a tracking loop: `polyhedral` reuses the link proof of the
// `lmi` certificate, so the reference chain is handled the same way.
//
//   dynacert examples/capabilities/TrackedPolyhedral.mo certify
model TrackedPolyhedral
  parameter Real kp = 6.0 "Position gain";
  parameter Real kd = 5.0 "Velocity gain";
  input Real x_ref annotation(__Dynacert(reference(derivative = "v_ref", start = 0)));
  input Real v_ref annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref annotation(__Dynacert(reference));
  input Real d "Force disturbance" annotation(__Dynacert(disturbance(bound = 1.0)));
  Real x(start = 0, fixed = true);
  Real v(start = 0, fixed = true);
  Real e annotation(__Dynacert(certify));
  Real ev annotation(__Dynacert(certify));
equation
  e = x - x_ref;
  ev = v - v_ref;
  der(x) = v;
  der(v) = a_ref - kp*e - kd*ev + d;
end TrackedPolyhedral;
