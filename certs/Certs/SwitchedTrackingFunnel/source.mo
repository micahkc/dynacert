// Switching combined with a reference chain and an initial box. The gain schedule is on the
// integrator state, whose derivative is continuous across the surface, so no sliding motion
// arises there.
//
//   dynacert examples/capabilities/SwitchedTrackingFunnel.mo certify switched
model SwitchedTrackingFunnel
  parameter Real kLow = 3.0 "Low position gain";
  parameter Real kHigh = 5.0 "High position gain";
  parameter Real kd = 4.0 "Velocity gain";
  parameter Real ki = 1.0 "Integral gain";
  input Real x_ref annotation(__Dynacert(reference(derivative = "v_ref", start = 0)));
  input Real v_ref annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref annotation(__Dynacert(reference));
  input Real d annotation(__Dynacert(disturbance(bound = 0.2)));
  Real x(start = 0, fixed = true) annotation(__Dynacert(initialSet(min = -0.1, max = 0.1)));
  Real v(start = 0, fixed = true);
  Real xi(start = 0, fixed = true) "Integral of the position error"
    annotation(__Dynacert(certify));
  Real e annotation(__Dynacert(certify));
  Real ev annotation(__Dynacert(certify));
equation
  e = x - x_ref;
  ev = v - v_ref;
  der(xi) = e;
  der(x) = v;
  der(v) = a_ref - (if abs(xi) > 0.2 then kHigh else kLow)*e - kd*ev - ki*xi + d;
end SwitchedTrackingFunnel;
