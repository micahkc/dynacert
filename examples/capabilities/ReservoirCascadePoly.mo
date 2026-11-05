// Two reservoirs in series with real, well-separated modes. A polytope fits this flow closely, so
// `polyhedral` can beat the ellipsoid of `lmi`. The portfolio runs both and keeps the tighter
// bound per output.
//
//   dynacert examples/capabilities/ReservoirCascadePoly.mo certify
//   dynacert examples/capabilities/ReservoirCascadePoly.mo certify polyhedral --facets 64
model ReservoirCascadePoly
  parameter Real a1 = 1.0 "Outflow rate, upper [1/h]";
  parameter Real a2 = 0.5 "Outflow rate, lower [1/h]";
  input Real q1 "Inflow error, upper [m/h]" annotation(__Dynacert(disturbance(bound = 1.0)));
  input Real q2 "Inflow error, lower [m/h]" annotation(__Dynacert(disturbance(bound = 0.5)));
  Real h1(start = 0, fixed = true) "Upper level [m]" annotation(__Dynacert(certify));
  Real h2(start = 0, fixed = true) "Lower level [m]" annotation(__Dynacert(certify));
equation
  der(h1) = -a1*h1 + q1;
  der(h2) = a1*h1 - a2*h2 + q2;
end ReservoirCascadePoly;
