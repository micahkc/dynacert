// Open-loop unstable: no invariant ellipsoid exists, so `lmi` reports infeasibility at assessment
// instead of a weak bound. Monte Carlo shows the growth.
//
//   dynacert examples/capabilities/UnstablePlantRejected.mo
//   dynacert examples/capabilities/UnstablePlantRejected.mo validate --sample --n 50
model UnstablePlantRejected
  parameter Real a = 0.5 "Unstable pole [1/s]";
  parameter Real k = 0.2 "Feedback too weak to stabilize [1/s]";
  input Real d annotation(__Dynacert(disturbance(bound = 0.1)));
  Real x(start = 0, fixed = true) annotation(__Dynacert(certify));
equation
  der(x) = (a - k)*x + d;
end UnstablePlantRejected;
