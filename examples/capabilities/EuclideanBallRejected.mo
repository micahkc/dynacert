// A Euclidean-ball disturbance on an array, `norm = "2"`: not supported yet. dynacert rejects it
// with a message instead of silently reading it as a per-component box.
//
//   dynacert examples/capabilities/EuclideanBallRejected.mo
model EuclideanBallRejected
  parameter Real k = 2.0;
  input Real d[2] annotation(__Dynacert(disturbance(bound = 1.0, norm = "2")));
  Real x[2](each start = 0, each fixed = true) annotation(__Dynacert(certify));
equation
  der(x) = -k*x + d;
end EuclideanBallRejected;
