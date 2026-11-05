// Quaternion attitude kinematics under a rate command, with an array state. No certify method
// handles this form yet; `structure` reports what it finds, and evidence still runs.
//
//   dynacert examples/capabilities/QuaternionAttitudeReport.mo structure
//   dynacert examples/capabilities/QuaternionAttitudeReport.mo validate --sample --n 100
model QuaternionAttitudeReport
  parameter Real k = 2.0 "Attitude gain [1/s]";
  input Real d[3] "Rate error [rad/s]" annotation(__Dynacert(disturbance(bound = 0.05)));
  Real q[4](start = {1, 0, 0, 0}, each fixed = true) "Attitude quaternion";
  Real w[3] "Body rate [rad/s]";
  Real e1 "Attitude error, x" annotation(__Dynacert(certify));
equation
  w = -k*{q[2], q[3], q[4]} + d;
  e1 = q[2];
  der(q[1]) = 0.5*(-q[2]*w[1] - q[3]*w[2] - q[4]*w[3]);
  der(q[2]) = 0.5*( q[1]*w[1] - q[4]*w[2] + q[3]*w[3]);
  der(q[3]) = 0.5*( q[4]*w[1] + q[1]*w[2] - q[2]*w[3]);
  der(q[4]) = 0.5*(-q[3]*w[1] + q[2]*w[2] + q[1]*w[3]);
end QuaternionAttitudeReport;
