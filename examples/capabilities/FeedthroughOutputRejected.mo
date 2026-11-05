// A certified output that reads a disturbance directly (y = C z + D w). This is not supported yet,
// so every linear method rejects it by name. MotorCommandOutput is the same motor with a
// certifiable output.
//
//   dynacert examples/capabilities/FeedthroughOutputRejected.mo
model FeedthroughOutputRejected
  parameter Real R = 1.0 "Winding resistance [ohm]";
  parameter Real Kt = 0.5 "Torque and back-EMF constant";
  parameter Real J = 0.1 "Inertia [kg m2]";
  parameter Real b = 0.1 "Viscous friction [N m s]";
  parameter Real kp = 2.0 "Speed gain [V s/rad]";
  input Real n "Speed sensor noise [rad/s]" annotation(__Dynacert(disturbance(bound = 0.1)));
  Real i(start = 0, fixed = true) "Current deviation [A]";
  Real w(start = 0, fixed = true) "Speed deviation [rad/s]";
  Real u "Voltage command [V]" annotation(__Dynacert(certify));
equation
  u = -kp*(w + n);
  der(i) = 2*(u - R*i - Kt*w);
  J*der(w) = Kt*i - b*w;
end FeedthroughOutputRejected;
