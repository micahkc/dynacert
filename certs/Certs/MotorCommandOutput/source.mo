// DC motor speed loop with an algebraic certified output: the bound on the voltage command `u`
// comes from the state ellipsoid through the output row, and noise enters the dynamics only.
//
//   dynacert examples/capabilities/MotorCommandOutput.mo certify lmi
model MotorCommandOutput
  parameter Real R = 1.0 "Winding resistance [ohm]";
  parameter Real L = 0.5 "Inductance [H]";
  parameter Real Kt = 0.5 "Torque and back-EMF constant";
  parameter Real J = 0.1 "Inertia [kg m2]";
  parameter Real b = 0.1 "Viscous friction [N m s]";
  parameter Real kp = 2.0 "Speed gain [V s/rad]";
  input Real n "Voltage noise [V]" annotation(__Dynacert(disturbance(bound = 0.2)));
  input Real tl "Load torque [N m]" annotation(__Dynacert(disturbance(bound = 0.2)));
  Real i(start = 0, fixed = true) "Current deviation [A]";
  Real w(start = 0, fixed = true) "Speed deviation [rad/s]" annotation(__Dynacert(certify));
  Real u "Voltage command [V]" annotation(__Dynacert(certify));
equation
  u = -kp*w;
  L*der(i) = u + n - R*i - Kt*w;
  J*der(w) = Kt*i - b*w - tl;
end MotorCommandOutput;
