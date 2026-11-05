// Two gravity-drained tanks in series; a pump fills the upper tank and a PI controller
// holds the lower-tank level. Linearized about the operating point of
// TwoTankLevelNonlinear.mo (h1 = 0.8 m, h2 = 0.9877 m, q0 = 0.4754 m3/min); the outflow
// sensitivities dq/dh = q0/(2h) come from the square-root (Torricelli) law.
// Illustrative laboratory-scale numbers; time in minutes. Disturbance: an unmeasured
// inflow into the upper tank. Deviation variables.
model TwoTankLevelLinearized
  parameter Real A1 = 0.5 "Upper tank cross-section [m2] (illustrative)";
  parameter Real A2 = 0.5 "Lower tank cross-section [m2] (illustrative)";
  parameter Real k1 = 0.2971 "Upper outflow sensitivity q0/(2*h1) [m2/min]";
  parameter Real k2 = 0.2407 "Lower outflow sensitivity q0/(2*h2) [m2/min]";
  parameter Real kp = 1.0 "PI proportional gain [m3/(min*m)]";
  parameter Real ki = 0.3 "PI integral gain [m3/(min2*m)]";

  input Real dqd "Unmeasured inflow into the upper tank [m3/min]" annotation(__Dynacert(disturbance(bound = 0.1)));

  Real dh1(start = 0, fixed = true) "Upper tank level deviation [m]" annotation(__Dynacert(certify));
  Real dh2(start = 0, fixed = true) "Lower tank level deviation [m]" annotation(__Dynacert(certify));
  Real z(start = 0, fixed = true) "Integral of lower level error [m*min]";
  Real dqp "Pump flow deviation [m3/min]" annotation(__Dynacert(certify));
equation
  dqp = -kp*dh2 - ki*z;
  der(z) = dh2;
  A1*der(dh1) = dqp + dqd - k1*dh1;
  A2*der(dh2) = k1*dh1 - k2*dh2;
end TwoTankLevelLinearized;
