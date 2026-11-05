// Nonlinear two-tank level control (validation only): Torricelli outflows
// q = a*sqrt(2*g*h), a pump with PI control of the lower-tank level, and an unmeasured
// inflow disturbance. Illustrative laboratory-scale numbers; time in minutes (so g is in
// m/min2). The sqrt makes the dynamics nonlinear, so the LMI certificate does not apply;
// montecarlo and falsify still run. Its linearization is certified in
// TwoTankLevelLinearized.mo.
model TwoTankLevelNonlinear
  parameter Real A1 = 0.5 "Upper tank cross-section [m2]";
  parameter Real A2 = 0.5 "Lower tank cross-section [m2]";
  parameter Real a1 = 0.002 "Upper outlet area [m2]";
  parameter Real a2 = 0.0018 "Lower outlet area [m2]";
  parameter Real g = 35316.0 "Gravity [m/min2] (9.81 m/s2)";
  parameter Real q0 = 0.4754 "Nominal pump flow [m3/min]";
  parameter Real h2sp = 0.9877 "Lower level setpoint [m]";
  parameter Real kp = 1.0 "PI proportional gain [m3/(min*m)]";
  parameter Real ki = 0.3 "PI integral gain [m3/(min2*m)]";

  input Real dqd "Unmeasured inflow into the upper tank [m3/min]" annotation(__Dynacert(disturbance(bound = 0.1)));

  Real h1(start = 0.8, fixed = true) "Upper tank level [m]";
  Real h2(start = 0.9877, fixed = true) "Lower tank level [m]";
  Real z(start = 0, fixed = true) "Integral of lower level error [m*min]";
  Real qp "Pump flow [m3/min]";
  Real e "Lower level error [m]" annotation(__Dynacert(certify));
equation
  e = h2 - h2sp;
  qp = q0 - kp*e - ki*z;
  der(z) = e;
  A1*der(h1) = qp + dqd - a1*sqrt(2*g*h1);
  A2*der(h2) = a1*sqrt(2*g*h1) - a2*sqrt(2*g*h2);
end TwoTankLevelNonlinear;
