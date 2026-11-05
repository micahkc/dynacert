// One-area power system load-frequency control (illustrative per-unit parameters).
// Swing equation (aggregated inertia), first-order governor-turbine with droop, and
// integral AGC acting on the area control error (ACE = beta * df for an isolated area).
// All quantities are deviations from the scheduled operating point, so the error frame
// is the state itself (no reference). The load step dPL is the disturbance.
model GridFrequencyDroopAGC
  parameter Real H = 5.0 "Inertia constant [s] (illustrative)";
  parameter Real D = 1.0 "Load damping [pu power / pu frequency] (illustrative)";
  parameter Real Tg = 0.5 "Governor-turbine time constant [s] (illustrative)";
  parameter Real R = 0.05 "Droop [pu frequency / pu power] (5 %, illustrative)";
  parameter Real beta = 21.0 "Frequency bias D + 1/R [pu/pu]";
  parameter Real Ki = 0.3 "AGC integral gain [1/s] (illustrative)";

  input Real dPL "Load step deviation [pu]" annotation(__Dynacert(disturbance(bound = 0.1)));

  Real df(start = 0, fixed = true) "Frequency deviation [pu]" annotation(__Dynacert(certify));
  Real dPm(start = 0, fixed = true) "Mechanical power deviation [pu]" annotation(__Dynacert(certify));
  Real dPc(start = 0, fixed = true) "AGC setpoint deviation [pu]" annotation(__Dynacert(certify));
  Real ace "Area control error [pu]";
equation
  ace = beta*df;
  2*H*der(df) = dPm - dPL - D*df;
  Tg*der(dPm) = -dPm + dPc - df/R;
  der(dPc) = -Ki*ace;
end GridFrequencyDroopAGC;
