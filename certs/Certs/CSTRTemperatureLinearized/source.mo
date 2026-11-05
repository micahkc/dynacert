// Exothermic CSTR (first-order reaction A -> B) with PI temperature control through the
// coolant temperature, linearized about the steady state of CSTRArrheniusPI.mo
// (Ca = 0.8773 mol/L, T = 324.48 K, Tc = 300 K). Illustrative textbook-style benchmark
// numbers; the Jacobian entries below are computed from that nonlinear model
// (rounded to 4 significant figures). Time in minutes. Disturbances: feed temperature
// and feed concentration deviations.
model CSTRTemperatureLinearized
  parameter Real a11 = -1.140 "d(dCa')/d(dCa) [1/min]";
  parameter Real a12 = -0.01020 "d(dCa')/d(dT) [mol/(L*K*min)]";
  parameter Real a21 = 29.27 "d(dT')/d(dCa) [K*L/(mol*min)]";
  parameter Real a22 = -0.9579 "d(dT')/d(dT) [1/min]";
  parameter Real bc = 2.092 "d(dT')/d(dTc) = UA/(V*rho*Cp) [1/min]";
  parameter Real qV = 1.0 "Dilution rate q/V [1/min]";
  parameter Real kp = 2.0 "PI proportional gain [K/K]";
  parameter Real ki = 1.0 "PI integral gain [K/(K*min)]";

  input Real dTf "Feed temperature deviation [K]" annotation(__Dynacert(disturbance(bound = 5.0)));
  input Real dCaf "Feed concentration deviation [mol/L]" annotation(__Dynacert(disturbance(bound = 0.1)));

  Real dCa(start = 0, fixed = true) "Concentration deviation [mol/L]" annotation(__Dynacert(certify));
  Real dT(start = 0, fixed = true) "Reactor temperature deviation [K]" annotation(__Dynacert(certify));
  Real z(start = 0, fixed = true) "Integral of temperature error [K*min]";
  Real dTc "Coolant temperature deviation (manipulated) [K]" annotation(__Dynacert(certify));
equation
  dTc = -kp*dT - ki*z;
  der(z) = dT;
  der(dCa) = a11*dCa + a12*dT + qV*dCaf;
  der(dT) = a21*dCa + a22*dT + bc*dTc + qV*dTf;
end CSTRTemperatureLinearized;
