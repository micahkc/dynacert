// RoomThermalPI with a physical heater: total heater power is limited to [0, Qmax] and
// the PI integrator uses back-calculation anti-windup (validation only). The saturation
// makes the closed loop nonlinear (piecewise), so the LMI certificate does not apply;
// montecarlo and falsify still run. Absolute temperatures in degC; time in hours, heat in
// kW. Illustrative numbers matching RoomThermalPI at Ca = 1 kWh/K.
model RoomThermalSaturatedPI
  parameter Real Ca = 1.0 "Air-node capacitance [kWh/K]";
  parameter Real Ce = 8.0 "Envelope capacitance [kWh/K]";
  parameter Real Rae = 0.5 "Air-to-envelope resistance [K/kW]";
  parameter Real Reo = 2.0 "Envelope-to-outdoor resistance [K/kW]";
  parameter Real To0 = 0.0 "Nominal outdoor temperature [degC]";
  parameter Real Tsp = 20.0 "Room setpoint [degC]";
  parameter Real Q0 = 8.0 "Steady heater power at To0 [kW] = (Tsp - To0)/(Rae + Reo)";
  parameter Real Qmax = 11.0 "Heater rating [kW] (illustrative; a 10 K cold snap needs 12 kW)";
  parameter Real kaw = 0.5 "Back-calculation anti-windup gain [1/(kW*h)]";
  parameter Real kp = 4.0 "PI proportional gain [kW/K]";
  parameter Real ki = 4.0 "PI integral gain [kW/(K*h)]";

  input Real dTo "Outdoor temperature deviation [K]" annotation(__Dynacert(disturbance(bound = 10.0)));

  Real Ta(start = 20.0, fixed = true) "Room air temperature [degC]";
  Real Te(start = 16.0, fixed = true) "Envelope temperature [degC]";
  Real z(start = 0, fixed = true) "Integral of room temperature error [K*h]";
  Real Qcmd "Unsaturated heater command [kW]";
  Real Q "Heater power [kW]";
  Real e "Room temperature error [K]" annotation(__Dynacert(certify));
equation
  e = Ta - Tsp;
  Qcmd = Q0 - kp*e - ki*z;
  Q = min(max(Qcmd, 0.0), Qmax);
  // An if-expression anti-windup (der(z) = if ... then 0 else e) is rejected by rumoca's
  // lean-dae target (no event support), which stops even montecarlo; min/max is accepted.
  der(z) = e + kaw*(Qcmd - Q);
  Ca*der(Ta) = (Te - Ta)/Rae + Q;
  Ce*der(Te) = (Ta - Te)/Rae + (To0 + dTo - Te)/Reo;
end RoomThermalSaturatedPI;
