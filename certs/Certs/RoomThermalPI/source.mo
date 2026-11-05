// Two-node RC thermal model of a room (air + furniture node, building envelope node) with
// a PI-controlled heater, illustrative numbers for a single office. Time in hours, heat in
// kW, capacitances in kWh/K. The outdoor temperature deviation drives the envelope.
// The air-node capacitance is uncertain (furniture, occupancy). The certificate needs the
// state matrix to be affine in uncertain parameters, and C appears as 1/C, so the uncertain
// parameter is the inverse capacitance invCa = 1/Ca in [1/1.5, 1/0.5] 1/(kWh/K)
// (Ca between 0.5 and 1.5 kWh/K). Deviations from a constant setpoint.
model RoomThermalPI
  parameter Real invCa = 1.0 "Inverse air-node capacitance 1/Ca [K/kWh] (Ca = 1 kWh/K nominal)"
    annotation(__Dynacert(uncertain(min = 0.6667, max = 2.0)));
  parameter Real Ce = 8.0 "Envelope capacitance [kWh/K] (illustrative)";
  parameter Real Rae = 0.5 "Air-to-envelope resistance [K/kW] (illustrative)";
  parameter Real Reo = 2.0 "Envelope-to-outdoor resistance [K/kW] (illustrative)";
  parameter Real kp = 4.0 "PI proportional gain [kW/K]";
  parameter Real ki = 4.0 "PI integral gain [kW/(K*h)]";

  input Real dTo "Outdoor temperature deviation [K]" annotation(__Dynacert(disturbance(bound = 10.0)));

  Real dTa(start = 0, fixed = true) "Room air temperature deviation from setpoint [K]" annotation(__Dynacert(certify));
  Real dTe(start = 0, fixed = true) "Envelope temperature deviation [K]";
  Real z(start = 0, fixed = true) "Integral of room temperature error [K*h]";
  Real dQ "Heater power deviation [kW]" annotation(__Dynacert(certify));
equation
  dQ = -kp*dTa - ki*z;
  der(z) = dTa;
  // dQ is written out here instead of referenced: with `invCa*(... + dQ)` the generated
  // link proof fails (`linear_combination` needs the dQ equation scaled by invCa; a
  // dynacert emitter issue).
  der(dTa) = invCa*((dTe - dTa)/Rae - kp*dTa - ki*z);
  Ce*der(dTe) = (dTa - dTe)/Rae + (dTo - dTe)/Reo;
end RoomThermalPI;
