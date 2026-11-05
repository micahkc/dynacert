// Chilled-water plant: chiller evaporator leaving-water (supply) temperature control.
// Evaporator water volume and the distribution loop/building coils are lumped thermal
// nodes; chiller capacity follows its command with a first-order lag; a PI loop sets the
// capacity from the supply-temperature error. Illustrative numbers; time in minutes,
// heat in kW, capacitances in kW*min/K. Disturbance: building cooling load.
// Deviation variables.
model ChilledWaterSupplyPI
  parameter Real Me = 300.0 "Evaporator water capacitance [kW*min/K] (~4.3 m3, illustrative)";
  parameter Real Ml = 1500.0 "Loop and coil water capacitance [kW*min/K] (illustrative)";
  parameter Real mc = 200.0 "Chilled-water flow times cp [kW/K] (~48 kg/s, illustrative)";
  parameter Real tch = 2.0 "Chiller capacity time constant [min] (illustrative)";
  parameter Real kp = 300.0 "PI proportional gain [kW/K]";
  parameter Real ki = 100.0 "PI integral gain [kW/(K*min)]";

  input Real dQload "Building cooling load deviation [kW]" annotation(__Dynacert(disturbance(bound = 200.0)));

  Real dTs(start = 0, fixed = true) "Supply water temperature deviation [K]" annotation(__Dynacert(certify));
  Real dTr(start = 0, fixed = true) "Return water temperature deviation [K]" annotation(__Dynacert(certify));
  Real dQch(start = 0, fixed = true) "Chiller capacity deviation [kW]" annotation(__Dynacert(certify));
  Real z(start = 0, fixed = true) "Integral of supply temperature error [K*min]";
  Real dQcmd "Chiller capacity command deviation [kW]";
equation
  dQcmd = kp*dTs + ki*z;
  der(z) = dTs;
  Me*der(dTs) = mc*(dTr - dTs) - dQch;
  Ml*der(dTr) = mc*(dTs - dTr) + dQload;
  tch*der(dQch) = dQcmd - dQch;
end ChilledWaterSupplyPI;
