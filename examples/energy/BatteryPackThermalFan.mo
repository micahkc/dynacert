// Battery pack thermal management with a cooling fan (linearized about an operating
// point; illustrative numbers for a small air-cooled pack). Two thermal nodes (cells,
// pack air) plus a first-order fan-speed response; a PI controller drives the fan from
// the cell temperature deviation. Disturbances: cell heat generation (drive-cycle
// current) and ambient temperature. Deviation variables; time in minutes, heat in W*min
// units so that C [J/K] / 60 appears as C_min [W*min/K].
model BatteryPackThermalFan
  parameter Real Cc = 800.0 "Cell thermal capacitance [W*min/K] (48 kJ/K, illustrative)";
  parameter Real Ca = 20.0 "Pack air thermal capacitance [W*min/K] (illustrative)";
  parameter Real Gca = 40.0 "Cell-to-air conductance [W/K] (illustrative)";
  parameter Real Gaa = 30.0 "Air-to-ambient conductance at nominal fan speed [W/K] (illustrative)";
  parameter Real kfan = 10.0 "Extra cooling per unit fan speed (linearized) [W/%] (illustrative)";
  parameter Real tfan = 0.1 "Fan speed time constant [min] (illustrative)";
  parameter Real kp = 20.0 "PI proportional gain [%/K]";
  parameter Real ki = 2.0 "PI integral gain [%/(K*min)]";

  input Real dQ "Cell heat generation deviation [W]" annotation(__Dynacert(disturbance(bound = 100.0)));
  input Real dTamb "Ambient temperature deviation [K]" annotation(__Dynacert(disturbance(bound = 5.0)));

  Real dTc(start = 0, fixed = true) "Cell temperature deviation [K]" annotation(__Dynacert(certify));
  Real dTa(start = 0, fixed = true) "Pack air temperature deviation [K]";
  Real dfan(start = 0, fixed = true) "Fan speed deviation [%]" annotation(__Dynacert(certify));
  Real z(start = 0, fixed = true) "Integral of cell temperature deviation [K*min]";
  Real fan_cmd "Fan speed command deviation [%]";
equation
  fan_cmd = kp*dTc + ki*z;
  der(z) = dTc;
  Cc*der(dTc) = dQ - Gca*(dTc - dTa);
  Ca*der(dTa) = Gca*(dTc - dTa) - Gaa*(dTa - dTamb) - kfan*dfan;
  tfan*der(dfan) = fan_cmd - dfan;
end BatteryPackThermalFan;
