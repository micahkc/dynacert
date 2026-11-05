// Greenhouse air temperature with the ventilation modelled physically: the heat removed by
// ventilation is Kv*(Ta - To), with the vent conductance Kv opened in proportion to the
// temperature error. Kv*(Ta - To) is bilinear (state times state / disturbance), so the
// closed loop is nonlinear and lmi does not apply: validation-only (montecarlo, falsify).
// Illustrative values matching GreenhouseClimate; absolute temperatures in degC.
// Kv is not clipped at zero here (a closed vent cannot go negative); the validation runs
// report whether that range is reached.
model GreenhouseVentilation
  parameter Real Ca = 1.33 "Air heat capacity [kWh/K]";
  parameter Real Cs = 20.0 "Soil and structure heat capacity [kWh/K]";
  parameter Real UA = 9.0 "Cover heat loss conductance [kW/K]";
  parameter Real h = 5.0 "Air-to-soil conductance [kW/K]";
  parameter Real Tset = 20.0 "Air temperature set point [degC]";
  parameter Real To0 = 10.0 "Nominal outside temperature [degC]";
  parameter Real Qs0 = 150.0 "Nominal absorbed solar power [kW]";
  parameter Real Kv0 = 10.0 "Nominal vent conductance [kW/K]";
  parameter Real kv = 3.0 "Vent opening gain [kW/K per K]";
  parameter Real kh = 30.0 "Heater proportional gain [kW/K]";
  parameter Real ki = 60.0 "Heater integral gain [kW/(K*h)]";
  parameter Real Q0 = 40.0 "Nominal heating power [kW]";

  input Real dTo "Outside temperature deviation [K]" annotation(__Dynacert(disturbance(bound = 5.0)));
  input Real dQs "Absorbed solar power deviation [kW]" annotation(__Dynacert(disturbance(bound = 60.0)));

  Real Ta(start = 20.0, fixed = true) "Air temperature [degC]";
  Real Ts(start = 20.0, fixed = true) "Soil temperature [degC]";
  Real xi(start = 0, fixed = true) "Integral of the air temperature error [K*h]";
  Real e "Air temperature error [K]" annotation(__Dynacert(certify));
  Real Kv "Vent conductance [kW/K]";
  Real Q "Heating power [kW]";
equation
  e = Ta - Tset;
  Kv = Kv0 + kv*e;
  Q = Q0 - kh*e - ki*xi;
  der(xi) = e;
  Ca*der(Ta) = -UA*(Ta - To0 - dTo) - Kv*(Ta - To0 - dTo) - h*(Ta - Ts) + Q + Qs0 + dQs;
  Cs*der(Ts) = h*(Ta - Ts);
end GreenhouseVentilation;
