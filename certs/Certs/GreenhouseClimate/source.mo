// Greenhouse air temperature regulated by a combined heating / ventilation-cooling
// actuator, linearized about the operating point; all variables are deviations.
// Illustrative values for a ~1000 m^2 glasshouse.
//
// Time in hours, energy in kWh, power in kW, temperature in K (deviation).
// Air:  Ca dTa/dt = -UA (Ta - To) - h (Ta - Ts) + Q + Qsun
// Soil / thermal mass:  Cs dTs/dt = h (Ta - Ts)
// The air-to-soil coupling h depends on canopy and soil moisture and is uncertain
// (A is affine in h; the disturbances enter through UA and 1/Ca, which are fixed).
// Controller: PI on the air temperature (integrator as a state); negative Q means
// ventilation cooling.
model GreenhouseClimate
  parameter Real Ca = 1.33 "Air heat capacity [kWh/K]";
  parameter Real Cs = 20.0 "Soil and structure heat capacity [kWh/K]";
  parameter Real UA = 9.0 "Cover heat loss conductance [kW/K]";
  parameter Real h = 5.0 "Air-to-soil conductance [kW/K]"
    annotation(__Dynacert(uncertain(min = 3.0, max = 7.0)));
  parameter Real kp = 40.0 "Proportional gain [kW/K]";
  parameter Real ki = 80.0 "Integral gain [kW/(K*h)]";

  input Real To "Outside temperature deviation [K]" annotation(__Dynacert(disturbance(bound = 5.0)));
  input Real Qsun "Absorbed solar power deviation [kW]" annotation(__Dynacert(disturbance(bound = 60.0)));

  Real Ta(start = 0, fixed = true) "Air temperature deviation [K]" annotation(__Dynacert(certify));
  Real Ts(start = 0, fixed = true) "Soil temperature deviation [K]" annotation(__Dynacert(certify));
  Real xi(start = 0, fixed = true) "Integral of the air temperature error [K*h]"
    annotation(__Dynacert(certify));
  Real Q "Net heating (+) / ventilation cooling (-) power [kW]";
equation
  Q = -kp*Ta - ki*xi;
  der(xi) = Ta;
  Ca*der(Ta) = -UA*(Ta - To) - h*(Ta - Ts) + Q + Qsun;
  Cs*der(Ts) = h*(Ta - Ts);
end GreenhouseClimate;
