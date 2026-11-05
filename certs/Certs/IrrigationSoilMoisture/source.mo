// Closed-loop irrigation of a two-layer soil profile; deviations from the target moisture.
// Illustrative values for a loam with a 300 mm root zone over a 600 mm subsoil layer.
//
// Time in days, water in mm, moisture in volumetric percent (1 mm over 300 mm = 1/3 %).
// Irrigation delivery (pump, canal and infiltration) is a first-order lag of 0.25 day.
// Drainage from the root zone, kperc*theta1, depends on soil texture and is uncertain
// (A is affine in kperc). The disturbance is the deviation of crop evapotranspiration
// from its forecast. Controller: PI on the root-zone moisture deviation.
model IrrigationSoilMoisture
  parameter Real Z1 = 3.0 "Root zone storage per % moisture (300 mm) [mm/%]";
  parameter Real Z2 = 6.0 "Subsoil storage per % moisture (600 mm) [mm/%]";
  parameter Real kperc = 2.0 "Root-zone drainage coefficient [mm/day per %]"
    annotation(__Dynacert(uncertain(min = 1.0, max = 3.0)));
  parameter Real kx = 0.5 "Capillary exchange between layers [mm/day per %]";
  parameter Real kdeep = 1.0 "Deep drainage from the subsoil [mm/day per %]";
  parameter Real tau = 0.25 "Irrigation delivery time constant [day]";
  parameter Real kp = 4.0 "Proportional gain [mm/day per %]";
  parameter Real ki = 2.0 "Integral gain [mm/day per %*day]";

  input Real dET "Evapotranspiration deviation from forecast [mm/day]"
    annotation(__Dynacert(disturbance(bound = 3.0)));

  Real th1(start = 0, fixed = true) "Root-zone moisture deviation [%]" annotation(__Dynacert(certify));
  Real th2(start = 0, fixed = true) "Subsoil moisture deviation [%]" annotation(__Dynacert(certify));
  Real w(start = 0, fixed = true) "Delivered irrigation rate deviation [mm/day]"
    annotation(__Dynacert(certify));
  Real xi(start = 0, fixed = true) "Integral of the root-zone deviation [%*day]"
    annotation(__Dynacert(certify));
  Real u "Irrigation command deviation [mm/day]";
equation
  u = -kp*th1 - ki*xi;
  der(xi) = th1;
  tau*der(w) = -w + u;
  Z1*der(th1) = w - dET - kperc*th1 - kx*(th1 - th2);
  Z2*der(th2) = kperc*th1 + kx*(th1 - th2) - kdeep*th2;
end IrrigationSoilMoisture;
