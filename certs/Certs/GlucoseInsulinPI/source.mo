// ILLUSTRATIVE, NOT CLINICAL. Closed-loop insulin infusion (artificial-pancreas style)
// on the Bergman minimal model linearized about the basal state. Parameter values are
// order-of-magnitude illustrations, not patient data, and must not be used for dosing.
//
// Time in hours. All variables are deviations from basal:
//   G  plasma glucose [mg/dL], Xs remote insulin action [1e-4/min], I plasma insulin [uU/mL].
// Linearization at G = Gb: dG/dt = -p1 G - Gb X + Ra, with X rescaled to Xs = 1e4 X
// (and rates converted from 1/min to 1/h) so that every coefficient is of order one.
// Controller: PI on the glucose deviation, u = kp G + ki int(G) [mU/h of insulin on top of
// the basal rate]. The meal is a bounded glucose appearance rate Ra.
model GlucoseInsulinPI
  parameter Real p1 = 1.8 "Glucose effectiveness (0.03/min) [1/h]";
  parameter Real p2 = 1.2 "Remote insulin decay (0.02/min) [1/h]";
  parameter Real p3s = 7.8 "Remote insulin gain, rescaled [(1e-4/min)/(h*uU/mL)]";
  parameter Real n = 5.4 "Insulin clearance (0.09/min) [1/h]";
  parameter Real VI = 12.0 "Insulin distribution volume [L]";
  parameter Real GbX = 0.6 "Gb times the X rescaling, 100 mg/dL * 1e-4/min * 60 min/h [mg/dL/h per Xs]";
  parameter Real kp = 60.0 "Proportional gain [mU/h per mg/dL]";
  parameter Real ki = 30.0 "Integral gain [mU/h per mg/dL*h]";

  input Real Ra "Meal glucose appearance rate (deviation) [mg/dL/h]"
    annotation(__Dynacert(disturbance(bound = 180.0)));

  Real G(start = 0, fixed = true) "Glucose deviation from basal [mg/dL]"
    annotation(__Dynacert(certify));
  Real Xs(start = 0, fixed = true) "Remote insulin action deviation [1e-4/min]"
    annotation(__Dynacert(certify));
  Real I(start = 0, fixed = true) "Plasma insulin deviation [uU/mL]"
    annotation(__Dynacert(certify));
  Real xi(start = 0, fixed = true) "Integral of the glucose deviation [mg/dL*h]"
    annotation(__Dynacert(certify));
  Real u "Insulin infusion above basal [mU/h]";
equation
  u = kp*G + ki*xi;
  der(xi) = G;
  der(G) = -p1*G - GbX*Xs + Ra;
  der(Xs) = -p2*Xs + p3s*I;
  der(I) = -n*I + u/VI;
end GlucoseInsulinPI;
