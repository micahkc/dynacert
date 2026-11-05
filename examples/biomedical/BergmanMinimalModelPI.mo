// ILLUSTRATIVE, NOT CLINICAL. The same PI insulin controller as GlucoseInsulinPI, closed
// around the nonlinear Bergman minimal model (glucose disappearance X*G is bilinear).
// Parameter values are order-of-magnitude illustrations, not patient data.
//
// Time in hours; absolute glucose G [mg/dL], remote insulin action Xs [1e-4/min] (zero at
// basal), insulin deviation I [uU/mL]. The total infusion ub + u cannot be negative; it is
// clipped smoothly, u_tot = (v + sqrt(v^2 + s^2))/2 with v = ub + u
// (no events, so the simulators stay smooth).
// Without this clip, falsify found a destabilising scenario: the PI commanded negative
// insulin, Xs went far below zero, and -cX*Xs*G turned into exponential glucose growth
// (|G - Gb| ~ 700 mg/dL within 10 h).
//
// The bilinear term makes the model nonlinear: lmi does not apply. Validation-only
// (montecarlo, falsify); compare with the linear certificate of GlucoseInsulinPI.
model BergmanMinimalModelPI
  parameter Real Gb = 100.0 "Basal glucose [mg/dL]";
  parameter Real p1 = 1.8 "Glucose effectiveness (0.03/min) [1/h]";
  parameter Real p2 = 1.2 "Remote insulin decay (0.02/min) [1/h]";
  parameter Real p3s = 7.8 "Remote insulin gain, rescaled [(1e-4/min)/(h*uU/mL)]";
  parameter Real n = 5.4 "Insulin clearance (0.09/min) [1/h]";
  parameter Real VI = 12.0 "Insulin distribution volume [L]";
  parameter Real cX = 0.006 "Rescaling of X*G: 1e-4/min * 60 min/h [1/h per Xs]";
  parameter Real ub = 648.0 "Basal infusion n*Ib*VI with Ib = 10 uU/mL [mU/h]";
  parameter Real s = 10.0 "Smoothing width of the clip at zero infusion [mU/h]";
  parameter Real kp = 60.0 "Proportional gain [mU/h per mg/dL]";
  parameter Real ki = 30.0 "Integral gain [mU/h per mg/dL*h]";

  input Real Ra "Meal glucose appearance rate (deviation) [mg/dL/h]"
    annotation(__Dynacert(disturbance(bound = 180.0)));

  Real G(start = 100.0, fixed = true) "Plasma glucose [mg/dL]";
  Real Xs(start = 0, fixed = true) "Remote insulin action [1e-4/min]";
  Real I(start = 0, fixed = true) "Plasma insulin deviation from basal [uU/mL]";
  Real xi(start = 0, fixed = true) "Integral of the glucose error [mg/dL*h]";
  Real eG "Glucose deviation from basal [mg/dL]" annotation(__Dynacert(certify));
  Real u "PI command above basal [mU/h]";
  Real u_tot "Delivered infusion, smoothly clipped at zero [mU/h]";
equation
  eG = G - Gb;
  u = kp*eG + ki*xi;
  der(xi) = eG;
  der(G) = -p1*(G - Gb) - cX*Xs*G + Ra;
  der(Xs) = -p2*Xs + p3s*I;
  u_tot = 0.5*((ub + u) + sqrt((ub + u)^2 + s^2));
  der(I) = -n*I + (u_tot - ub)/VI;
end BergmanMinimalModelPI;
