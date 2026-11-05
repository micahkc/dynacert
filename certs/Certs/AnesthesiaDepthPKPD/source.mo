// ILLUSTRATIVE, NOT CLINICAL. Closed-loop hypnotic (propofol-like) infusion regulating the
// effect-site concentration with a three-compartment pharmacokinetic model and an
// effect-site compartment. Rate constants are order-of-magnitude illustrations in the
// range of published adult models; they are not a validated patient model and must not be
// used for dosing.
//
// Time in HOURS (the per-minute rates are multiplied by 60). Hours are used because the
// slow peripheral compartment (k31 = 0.0033/min) gives a closed-loop pole near
// -0.0033/min, below the smallest decay rate (0.02 per time unit) the lmi search tries.
//
// Variables are deviations from the maintenance steady state (which itself depends on the
// patient's clearance): drug amounts A1..A3 [mg], effect-site concentration Ce
// [ug/mL = mg/L]. Inter-patient variability: elimination k10 and effect-site equilibration
// ke0 are uncertain (A is affine in each). The disturbance is an infusion-pump delivery
// error. Controller: PI on the effect-site deviation.
model AnesthesiaDepthPKPD
  parameter Real k10 = 7.2 "Elimination rate (0.12/min) [1/h]"
    annotation(__Dynacert(uncertain(min = 4.8, max = 9.6)));
  parameter Real ke0 = 18.0 "Effect-site equilibration rate (0.3/min) [1/h]"
    annotation(__Dynacert(uncertain(min = 12.0, max = 24.0)));
  parameter Real k12 = 6.72 "Central to fast peripheral (0.112/min) [1/h]";
  parameter Real k21 = 3.3 "Fast peripheral to central (0.055/min) [1/h]";
  parameter Real k13 = 2.52 "Central to slow peripheral (0.042/min) [1/h]";
  parameter Real k31 = 0.198 "Slow peripheral to central (0.0033/min) [1/h]";
  parameter Real V1 = 16.0 "Central volume [L]";
  parameter Real kp = 2400.0 "Proportional gain (40 mg/min per ug/mL) [mg/h per ug/mL]";
  parameter Real ki = 14400.0 "Integral gain (4 mg/min per ug/mL*min) [mg/h per ug/mL*h]";

  input Real d_pump "Infusion delivery error (0.5 mg/min) [mg/h]"
    annotation(__Dynacert(disturbance(bound = 30.0)));

  Real A1(start = 0, fixed = true) "Central amount deviation [mg]" annotation(__Dynacert(certify));
  Real A2(start = 0, fixed = true) "Fast peripheral amount deviation [mg]" annotation(__Dynacert(certify));
  Real A3(start = 0, fixed = true) "Slow peripheral amount deviation [mg]" annotation(__Dynacert(certify));
  Real Ce(start = 0, fixed = true) "Effect-site concentration deviation [ug/mL]"
    annotation(__Dynacert(certify));
  Real xi(start = 0, fixed = true) "Integral of the effect-site deviation [ug/mL*h]"
    annotation(__Dynacert(certify));
  Real u "Infusion rate deviation [mg/h]";
equation
  u = -kp*Ce - ki*xi;
  der(xi) = Ce;
  der(A1) = -(k10 + k12 + k13)*A1 + k21*A2 + k31*A3 + u + d_pump;
  der(A2) = k12*A1 - k21*A2;
  der(A3) = k13*A1 - k31*A3;
  der(Ce) = ke0*(A1/V1 - Ce);
end AnesthesiaDepthPKPD;
