// Locomotive + car with an elastic coupler: speed regulation and coupler load.
//
// Two masses joined by a coupler spring/damper (draft gear). All variables are deviations
// from steady cruise. The locomotive's speed controller is PI on its own speed:
//   F_trac = -kv*dv_loco - ki*xi,   xi' = dv_loco
//   M_loco*dv_loco' = F_trac - F_c + F_g1
//   M_car *dv_car'  =          F_c + F_g2
//   s' = dv_loco - dv_car,   F_c = k_c*s + c_c*(dv_loco - dv_car)  (coupler force)
// F_g1, F_g2 are grade/wind force perturbations on each vehicle (bounded independently).
// Units: tonnes, kN, metres.
//
// Certified: the coupler force deviation, the coupler stretch and the locomotive speed
// deviation stay bounded for all grade/wind perturbations within the bounds.
// Values are illustrative (heavy-haul order of magnitude).
model TrainCouplerForce
  parameter Real M_loco = 120.0 "Locomotive mass [t]";
  parameter Real M_car = 100.0 "Car mass [t]";
  parameter Real k_c = 5000.0 "Coupler/draft-gear stiffness [kN/m]";
  parameter Real c_c = 50.0 "Coupler damping [kN*s/m]";
  parameter Real kv = 400.0 "Speed gain [kN*s/m]";
  parameter Real ki = 40.0 "Integral gain [kN/m]";

  input Real F_g1 "Grade/wind perturbation on locomotive [kN]"
    annotation(__Dynacert(disturbance(bound = 20.0)));
  input Real F_g2 "Grade/wind perturbation on car [kN]"
    annotation(__Dynacert(disturbance(bound = 20.0)));

  Real dv_loco(start = 0, fixed = true) "Locomotive speed deviation [m/s]"
    annotation(__Dynacert(certify));
  Real dv_car(start = 0, fixed = true) "Car speed deviation [m/s]";
  Real s(start = 0, fixed = true) "Coupler stretch deviation [m]"
    annotation(__Dynacert(certify));
  Real xi(start = 0, fixed = true) "Integral of locomotive speed deviation [m]";
  Real F_c "Coupler force deviation [kN]" annotation(__Dynacert(certify));
  Real F_trac "Traction force deviation [kN]";
equation
  F_trac = -kv*dv_loco - ki*xi;
  F_c = k_c*s + c_c*(dv_loco - dv_car);
  der(xi) = dv_loco;
  der(s) = dv_loco - dv_car;
  M_loco*der(dv_loco) = F_trac - F_c + F_g1;
  M_car*der(dv_car) = F_c + F_g2;
end TrainCouplerForce;
