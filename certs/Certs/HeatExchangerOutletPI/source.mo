// Steam/hot-utility heated exchanger: lumped tube-side fluid temperature with PI control
// of the outlet temperature through a hot-side temperature actuator (mixing valve with a
// first-order lag). Illustrative numbers; time in seconds. The overall heat-transfer
// coefficient UA degrades with fouling, so it is uncertain (+/- 30 %); the claim holds
// for every UA in the range. Disturbance: process inlet temperature. Deviation variables.
model HeatExchangerOutletPI
  parameter Real Mc = 400.0 "Tube-side thermal capacitance M*cp [kJ/K] (illustrative)";
  parameter Real Fc = 20.0 "Process flow times cp [kW/K] (illustrative)";
  parameter Real UA = 30.0 "Overall heat transfer coefficient times area [kW/K] (illustrative)"
    annotation(__Dynacert(uncertain(min = 21.0, max = 39.0)));
  parameter Real tv = 5.0 "Hot-side actuator time constant [s] (illustrative)";
  parameter Real kp = 1.5 "PI proportional gain [K/K]";
  parameter Real ki = 0.05 "PI integral gain [K/(K*s)]";

  input Real dTin "Process inlet temperature deviation [K]" annotation(__Dynacert(disturbance(bound = 5.0)));

  Real dT(start = 0, fixed = true) "Outlet temperature deviation [K]" annotation(__Dynacert(certify));
  Real dTh(start = 0, fixed = true) "Hot-side temperature deviation [K]" annotation(__Dynacert(certify));
  Real z(start = 0, fixed = true) "Integral of outlet temperature error [K*s]";
  Real dTh_cmd "Hot-side temperature command [K]";
equation
  dTh_cmd = -kp*dT - ki*z;
  der(z) = dT;
  Mc*der(dT) = Fc*(dTin - dT) + UA*(dTh - dT);
  tv*der(dTh) = dTh_cmd - dTh;
end HeatExchangerOutletPI;
