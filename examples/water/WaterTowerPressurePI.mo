// Municipal pressure zone fed by a variable-speed pump into an elevated storage tank;
// zone pressure follows the tank level (hydrostatic head). A PI controller sets the pump
// speed from the pressure deviation. The pump flow is linearized in speed and in head
// (pump curve slope). Illustrative numbers; time in minutes. Disturbance: zone demand.
// Deviation variables.
model WaterTowerPressurePI
  parameter Real At = 200.0 "Tank cross-section [m2] (illustrative)";
  parameter Real kn = 0.3 "Pump flow sensitivity to speed [m3/(min*%)] (illustrative)";
  parameter Real kh = 2.0 "Pump flow sensitivity to head (curve slope) [m3/(min*m)] (illustrative)";
  parameter Real tvfd = 0.2 "VFD speed time constant [min] (illustrative)";
  parameter Real rhog = 9.81 "rho*g [kPa/m]";
  parameter Real kp = 2.0 "PI proportional gain [%/kPa]";
  parameter Real ki = 0.2 "PI integral gain [%/(kPa*min)]";

  input Real dqdem "Zone demand deviation [m3/min]" annotation(__Dynacert(disturbance(bound = 5.0)));

  Real dh(start = 0, fixed = true) "Tank level deviation [m]";
  Real dn(start = 0, fixed = true) "Pump speed deviation [%]" annotation(__Dynacert(certify));
  Real z(start = 0, fixed = true) "Integral of pressure error [kPa*min]";
  Real dp "Zone pressure deviation [kPa]" annotation(__Dynacert(certify));
  Real dncmd "Pump speed command deviation [%]";
equation
  dp = rhog*dh;
  dncmd = -kp*dp - ki*z;
  der(z) = dp;
  tvfd*der(dn) = dncmd - dn;
  At*der(dh) = kn*dn - kh*dh - dqdem;
end WaterTowerPressurePI;
