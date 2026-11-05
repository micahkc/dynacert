// Nonlinear exothermic CSTR with Arrhenius kinetics and PI coolant-temperature control
// (validation only). Illustrative textbook-style benchmark parameters; time in minutes.
// The exp(-E/(R*T)) rate makes the error dynamics nonlinear, so the LMI certificate does
// not apply; montecarlo and falsify still run. Its linearization at the operating point
// is certified in CSTRTemperatureLinearized.mo.
model CSTRArrheniusPI
  parameter Real q = 100.0 "Feed flow [L/min]";
  parameter Real V = 100.0 "Reactor volume [L]";
  parameter Real rho = 1000.0 "Density [g/L]";
  parameter Real Cp = 0.239 "Heat capacity [J/(g*K)]";
  parameter Real dH = -5.0e4 "Heat of reaction [J/mol]";
  parameter Real EoverR = 8750.0 "Activation temperature E/R [K]";
  parameter Real k0 = 7.2e10 "Pre-exponential factor [1/min]";
  parameter Real UA = 5.0e4 "Heat transfer coefficient times area [J/(min*K)]";
  parameter Real Caf0 = 1.0 "Nominal feed concentration [mol/L]";
  parameter Real Tf0 = 350.0 "Nominal feed temperature [K]";
  parameter Real Tc0 = 300.0 "Nominal coolant temperature [K]";
  parameter Real Tsp = 324.4754 "Temperature setpoint (steady state at Tc0) [K]";
  parameter Real kp = 2.0 "PI proportional gain [K/K]";
  parameter Real ki = 1.0 "PI integral gain [K/(K*min)]";

  input Real dTf "Feed temperature deviation [K]" annotation(__Dynacert(disturbance(bound = 5.0)));
  input Real dCaf "Feed concentration deviation [mol/L]" annotation(__Dynacert(disturbance(bound = 0.1)));

  Real Ca(start = 0.8772529, fixed = true) "Concentration of A [mol/L]";
  Real T(start = 324.4754, fixed = true) "Reactor temperature [K]";
  Real z(start = 0, fixed = true) "Integral of temperature error [K*min]";
  Real Tc "Coolant temperature (manipulated) [K]";
  Real rate "Reaction rate [mol/(L*min)]";
  Real e "Temperature error [K]" annotation(__Dynacert(certify));
equation
  e = T - Tsp;
  Tc = Tc0 - kp*e - ki*z;
  der(z) = e;
  rate = k0*exp(-EoverR/T)*Ca;
  der(Ca) = q/V*(Caf0 + dCaf - Ca) - rate;
  der(T) = q/V*(Tf0 + dTf - T) - dH/(rho*Cp)*rate + UA/(V*rho*Cp)*(Tc - T);
end CSTRArrheniusPI;
