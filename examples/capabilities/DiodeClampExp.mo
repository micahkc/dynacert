// A nonlinearity with no atom lemma: the exponential of a diode clamp. dynacert names the gap
// and claims nothing, and Monte Carlo and falsification still give evidence.
//
//   dynacert examples/capabilities/DiodeClampExp.mo
//   dynacert examples/capabilities/DiodeClampExp.mo validate --n 200
model DiodeClampExp
  parameter Real C = 1.0 "Capacitance";
  parameter Real G = 1.0 "Load conductance";
  parameter Real Is = 0.01 "Saturation current";
  parameter Real Vt = 0.5 "Thermal voltage";
  input Real i "Injected current" annotation(__Dynacert(disturbance(bound = 1.0)));
  Real v(start = 0, fixed = true) "Node voltage" annotation(__Dynacert(certify));
equation
  C*der(v) = -G*v - Is*(exp(v/Vt) - 1) + i;
end DiodeClampExp;
