// Two independent if-expressions give four modes. The gain switches on the integrator and the
// damping on the speed sign. The certificate is one quadratic storage that decays in every mode,
// so it holds under any switching, including this model's.
//
//   dynacert examples/capabilities/ValveGainTwoSwitches.mo certify switched
model ValveGainTwoSwitches
  parameter Real kLow = 4.0 "Stiffness near the seat [1/s2]";
  parameter Real kHigh = 6.0 "Stiffness away from the seat [1/s2]";
  parameter Real cOpen = 3.0 "Damping opening [1/s]";
  parameter Real cClose = 4.0 "Damping closing [1/s]";
  parameter Real band = 0.1 "Schedule band [m]";
  input Real d "Flow force [m/s2]" annotation(__Dynacert(disturbance(bound = 0.5)));
  Real x(start = 0, fixed = true) "Spool position [m]" annotation(__Dynacert(certify));
  Real v(start = 0, fixed = true) "Spool speed [m/s]" annotation(__Dynacert(certify));
equation
  der(x) = v;
  der(v) = -(if abs(x) > band then kHigh else kLow)*x
           - (if v > 0 then cOpen else cClose)*v + d;
end ValveGainTwoSwitches;
