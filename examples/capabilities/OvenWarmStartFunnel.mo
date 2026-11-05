// Oven held at a set point, starting anywhere in an initial box instead of at rest. The
// certificate proves a tube that covers the box and a shrinking funnel (`Cert.funnel`):
// V(z(t)) ≤ V₀e^{-αt} + (γμ/α)(1 - e^{-αt}).
//
//   dynacert examples/capabilities/OvenWarmStartFunnel.mo certify lmi
model OvenWarmStartFunnel
  parameter Real a = 0.1 "Heat loss rate [1/s]";
  parameter Real kp = 0.5 "Proportional gain [1/s]";
  parameter Real ki = 0.05 "Integral gain [1/s2]";
  input Real d "Door and load heat flux [K/s]" annotation(__Dynacert(disturbance(bound = 0.1)));
  Real T(start = 0, fixed = true) "Temperature deviation [K]"
    annotation(__Dynacert(certify, initialSet(min = -2, max = 2)));
  Real xi(start = 0, fixed = true) "Integrator [K s]"
    annotation(__Dynacert(initialSet(min = -1, max = 1)));
equation
  der(T) = -a*T - kp*T - ki*xi + d;
  der(xi) = T;
end OvenWarmStartFunnel;
