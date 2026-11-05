// A three-branch `if … elseif … else` chain gives three modes, and the algebraic output `u`
// depends on the mode (each mode gets its own output row, and the bound is the largest).
//
//   dynacert examples/capabilities/GearshiftElseifChain.mo certify switched
model GearshiftElseifChain
  parameter Real k1 = 8.0 "Gain, first band";
  parameter Real k2 = 6.0 "Gain, second band";
  parameter Real k3 = 4.0 "Gain, third band";
  parameter Real ki = 1.0 "Integral gain";
  input Real d "Road load" annotation(__Dynacert(disturbance(bound = 0.5)));
  Real w(start = 0, fixed = true) "Speed error" annotation(__Dynacert(certify));
  Real z(start = 0, fixed = true) "Integrator";
  Real u "Drive command" annotation(__Dynacert(certify));
equation
  u = -(if abs(z) < 0.1 then k1 elseif abs(z) < 0.2 then k2 else k3)*w - ki*z;
  der(w) = -w + u + d;
  der(z) = w;
end GearshiftElseifChain;
