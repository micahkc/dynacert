// Payload hoist with two uncertain parameters at once: inverse mass and viscous drag. Their
// product appears in A, which is multi-affine, so the claim holds for every point of the box by
// checking one LMI per corner (four corners) with a common P. The disturbance enters in
// acceleration units because the input matrix must not depend on an uncertain parameter;
// UncertainInputRejected shows that case.
//
//   dynacert examples/capabilities/PayloadLiftUncertain.mo certify lmi
model PayloadLiftUncertain
  parameter Real im = 0.5 "Inverse mass [1/kg]"
    annotation(__Dynacert(uncertain(min = 0.3, max = 0.7)));
  parameter Real c = 1.0 "Drag [N s/m]" annotation(__Dynacert(uncertain(min = 0.5, max = 2.0)));
  parameter Real kp = 16.0 "Position gain [m/s2/m]";
  parameter Real kd = 8.0 "Velocity gain [m/s2/(m/s)]";
  input Real d "Wind acceleration [m/s2]" annotation(__Dynacert(disturbance(bound = 1.0)));
  Real z(start = 0, fixed = true) "Height error [m]" annotation(__Dynacert(certify));
  Real w(start = 0, fixed = true) "Rate of climb [m/s]" annotation(__Dynacert(certify));
equation
  der(z) = w;
  der(w) = -kp*z - kd*w - im*c*w + d;
end PayloadLiftUncertain;
