// An uncertain parameter in the input matrix (the disturbance is scaled by the unknown inverse
// mass). This is not supported yet, so `lmi` rejects it by name. PayloadLiftUncertain is the
// certifiable form.
//
//   dynacert examples/capabilities/UncertainInputRejected.mo
model UncertainInputRejected
  parameter Real im = 0.5 "Inverse mass [1/kg]"
    annotation(__Dynacert(uncertain(min = 0.3, max = 0.7)));
  parameter Real kp = 16.0 "Position gain";
  parameter Real kd = 8.0 "Velocity gain";
  input Real d "Wind force [N]" annotation(__Dynacert(disturbance(bound = 2.0)));
  Real z(start = 0, fixed = true) annotation(__Dynacert(certify));
  Real w(start = 0, fixed = true);
equation
  der(z) = w;
  der(w) = -kp*z - kd*w + im*d;
end UncertainInputRejected;
