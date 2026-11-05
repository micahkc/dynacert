// Three-axis gimbal with array variables: a coupled stiffness matrix, one damping per axis and
// one disturbance bound per axis. Arrays are annotated as a whole and read per component, so the
// claim gives one bound per element: |th[1]| ≤ b₀, |th[2]| ≤ b₁, |th[3]| ≤ b₂.
//
//   dynacert examples/capabilities/GimbalThreeAxis.mo certify lmi
model GimbalThreeAxis
  parameter Real K[3,3] = {{4.0, 0.2, 0}, {0, 6.0, 0.3}, {0.1, 0, 5.0}} "Servo stiffness [1/s2]";
  parameter Real c[3] = {3.0, 3.5, 3.2} "Rate damping [1/s]";
  input Real d[3] "Base-motion torque [rad/s2]"
    annotation(__Dynacert(disturbance(bound = {0.2, 0.1, 0.1})));
  Real th[3](each start = 0, each fixed = true) "Pointing error [rad]"
    annotation(__Dynacert(certify));
  Real w[3](each start = 0, each fixed = true) "Rate [rad/s]";
equation
  der(th) = w;
  for i in 1:3 loop
    der(w[i]) = -(K * th)[i] - c[i] * w[i] + d[i];
  end for;
end GimbalThreeAxis;
