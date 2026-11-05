// The PID-tracked pendulum of Condie, Woodbury, Pant and Goppert, "Continuous-time certified
// invariant funnels for nonlinear tracking systems via polytopic embeddings and univariate
// sum-of-squares" (Section V), with a single rest-to-rest-to-rest polynomial reference
// θ_ref(t) = 64 A s³(1 - s)³, s = t/T (0 → π/4 → 0 over 4 s), in place of the paper's two
// quintics (a piecewise reference would need time events, which rumoca's Lean export lacks).
//
// The feedforward makes the reference an exact solution of the undisturbed closed loop, so the
// tracking error obeys ż = f(x* + z) - f(x*) + B w. `dynacert examples/PendulumPID.mo funnel`
// certifies a finite-horizon funnel on the angle error over [0, 4] s (Dynacert.Nonlinear.FunnelCert).
model PendulumPID
  parameter Real m = 1.0 "mass [kg]";
  parameter Real l = 1.0 "length [m]";
  parameter Real g = 9.81 "gravity [m/s2]";
  parameter Real b = 0.1 "viscous damping [N m s]";
  parameter Real Kp = 0.1;
  parameter Real Ki = 0.1;
  parameter Real Kd = 0.1;
  parameter Real A = 0.7853981633974483 "reference peak [rad]";
  parameter Real Tf = 4 "reference duration [s]";
  input Real w "disturbance torque [N m]" annotation(__Dynacert(disturbance(bound = 0.1)));
  Real theta(start = 0, fixed = true) annotation(__Dynacert(nominal = "theta_ref"));
  Real omega(start = 0, fixed = true) annotation(__Dynacert(nominal = "omega_ref"));
  Real xi(start = 0, fixed = true) "integral of the angle error";
  Real s "normalized time";
  Real theta_ref;
  Real omega_ref;
  Real a_ref;
  Real u "control torque [N m]";
  Real e "angle error [rad]" annotation(__Dynacert(certify));
equation
  s = time/Tf;
  theta_ref = 64*A*s^3*(1 - s)^3;
  omega_ref = 64*A*(3*s^2*(1 - s)^3 - 3*s^3*(1 - s)^2)/Tf;
  a_ref = 64*A*(6*s*(1 - s)^3 - 18*s^2*(1 - s)^2 + 6*s^3*(1 - s))/Tf^2;
  u = m*l^2*a_ref + b*omega_ref + m*g*l*sin(theta_ref)
      + Kp*(theta_ref - theta) + Ki*xi + Kd*(omega_ref - omega);
  der(theta) = omega;
  m*l^2*der(omega) = -m*g*l*sin(theta) - b*omega + u + w;
  der(xi) = theta_ref - theta;
  e = theta - theta_ref;
  annotation(__Dynacert(horizon = 4), experiment(StopTime = 4));
end PendulumPID;
