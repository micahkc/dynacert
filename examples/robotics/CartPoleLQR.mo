// Nonlinear cart-pole (point-mass pole on a cart) balanced upright by a state-feedback LQR
// designed on the linearization at theta = 0 (Q = diag(10, 1, 100, 1), R = 0.1).
// Illustrative laboratory-scale parameters.
//
// The sin/cos terms make the closed loop nonlinear, so the lmi certificate does not apply.
// The model is a validation-only example: montecarlo and falsify estimate how close the
// pole and cart come to their limits under a bounded push (up to 4 N) on the cart, starting from a
// 0.1 rad tilt.
model CartPoleLQR
  parameter Real M = 1.0 "Cart mass [kg]";
  parameter Real m = 0.2 "Pole tip mass [kg]";
  parameter Real l = 0.5 "Pole length [m]";
  parameter Real g = 9.81 "Gravity [m/s2]";
  parameter Real b = 0.1 "Cart viscous friction [N*s/m]";
  parameter Real k_x = 10.0 "LQR gain on cart position [N/m]";
  parameter Real k_v = 11.7597 "LQR gain on cart velocity [N*s/m]";
  parameter Real k_th = 73.5448 "LQR gain on pole angle [N/rad]";
  parameter Real k_w = 14.8325 "LQR gain on pole rate [N*s/rad]";

  input Real F_d "Push on the cart [N]" annotation(__Dynacert(disturbance(bound = 4.0)));

  Real x(start = 0, fixed = true) "Cart position [m]" annotation(__Dynacert(certify));
  Real v(start = 0, fixed = true) "Cart velocity [m/s]";
  Real th(start = 0.1, fixed = true) "Pole angle from upright [rad]"
    annotation(__Dynacert(certify));
  Real w(start = 0, fixed = true) "Pole rate [rad/s]";
  Real F "Motor force on the cart [N]";
  Real xdd "Cart acceleration [m/s2]";
equation
  F = k_x*x + k_v*v + k_th*th + k_w*w;
  xdd = (F + F_d - b*v - m*g*sin(th)*cos(th) + m*l*w^2*sin(th)) / (M + m*sin(th)^2);
  der(x) = v;
  der(v) = xdd;
  der(th) = w;
  der(w) = (g*sin(th) - xdd*cos(th)) / l;
end CartPoleLQR;
