// Nonlinear train cruise control with full Davis running resistance (validation only).
//
//   M*v' = F - (A0 + A1*v + A2*v^2) - M*g*sin(grade) ,  grade = grade0 + d_grade
// The quadratic aerodynamic term A2*v^2 and sin(grade) make the dynamics nonlinear.
// The cruise controller is PI on speed with a feedforward of the nominal resistance at
// the set speed, starting from the set speed at time 0:
//   F = R(v_set) - kp*(v - v_set) - ki*xi,  xi' = v - v_set
// d_grade is an unknown grade perturbation (bounded, rad).
//
// Not certifiable by the LMI method (nonlinear); montecarlo and falsify report achieved
// peaks of the speed error. Units: tonnes, kN, m/s. Values are illustrative.
model TrainSpeedDavis
  parameter Real M = 400.0 "Train mass [t]";
  parameter Real g = 9.81 "Gravity [m/s2]";
  parameter Real A0 = 6.0 "Davis constant term [kN]";
  parameter Real A1 = 0.1 "Davis linear term [kN*s/m]";
  parameter Real A2 = 0.008 "Davis aerodynamic term [kN*s2/m2]";
  parameter Real v_set = 40.0 "Set speed [m/s]";
  parameter Real kp = 300.0 "Speed gain [kN*s/m]";
  parameter Real ki = 30.0 "Integral gain [kN/m]";
  parameter Real grade0 = 0.0 "Nominal grade [rad]";

  input Real d_grade "Grade perturbation [rad]" annotation(__Dynacert(disturbance(bound = 0.02)));

  Real v(start = 40.0, fixed = true) "Train speed [m/s]";
  Real xi(start = 0, fixed = true) "Integral of speed error [m]";
  Real e_v "Speed error [m/s]" annotation(__Dynacert(certify));
  Real F "Traction force [kN]";
equation
  e_v = v - v_set;
  F = A0 + A1*v_set + A2*v_set^2 - kp*e_v - ki*xi;
  der(xi) = e_v;
  M*der(v) = F - (A0 + A1*v + A2*v^2) - M*g*sin(grade0 + d_grade);
end TrainSpeedDavis;
