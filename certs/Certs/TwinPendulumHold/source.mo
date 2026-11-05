// Two inverted pendula held upright and joined by a soft spring: `sin` atoms on two independent
// coordinates. The exact linear part includes the spring; each sin θ - θ is a sector channel
// proved in Lean on the region found by the fixed point.
//
//   dynacert examples/capabilities/TwinPendulumHold.mo certify sector
model TwinPendulumHold
  parameter Real a = 9.81 "g/l [1/s2]";
  parameter Real kp = 25.0 "Angle gain [1/s2]";
  parameter Real kd = 8.0 "Rate gain [1/s]";
  parameter Real ks = 1.0 "Spring between the links [1/s2]";
  input Real d1 "Torque, link 1 [rad/s2]" annotation(__Dynacert(disturbance(bound = 1.0)));
  input Real d2 "Torque, link 2 [rad/s2]" annotation(__Dynacert(disturbance(bound = 0.5)));
  Real th1(start = 0, fixed = true) "Angle, link 1 [rad]" annotation(__Dynacert(certify));
  Real w1(start = 0, fixed = true) "Rate, link 1 [rad/s]";
  Real th2(start = 0, fixed = true) "Angle, link 2 [rad]" annotation(__Dynacert(certify));
  Real w2(start = 0, fixed = true) "Rate, link 2 [rad/s]";
  Real u1 "Control, link 1 [rad/s2]";
  Real u2 "Control, link 2 [rad/s2]";
equation
  u1 = -kp*th1 - kd*w1;
  u2 = -kp*th2 - kd*w2;
  der(th1) = w1;
  der(w1) = a*sin(th1) + ks*(th2 - th1) + u1 + d1;
  der(th2) = w2;
  der(w2) = a*sin(th2) + ks*(th1 - th2) + u2 + d2;
end TwinPendulumHold;
