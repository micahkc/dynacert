// Dynamic positioning (station keeping) of an offshore vessel, surge axis.
//
//   M*u' = -D*u + tau + F_wave,   x' = u
// M includes added mass. The linear damping D depends on current, sea state and hull
// fouling, so it is declared uncertain over [3e4, 8e4] N*s/m (A is affine in D).
// F_wave is the slowly varying second-order wave drift plus wind gust force (bounded).
// The DP controller is PID on position (integral state xi' = x), using thrust tau.
// Units are tonnes, kN and metres to keep the numbers well scaled.
//
// Certified: position excursion |x|, surge speed |u| and the integrator state stay bounded
// for every drift force within +-100 kN and every damping in the range (position-keeping
// watch circle). Values are illustrative for a ~5000 t offshore supply vessel.
model DynamicPositioningSurge
  parameter Real M = 5000.0 "Mass including added mass [t]";
  parameter Real D = 50.0 "Linear surge damping [kN*s/m]"
    annotation(__Dynacert(uncertain(min = 30.0, max = 80.0)));
  parameter Real kp = 200.0 "Position gain [kN/m]";
  parameter Real kd = 2000.0 "Velocity gain [kN*s/m]";
  parameter Real ki = 4.0 "Integral gain [kN/(m*s)]";

  input Real F_wave "Wave drift + wind gust force [kN]"
    annotation(__Dynacert(disturbance(bound = 100.0)));

  Real x(start = 0, fixed = true) "Surge position error from setpoint [m]"
    annotation(__Dynacert(certify));
  Real u(start = 0, fixed = true) "Surge speed [m/s]" annotation(__Dynacert(certify));
  Real xi(start = 0, fixed = true) "Integral of position error [m*s]"
    annotation(__Dynacert(certify));
  Real tau "Thruster force [kN]";
equation
  tau = -kp*x - kd*u - ki*xi;
  der(xi) = x;
  der(x) = u;
  M*der(u) = -D*u + tau + F_wave;
end DynamicPositioningSurge;
