// Lane keeping at constant speed: linear single-track (bicycle) model in road-relative
// error coordinates.
//   e_y   lateral offset from the lane centre        e_y'   = v_y + v_x*e_psi
//   e_psi heading error relative to the lane tangent e_psi' = r - v_x*kappa
// v_y (lateral velocity) and r (yaw rate) follow the linear tire-force bicycle model.
// The road curvature kappa is an unknown bounded disturbance (curves up to 200 m radius);
// the controller uses a kinematic curvature feedforward (a + b)*kappa from a lane camera plus
// state feedback (gains from an LQR design on the nominal model).
//
// Certified: lateral offset and heading error stay bounded for any curvature profile with
// |kappa| <= 0.005 1/m, at 20 m/s. All parameter values are illustrative.
model LaneKeepingLateral
  parameter Real m = 1500.0 "Vehicle mass [kg]";
  parameter Real Iz = 2500.0 "Yaw inertia [kg*m2]";
  parameter Real a = 1.2 "CG to front axle [m]";
  parameter Real b = 1.6 "CG to rear axle [m]";
  parameter Real Cf = 80000.0 "Front axle cornering stiffness [N/rad]";
  parameter Real Cr = 80000.0 "Rear axle cornering stiffness [N/rad]";
  parameter Real vx = 20.0 "Longitudinal speed [m/s]";
  parameter Real k_y = 0.141 "Lateral offset gain [rad/m]";
  parameter Real k_vy = 0.030 "Lateral velocity gain [rad*s/m]";
  parameter Real k_psi = 1.602 "Heading error gain [rad/rad]";
  parameter Real k_r = 0.144 "Yaw rate gain [rad*s/rad]";

  input Real kappa "Road curvature [1/m]" annotation(__Dynacert(disturbance(bound = 0.005)));

  Real e_y(start = 0, fixed = true) "Lateral offset [m]" annotation(__Dynacert(certify));
  Real v_y(start = 0, fixed = true) "Lateral velocity [m/s]";
  Real e_psi(start = 0, fixed = true) "Heading error [rad]" annotation(__Dynacert(certify));
  Real r(start = 0, fixed = true) "Yaw rate [rad/s]";
  Real delta "Front steering angle [rad]";
equation
  delta = (a + b)*kappa - k_y*e_y - k_vy*v_y - k_psi*e_psi - k_r*r;
  der(e_y) = v_y + vx*e_psi;
  der(e_psi) = r - vx*kappa;
  m*der(v_y) = -(Cf + Cr)/vx*v_y + ((b*Cr - a*Cf)/vx - m*vx)*r + Cf*delta;
  Iz*der(r) = (b*Cr - a*Cf)/vx*v_y - (a*a*Cf + b*b*Cr)/vx*r + a*Cf*delta;
end LaneKeepingLateral;
