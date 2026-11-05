// A planar hopper hovering in lunar gravity with a cascaded thrust-vector controller: thrust norm
// √(s_x² + (g - s_z)²) and pitch command atan2(-s_x, g - s_z). Same structure as PlanarQuadrotor,
// with a much smaller hover margin. All four atoms appear (sin, cos, √, atan2).
//
//   dynacert examples/capabilities/LunarHopperHover.mo certify sector
model LunarHopperHover
  parameter Real g = 1.62 "Lunar gravity [m/s2]";
  parameter Real Kp = 1.0 "Outer-loop position gain [1/s2]";
  parameter Real Kv = 2.0 "Outer-loop velocity gain [1/s]";
  parameter Real kt = 25.0 "Pitch gain [1/s2]";
  parameter Real kq = 10.0 "Pitch-rate gain [1/s]";
  input Real wx "Lateral thrust error [m/s2]" annotation(__Dynacert(disturbance(bound = 0.02)));
  input Real wz "Vertical thrust error [m/s2]" annotation(__Dynacert(disturbance(bound = 0.02)));
  input Real wq "Pitch torque error [rad/s2]" annotation(__Dynacert(disturbance(bound = 0.1)));
  Real ex(start = 0, fixed = true) "Lateral error [m]" annotation(__Dynacert(certify));
  Real ez(start = 0, fixed = true) "Vertical error [m]";
  Real vx(start = 0, fixed = true) "Lateral velocity error [m/s]";
  Real vz(start = 0, fixed = true) "Vertical velocity error [m/s]";
  Real th(start = 0, fixed = true) "Pitch [rad]" annotation(__Dynacert(certify));
  Real q(start = 0, fixed = true) "Pitch rate [rad/s]";
  Real sx "Outer-loop command, lateral [m/s2]";
  Real sz "Outer-loop command, vertical [m/s2]";
  Real f "Thrust acceleration [m/s2]";
  Real th_d "Commanded pitch [rad]";
equation
  sx = Kp*ex + Kv*vx;
  sz = Kp*ez + Kv*vz;
  f = sqrt(sx^2 + (g - sz)^2);
  th_d = atan2(-sx, g - sz);
  der(ex) = vx;
  der(ez) = vz;
  der(vx) = f*sin(th) + wx;
  der(vz) = f*cos(th) - g + wz;
  der(th) = q;
  der(q) = -kt*(th - th_d) - kq*q + wq;
end LunarHopperHover;
