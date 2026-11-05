// Full 3D quadrotor holding hover under a cascaded controller: the 3D version of
// PlanarQuadrotor.mo ("Where to Tear", Section III), for the paper's "Full 3D vehicle" direction.
//
// States: position errors e, velocity errors v (world, z up), the vector part (qx, qy, qz) of the
// body → world unit quaternion, and the body rates (p, q, r). Mass and inertia are normalized and
// the hover reference is at the origin. The scalar part is the chart q0 = √(1 − |q_v|²), valid
// for attitudes below 180°.
//
// Plant (SE₂(3) kinematics in the quaternion chart):
//   ė = v,  v̇ = T b3 − g ẑ + w_a,  q̇_v = ½ (q0 ω + q_v × ω),  ω̇ = kw (ω_cmd − ω) + w_ω
// with b3 = R ẑ (the thrust axis) and an ideal rate loop (torque = J kw (ω_cmd − ω) + ω × Jω).
// Controller:
//   outer loop   s = Kp e + Kv v,  desired force f = −s + g ẑ
//   thrust       T = f · b3                              (projection on the thrust axis)
//   tilt         ω_cmd,xy = (kR/g) (ẑ × Rᵀf)_xy            (turn b3 toward f)
//   yaw          ω_cmd,z = −2 kψ qz                         (2 qz ≈ yaw angle)
// Linearized, roll φ ≈ 2qx and pitch θ ≈ 2qy obey φ̈ = −kw φ̇ − kw kR (φ − s_y/g), etc., so
// kw = 2ωn, kR = ωn/2 is the planar model's inner loop (k_θ = ωn², k_q = 2ωn) on each tilt axis.
// Every nonlinearity is a polynomial in the states and q0: products of the outer-loop command
// with the attitude (thrust direction and magnitude), q_v × ω and q0 ω in the kinematics.
//
// Disturbances at 10% of the planar model's full level (|w_a,i| ≤ 0.1, |w_ω,i| ≤ 0.5): the joint
// sector certificate closes at 10% and fails at 15% (the planar one closes at 25%).
model Quadrotor3D
  parameter Real g = 9.81 "Gravity [m/s2]";
  parameter Real Kp = 4.0 "Outer-loop position gain [1/s2]";
  parameter Real Kv = 4.0 "Outer-loop velocity gain [1/s]";
  parameter Real wn = 10.0 "Attitude-loop natural frequency [rad/s]";
  parameter Real kw = 2*wn "Rate-loop gain [1/s]";
  parameter Real kR = wn/2 "Tilt gain [1/s]";
  parameter Real kpsi = wn/2 "Yaw gain [1/s]";

  input Real w_ax "Gust, x [m/s2]" annotation(__Dynacert(disturbance(bound = 0.1)));
  input Real w_ay "Gust, y [m/s2]" annotation(__Dynacert(disturbance(bound = 0.1)));
  input Real w_az "Gust, z [m/s2]" annotation(__Dynacert(disturbance(bound = 0.1)));
  input Real w_p "Roll torque disturbance [rad/s2]" annotation(__Dynacert(disturbance(bound = 0.5)));
  input Real w_q "Pitch torque disturbance [rad/s2]" annotation(__Dynacert(disturbance(bound = 0.5)));
  input Real w_r "Yaw torque disturbance [rad/s2]" annotation(__Dynacert(disturbance(bound = 0.5)));

  Real e_x(start = 0, fixed = true) "Position error, x [m]" annotation(__Dynacert(certify));
  Real e_y(start = 0, fixed = true) "Position error, y [m]" annotation(__Dynacert(certify));
  Real e_z(start = 0, fixed = true) "Position error, z [m]" annotation(__Dynacert(certify));
  Real v_x(start = 0, fixed = true) "Velocity error, x [m/s]";
  Real v_y(start = 0, fixed = true) "Velocity error, y [m/s]";
  Real v_z(start = 0, fixed = true) "Velocity error, z [m/s]";
  Real qx(start = 0, fixed = true) "Quaternion vector part, x (≈ roll/2)" annotation(__Dynacert(certify));
  Real qy(start = 0, fixed = true) "Quaternion vector part, y (≈ pitch/2)" annotation(__Dynacert(certify));
  Real qz(start = 0, fixed = true) "Quaternion vector part, z (≈ yaw/2)";
  Real p(start = 0, fixed = true) "Body roll rate [rad/s]";
  Real q(start = 0, fixed = true) "Body pitch rate [rad/s]";
  Real r(start = 0, fixed = true) "Body yaw rate [rad/s]";
  Real q0 "Quaternion scalar part";
  Real s_x "Outer-loop command, x [m/s2]";
  Real s_y "Outer-loop command, y [m/s2]";
  Real s_z "Outer-loop command, z [m/s2]";
  Real b3x "Thrust axis R ẑ, x";
  Real b3y "Thrust axis R ẑ, y";
  Real b3z "Thrust axis R ẑ, z";
  Real T "Thrust acceleration f · b3 [m/s2]";
  Real fbx "Desired force in the body frame, x [m/s2]";
  Real fby "Desired force in the body frame, y [m/s2]";
equation
  q0 = sqrt(1 - qx^2 - qy^2 - qz^2);
  s_x = Kp*e_x + Kv*v_x;
  s_y = Kp*e_y + Kv*v_y;
  s_z = Kp*e_z + Kv*v_z;
  b3x = 2*(qx*qz + q0*qy);
  b3y = 2*(qy*qz - q0*qx);
  b3z = 1 - 2*(qx^2 + qy^2);
  T = -s_x*b3x - s_y*b3y + (g - s_z)*b3z;
  // (Rᵀ f)_x = b1 · f and (Rᵀ f)_y = b2 · f with the first two columns of R
  fbx = -s_x*(1 - 2*(qy^2 + qz^2)) - s_y*2*(qx*qy + q0*qz) + (g - s_z)*2*(qx*qz - q0*qy);
  fby = -s_x*2*(qx*qy - q0*qz) - s_y*(1 - 2*(qx^2 + qz^2)) + (g - s_z)*2*(qy*qz + q0*qx);
  der(e_x) = v_x;
  der(e_y) = v_y;
  der(e_z) = v_z;
  der(v_x) = T*b3x + w_ax;
  der(v_y) = T*b3y + w_ay;
  der(v_z) = T*b3z - g + w_az;
  der(qx) = 0.5*(q0*p + qy*r - qz*q);
  der(qy) = 0.5*(q0*q + qz*p - qx*r);
  der(qz) = 0.5*(q0*r + qx*q - qy*p);
  der(p) = kw*(-(kR/g)*fby - p) + w_p;
  der(q) = kw*((kR/g)*fbx - q) + w_q;
  der(r) = kw*(-2*kpsi*qz - r) + w_r;
end Quadrotor3D;
