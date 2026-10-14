// A quadrotor tracking a reference, built from components: the vehicle and the reference
// are the same rigid-body model (SE₂(3) kinematics in constant gravity), the thrust goes
// through a first-order motor lag, and the controller uses body-frame (group) errors.
// `dynacert examples/QuadrotorTracking.mo structure` finds both SE₂(3) blocks, pairs them
// into a log error whose gravity residual vanishes (group-affine), and finds the
// motor ↔ vehicle feedback layer.

model RigidBody "ṗ = v, v̇ = R a + g, Ṙ = R·skew(ω); a, ω in the body frame"
  parameter Real g = 9.81;
  input Real a[3] "specific force (body frame)";
  input Real w[3] "body rates";
  Real p[3](each start = 0, each fixed = true);
  Real v[3](each start = 0, each fixed = true);
  Real R[3,3](start = {{1,0,0},{0,1,0},{0,0,1}}, each fixed = true);
equation
  der(p) = v;
  der(v) = R*a + {0, 0, -g};
  der(R) = R*skew(w);
end RigidBody;

model Motor "first-order thrust lag"
  parameter Real tau = 0.05;
  input Real cmd;
  Real f(start = 9.81, fixed = true);
equation
  der(f) = (cmd - f)/tau;
end Motor;

model QuadrotorTracking
  parameter Real m = 1.0;
  parameter Real kp = 4.0;
  parameter Real kd = 3.0;
  parameter Real kR = 8.0;
  parameter Real kx = 0.4;
  input Real T_ref "reference collective thrust";
  input Real w_ref[3] "reference body rates";
  input Real d[3] annotation(__Dynacert(disturbance(bound = 0.2)));
  RigidBody quad;
  RigidBody ref;
  Motor motor;
  Real Rt[3,3] "attitude error R_refᵀ R";
  Real ep[3] "position error, reference body frame";
  Real ev[3] "velocity error, reference body frame";
  Real eR[3] "attitude error vector";
equation
  Rt = transpose(ref.R)*quad.R;
  ep = transpose(ref.R)*(quad.p - ref.p);
  ev = transpose(ref.R)*(quad.v - ref.v);
  eR = {0.5*(Rt[3,2] - Rt[2,3]), 0.5*(Rt[1,3] - Rt[3,1]), 0.5*(Rt[2,1] - Rt[1,2])};
  ref.a = {0, 0, T_ref/m};
  ref.w = w_ref;
  motor.cmd = T_ref - m*(kp*ep[3] + kd*ev[3]);
  quad.a = {0, 0, motor.f/m} + d;
  quad.w = w_ref + {kx*(kp*ep[2] + kd*ev[2]), -kx*(kp*ep[1] + kd*ev[1]), 0} - kR*eR;
end QuadrotorTracking;
