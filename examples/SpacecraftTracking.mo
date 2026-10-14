// A spacecraft tracking a reference orbit in inverse-square gravity. Same structure as
// QuadrotorTracking (two SE₂(3) blocks, body-frame controller), but the gravity is
// -μ p/‖p‖³: `structure` classifies it as inverse-square, not group-affine, and pairs it with
// the gravity residual lemma `Lie.gravity_residual_inverse_square`.

model OrbitalBody "ṗ = v, v̇ = R a - μ p/‖p‖³, Ṙ = R·skew(ω)"
  parameter Real mu = 1.0;
  parameter Real p0[3] = {1, 0, 0};
  parameter Real v0[3] = {0, 1, 0};
  input Real a[3] "thrust acceleration (body frame)";
  input Real w[3] "body rates";
  Real p[3](start = p0, each fixed = true);
  Real v[3](start = v0, each fixed = true);
  Real R[3,3](start = {{1,0,0},{0,1,0},{0,0,1}}, each fixed = true);
equation
  der(p) = v;
  der(v) = R*a - mu*p/(p*p)^1.5;
  der(R) = R*skew(w);
end OrbitalBody;

model SpacecraftTracking
  parameter Real kp = 0.04;
  parameter Real kd = 0.4;
  parameter Real kR = 0.5;
  input Real a_ref[3];
  input Real w_ref[3];
  input Real d[3] annotation(__Dynacert(disturbance(bound = 0.001)));
  OrbitalBody sc;
  OrbitalBody ref;
  Real Rt[3,3];
  Real ep[3];
  Real ev[3];
  Real eR[3];
equation
  Rt = transpose(ref.R)*sc.R;
  ep = transpose(ref.R)*(sc.p - ref.p);
  ev = transpose(ref.R)*(sc.v - ref.v);
  eR = {0.5*(Rt[3,2] - Rt[2,3]), 0.5*(Rt[1,3] - Rt[3,1]), 0.5*(Rt[2,1] - Rt[1,2])};
  ref.a = a_ref;
  ref.w = w_ref;
  sc.a = a_ref - kp*ep - kd*ev + d;
  sc.w = w_ref - kR*eR;
end SpacecraftTracking;
