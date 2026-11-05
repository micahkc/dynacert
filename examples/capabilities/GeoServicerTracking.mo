// A servicer holding station on a coasting client in a circular orbit, in inverse-square gravity.
// Same structure as SpacecraftTracking with different gains and orbit: `structure` finds the
// SE₂(3) pair, and `lie` certifies the errors through the log-error tube.
//
//   dynacert examples/capabilities/GeoServicerTracking.mo structure
//   dynacert examples/capabilities/GeoServicerTracking.mo certify lie
model ServicerBody "ṗ = v, v̇ = R a - μ p/‖p‖³, Ṙ = R·skew(ω)"
  parameter Real mu = 0.01;
  parameter Real p0[3] = {1, 0, 0};
  parameter Real v0[3] = {0, 0.1, 0} "circular: |v0|² = mu/|p0|";
  input Real a[3] "thrust acceleration (body frame)";
  input Real w[3] "body rates";
  Real p[3](start = p0, each fixed = true);
  Real v[3](start = v0, each fixed = true);
  Real R[3,3](start = {{1,0,0},{0,1,0},{0,0,1}}, each fixed = true);
equation
  der(p) = v;
  der(v) = R*a - mu*p/(p*p)^1.5;
  der(R) = R*skew(w);
end ServicerBody;

model GeoServicerTracking
  parameter Real kp = 4.0;
  parameter Real kd = 5.0;
  parameter Real kR = 2.0;
  input Real d[3] annotation(__Dynacert(disturbance(bound = 0.002)));
  ServicerBody sc;
  ServicerBody ref;
  Real Rt[3,3] "attitude error R_refᵀ R";
  Real ep[3] "position error, reference body frame";
  Real ev[3] "velocity error, reference body frame";
  Real eR[3] "attitude error vector";
  Real pos_err annotation(__Dynacert(certify));
  Real vel_err annotation(__Dynacert(certify));
  Real att_err annotation(__Dynacert(certify));
equation
  Rt = transpose(ref.R)*sc.R;
  ep = transpose(ref.R)*(sc.p - ref.p);
  ev = transpose(ref.R)*(sc.v - ref.v);
  eR = {0.5*(Rt[3,2] - Rt[2,3]), 0.5*(Rt[1,3] - Rt[3,1]), 0.5*(Rt[2,1] - Rt[1,2])};
  ref.a = {0, 0, 0};
  ref.w = {0, 0, 0};
  sc.a = -kp*ep - kd*ev + d;
  sc.w = -kR*eR;
  pos_err = sqrt((sc.p - ref.p)*(sc.p - ref.p));
  vel_err = sqrt((sc.v - ref.v)*(sc.v - ref.v));
  att_err = sqrt(eR*eR);
end GeoServicerTracking;
