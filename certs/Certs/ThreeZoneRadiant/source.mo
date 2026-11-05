// Three heated zones in a row, written as three instances of one component and weakly coupled
// through their walls. `structure` reports the instances as coupled layers. `layered` certifies
// each zone with its neighbours' temperatures as bounded disturbances and closes the cycle with
// `Compose.assume_guarantee` (mutual first exit).
//
//   dynacert examples/capabilities/ThreeZoneRadiant.mo structure
//   dynacert examples/capabilities/ThreeZoneRadiant.mo certify
model Zone
  parameter Real a = 1.0 "Loss plus heater feedback rate [1/h]";
  input Real Q "Net wall and load heat [K/h]";
  Real T(start = 0, fixed = true) "Temperature deviation [K]" annotation(__Dynacert(certify));
equation
  der(T) = -a*T + Q;
end Zone;

model ThreeZoneRadiant
  parameter Real kw = 0.15 "Wall conductance [1/h]";
  input Real d1 "Load, zone 1 [K/h]" annotation(__Dynacert(disturbance(bound = 1.0)));
  input Real d2 "Load, zone 2 [K/h]" annotation(__Dynacert(disturbance(bound = 0.5)));
  input Real d3 "Load, zone 3 [K/h]" annotation(__Dynacert(disturbance(bound = 0.8)));
  Zone z1(a = 1.2);
  Zone z2(a = 1.5);
  Zone z3(a = 1.0);
equation
  z1.Q = kw*(z2.T - z1.T) + d1;
  z2.Q = kw*(z1.T - z2.T) + kw*(z3.T - z2.T) + d2;
  z3.Q = kw*(z2.T - z3.T) + d3;
end ThreeZoneRadiant;
