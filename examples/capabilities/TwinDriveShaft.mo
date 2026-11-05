// Two speed-controlled drives sharing a soft shaft, one component class with two sets of
// parameters. `layered` proves much tighter bounds than one joint ellipsoid when the disturbances
// are unequal, because each drive gets its own storage.
//
//   dynacert examples/capabilities/TwinDriveShaft.mo certify
model Drive
  parameter Real k = 4.0 "Position loop gain [1/s2]";
  parameter Real c = 3.0 "Rate loop gain [1/s]";
  input Real T "Shaft and load torque [rad/s2]";
  Real th(start = 0, fixed = true) "Angle error [rad]" annotation(__Dynacert(certify));
  Real w(start = 0, fixed = true) "Rate error [rad/s]";
equation
  der(th) = w;
  der(w) = -k*th - c*w + T;
end Drive;

model TwinDriveShaft
  parameter Real ks = 0.3 "Shaft stiffness [1/s2]";
  input Real d1 "Load, drive 1 [rad/s2]" annotation(__Dynacert(disturbance(bound = 2.0)));
  input Real d2 "Load, drive 2 [rad/s2]" annotation(__Dynacert(disturbance(bound = 0.2)));
  Drive a(k = 4.0, c = 3.0);
  Drive b(k = 9.0, c = 5.0);
equation
  a.T = ks*(b.th - a.th) + d1;
  b.T = ks*(a.th - b.th) + d2;
end TwinDriveShaft;
