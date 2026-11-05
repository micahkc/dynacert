// Hard-disk-drive head positioning, track following. Voice-coil actuator modelled as a
// rigid double integrator plus one lightly damped suspension resonance in the measured
// position. Illustrative parameters (not a specific drive).
//
// Units: position in nm, time in ms (so velocity nm/ms, acceleration nm/ms^2; 1 nm/ms^2 =
// 1 mm/s^2). The head position y is measured relative to the track centre, so repeatable
// runout (track eccentricity, 120 Hz at 7200 rpm, ~100 nm amplitude) enters as an
// equivalent acceleration a_ro with |a_ro| <= A*w^2 = 100*(0.754)^2 ~ 57 nm/ms^2.
// Windage and flex-cable bias are a second bounded acceleration.
// Controller: PID on the measured position y + q (rate from a state estimator, assumed
// exact here); closed-loop bandwidth ~ 300-450 Hz.
model HardDiskTrackFollow
  parameter Real wr = 31.4 "Suspension resonance, 5 kHz [rad/ms]";
  parameter Real zr = 0.02 "Suspension damping ratio [-]";
  parameter Real gr = 0.3 "Modal gain of the resonance [-]";
  parameter Real kp = 27.0 "Position gain [1/ms^2]";
  parameter Real kd = 9.0 "Rate gain [1/ms]";
  parameter Real ki = 27.0 "Integral gain [1/ms^3]";

  input Real a_ro "Runout seen as relative acceleration [nm/ms^2]"
    annotation(__Dynacert(disturbance(bound = 57.0)));
  input Real a_w "Windage and flex-cable bias [nm/ms^2]"
    annotation(__Dynacert(disturbance(bound = 20.0)));

  Real y(start = 0, fixed = true) "Rigid-body head position off track [nm]"
    annotation(__Dynacert(certify));
  Real v(start = 0, fixed = true) "Rigid-body head velocity [nm/ms]" annotation(__Dynacert(certify));
  Real q(start = 0, fixed = true) "Suspension mode displacement at the head [nm]"
    annotation(__Dynacert(certify));
  Real qd(start = 0, fixed = true) "Suspension mode velocity [nm/ms]" annotation(__Dynacert(certify));
  Real xi(start = 0, fixed = true) "Integral of the measured position [nm*ms]"
    annotation(__Dynacert(certify));
  Real u "Actuator acceleration command [nm/ms^2]";
equation
  u = -kp*(y + q) - kd*(v + qd) - ki*xi;
  der(xi) = y + q;
  der(y) = v;
  der(v) = u + a_ro + a_w;
  der(q) = qd;
  der(qd) = -wr^2*q - 2*zr*wr*qd + gr*u;
end HardDiskTrackFollow;
