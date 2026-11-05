// Lithography / inspection wafer stage scanning a reference trajectory on an isolated
// metrology frame. Illustrative parameters.
//
// Units: position in um, time in s (velocity um/s, acceleration um/s^2), force in N,
// mass in kg; 1 N on 20 kg gives 5e4 um/s^2, hence the factor 1e6/m.
// The frame sits on an isolation system (5 Hz, damping 0.3) excited by floor acceleration;
// q is the frame displacement relative to the floor, and the frame's absolute acceleration
// a_f = -wn^2 q - 2 zf wn q' pushes the stage relative to the frame. The stage position x is
// measured relative to the frame (interferometer on the frame).
// Controller: PID with acceleration feedforward m*a_ref, poles at a triple -300 rad/s.
// The integrator state is scaled, der(xi) = wi*e with wi = 300 rad/s, so xi is in um:
// with the textbook der(xi) = e the A matrix has entries up to 2.7e7 and the lmi search
// reports no certificate (numerical conditioning), although the loop is the same.
model WaferStageScan
  parameter Real m = 20.0 "Stage mass [kg]";
  parameter Real wn = 31.4 "Isolation natural frequency, 5 Hz [rad/s]";
  parameter Real zf = 0.3 "Isolation damping ratio [-]";
  parameter Real kp = 5.4 "Position gain [N/um]";
  parameter Real kd = 0.018 "Velocity gain [N*s/um]";
  parameter Real ki = 1.8 "Integral gain on the scaled integrator [N/um]";
  parameter Real wi = 300.0 "Integrator scaling [rad/s]";

  input Real x_ref "Scan reference position [um]"
    annotation(__Dynacert(reference(derivative = "v_ref", start = 0)));
  input Real v_ref "Scan reference velocity [um/s]"
    annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref "Scan reference acceleration [um/s^2]" annotation(__Dynacert(reference));
  input Real a_floor "Floor vibration acceleration [um/s^2]"
    annotation(__Dynacert(disturbance(bound = 2000.0)));
  input Real F_rip "Motor force ripple and cable force [N]"
    annotation(__Dynacert(disturbance(bound = 0.2)));

  Real x(start = 0, fixed = true) "Stage position relative to the frame [um]";
  Real v(start = 0, fixed = true) "Stage velocity relative to the frame [um/s]";
  Real xi(start = 0, fixed = true) "Scaled integral of the position error, wi*int(e) [um]";
  Real q(start = 0, fixed = true) "Frame displacement relative to the floor [um]"
    annotation(__Dynacert(certify));
  Real qd(start = 0, fixed = true) "Frame velocity relative to the floor [um/s]"
    annotation(__Dynacert(certify));

  Real a_f "Absolute frame acceleration [um/s^2]";
  Real F "Motor force [N]";
  Real e "Position error [um]" annotation(__Dynacert(certify));
  Real ev "Velocity error [um/s]" annotation(__Dynacert(certify));
  Real ei "Scaled integral of the position error [um]" annotation(__Dynacert(certify));
equation
  e = x - x_ref;
  ev = v - v_ref;
  ei = xi;
  F = m*a_ref/1e6 - kp*e - kd*ev - ki*xi;
  a_f = -wn^2*q - 2*zf*wn*qd;
  der(xi) = wi*e;
  der(x) = v;
  der(v) = 1e6*(F + F_rip)/m - a_f;
  der(q) = qd;
  der(qd) = a_f - a_floor;
end WaferStageScan;
