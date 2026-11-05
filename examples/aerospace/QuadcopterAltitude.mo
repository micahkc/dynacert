// Quadcopter altitude tracking with thrust feedforward and PID feedback.
//
// Vertical dynamics: m*w' = T - m*g - c_d*w + F_d   (T total rotor thrust, c_d linear
// vertical drag, F_d wind/ground-effect force disturbance).
// The altitude reference is a smooth trajectory z_ref' = w_ref, w_ref' = a_ref with a_ref
// free (any climb/descent profile); the controller computes the feedforward thrust
//   T_ff = m*(g + a_ref) + c_d*w_ref
// and adds PID feedback on the tracking error, with the integral state xi' = e_z.
//
// Certified: altitude error, vertical-speed error and the integrator state stay bounded
// along every reference trajectory, for every disturbance force within +-2 N.
// Values are illustrative for a 1.5 kg quadcopter.
model QuadcopterAltitude
  parameter Real m = 1.5 "Vehicle mass [kg]";
  parameter Real g = 9.81 "Gravity [m/s2]";
  parameter Real c_d = 0.3 "Vertical linear drag [N*s/m]";
  parameter Real kp = 12.0 "Altitude gain [N/m]";
  parameter Real kd = 7.0 "Vertical-speed gain [N*s/m]";
  parameter Real ki = 4.0 "Integral gain [N/(m*s)]";

  input Real z_ref "Altitude reference [m]"
    annotation(__Dynacert(reference(derivative = "w_ref", start = 0)));
  input Real w_ref "Vertical-speed reference [m/s]"
    annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref "Vertical-acceleration reference [m/s2]" annotation(__Dynacert(reference));
  input Real F_d "Disturbance force [N]" annotation(__Dynacert(disturbance(bound = 2.0)));

  Real z(start = 0, fixed = true) "Altitude [m]";
  Real w(start = 0, fixed = true) "Vertical speed [m/s]";
  Real xi(start = 0, fixed = true) "Integral of altitude error [m*s]"
    annotation(__Dynacert(certify));
  Real e_z "Altitude error [m]" annotation(__Dynacert(certify));
  Real e_w "Vertical-speed error [m/s]" annotation(__Dynacert(certify));
  Real T_ff "Feedforward thrust [N]";
  Real T "Total thrust [N]";
equation
  e_z = z - z_ref;
  e_w = w - w_ref;
  T_ff = m*(g + a_ref) + c_d*w_ref;
  T = T_ff - kp*e_z - kd*e_w - ki*xi;
  der(xi) = e_z;
  der(z) = w;
  m*der(w) = T - m*g - c_d*w + F_d;
end QuadcopterAltitude;
