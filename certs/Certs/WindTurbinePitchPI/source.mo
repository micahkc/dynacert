// Above-rated wind turbine rotor-speed regulation by collective pitch (linearized about
// an operating point; illustrative multi-megawatt-class numbers). Generator torque is
// held constant above rated, so the rotor sees aerodynamic torque deviations only:
//   J*dw' = kw*dw + ktheta*dtheta + kv*dv_wind
// The pitch sensitivity ktheta varies strongly with wind speed, so it is uncertain;
// the PI gain is fixed (no gain scheduling), and the claim covers the whole range.
// Torque in MN*m, inertia in 1e6 kg*m^2, pitch in degrees, time in seconds.
model WindTurbinePitchPI
  parameter Real J = 40.0 "Drivetrain inertia referred to rotor [1e6 kg*m2] (illustrative)";
  parameter Real kw = -1.5 "Aero torque sensitivity to rotor speed [MN*m*s/rad] (illustrative)";
  parameter Real ktheta = -0.8 "Aero torque sensitivity to pitch [MN*m/deg] (illustrative)"
    annotation(__Dynacert(uncertain(min = -1.2, max = -0.5)));
  parameter Real kv = 0.6 "Aero torque sensitivity to wind speed [MN*m/(m/s)] (illustrative)";
  parameter Real tau = 0.3 "Pitch actuator time constant [s] (illustrative)";
  parameter Real kp = 60.0 "Pitch PI proportional gain [deg/(rad/s)]";
  parameter Real ki = 15.0 "Pitch PI integral gain [deg/rad]";

  input Real dv_wind "Wind speed deviation [m/s]" annotation(__Dynacert(disturbance(bound = 2.0)));

  Real dw(start = 0, fixed = true) "Rotor speed deviation [rad/s]" annotation(__Dynacert(certify));
  Real dtheta(start = 0, fixed = true) "Pitch angle deviation [deg]" annotation(__Dynacert(certify));
  Real z(start = 0, fixed = true) "Integral of rotor speed deviation [rad]";
  Real theta_cmd "Pitch command deviation [deg]";
equation
  theta_cmd = kp*dw + ki*z;
  der(z) = dw;
  J*der(dw) = kw*dw + ktheta*dtheta + kv*dv_wind;
  tau*der(dtheta) = theta_cmd - dtheta;
end WindTurbinePitchPI;
