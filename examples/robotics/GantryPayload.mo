// Pick-and-place gantry axis holding a place position while the payload mass is unknown
// (empty gripper up to a 20 kg part) and the machine frame vibrates. Illustrative values.
//
// The moving mass enters the dynamics as 1/(m_carriage + m_payload). dynacert needs the
// A matrix to be affine in uncertain parameters, so the uncertain parameter is the inverse
// moving mass winv in [1/50, 1/30] 1/kg. Disturbances enter as accelerations (frame
// vibration, cable-carrier drag per unit mass) so that B does not depend on winv.
// The motor force is substituted into der(v) instead of being used through the algebraic
// F: with F multiplied by the uncertain winv, the generated Lean link proof (dynacert at the
// time of writing) omitted the winv*(F equation) term and failed with `ring failed`.
// x is measured from the place position; the axis starts with a 2 mm residual error left
// by the preceding move.
model GantryPayload
  parameter Real winv = 0.025 "Inverse moving mass, carriage 30 kg + payload 0..20 kg [1/kg]"
    annotation(__Dynacert(uncertain(min = 0.02, max = 0.0333)));
  parameter Real c = 80.0 "Viscous friction of the linear guide [N*s/m]";
  parameter Real kp = 16000.0 "Position gain [N/m]";
  parameter Real kd = 1200.0 "Velocity gain [N*s/m]";
  parameter Real ki = 40000.0 "Integral gain [N/(m*s)]";

  input Real a_vib "Frame vibration acceleration [m/s2]"
    annotation(__Dynacert(disturbance(bound = 0.5)));
  input Real a_drag "Cable-carrier drag per unit moving mass [m/s2]"
    annotation(__Dynacert(disturbance(bound = 0.2)));

  Real x(start = 0.002, fixed = true) "Position error from the place position [m]"
    annotation(__Dynacert(certify));
  Real v(start = 0, fixed = true) "Velocity [m/s]" annotation(__Dynacert(certify));
  Real xi(start = 0, fixed = true) "Integral of the position error [m*s]"
    annotation(__Dynacert(certify));
  Real F "Motor force [N]";
equation
  F = -kp*x - kd*v - ki*xi;
  der(xi) = x;
  der(x) = v;
  der(v) = winv*(-kp*x - kd*v - ki*xi - c*v) + a_vib + a_drag;
end GantryPayload;
