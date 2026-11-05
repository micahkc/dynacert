// CNC machine-tool feed axis (ball-screw table, rigid-body model) following a programmed
// tool path under cutting-force disturbance. Illustrative parameters.
//
// Units: position in mm, velocity in mm/s, force in N, mass in kg, time in s.
// Controller: PID on the position error (integrator as a state) plus model-based
// feedforward computed from the reference (inertia and viscous friction).
// Closed-loop poles are placed at a triple -150 rad/s for the nominal plant.
model CNCFeedAxis
  parameter Real m = 200.0 "Table + workpiece mass [kg]";
  parameter Real c = 1000.0 "Viscous friction of guideways and screw [N*s/m]";
  parameter Real kp = 13500.0 "Position gain [N/mm]";
  parameter Real kd = 89.8 "Velocity gain [N*s/mm]";
  parameter Real ki = 675000.0 "Integral gain [N/(mm*s)]";

  input Real x_ref "Commanded position [mm]"
    annotation(__Dynacert(reference(derivative = "v_ref", start = 0)));
  input Real v_ref "Commanded feed rate [mm/s]"
    annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref "Commanded acceleration [mm/s2]" annotation(__Dynacert(reference));
  input Real F_cut "Cutting force along the axis [N]"
    annotation(__Dynacert(disturbance(bound = 500.0)));

  Real x(start = 0, fixed = true) "Table position [mm]";
  Real v(start = 0, fixed = true) "Table velocity [mm/s]";
  Real xi(start = 0, fixed = true) "Integral of the position error [mm*s]";

  Real F_ff "Feedforward force [N]";
  Real F "Motor force at the table [N]";
  Real e "Contouring (position) error [mm]" annotation(__Dynacert(certify));
  Real ev "Velocity error [mm/s]" annotation(__Dynacert(certify));
  Real ei "Integral of the position error [mm*s]" annotation(__Dynacert(certify));
equation
  e = x - x_ref;
  ev = v - v_ref;
  ei = xi;
  F_ff = (m*a_ref + c*v_ref)/1000;
  F = F_ff - kp*e - kd*ev - ki*xi;
  der(xi) = e;
  der(x) = v;
  der(v) = 1000*(F + F_cut)/m - c*v/m;
end CNCFeedAxis;
