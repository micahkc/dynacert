// cp_reach examples/general/models/closed_loop_composed.mo, with three changes for a
// sound certificate:
//  * the feedforward is computed in the model (u_ff = m a_ref + c v_ref + k x_ref)
//    instead of being a free input assumed to cancel the reference dynamics;
//  * the reference is declared: x_ref' = v_ref, v_ref' = a_ref, starting at rest;
//  * the plant starts at rest (fixed = true).
// Error dynamics are derived by dynacert from these equations, not written by hand.

model MassSpringDamper "Plant: Mass-spring-damper system"
  parameter Real m = 1.0 "Mass [kg]";
  parameter Real c = 0.2 "Damping coefficient [N*s/m]";
  parameter Real k = 1.0 "Spring constant [N/m]";

  input Real F "Applied force [N]";
  input Real d "Disturbance force [N]";

  Real x(start = 0, fixed = true) "Position [m]";
  Real v(start = 0, fixed = true) "Velocity [m/s]";

  output Real y_x "Position output";
  output Real y_v "Velocity output";
equation
  der(x) = v;
  der(v) = (F + d - c*v - k*x) / m;
  y_x = x;
  y_v = v;
end MassSpringDamper;

model PDController "Controller: PD with feedforward"
  parameter Real kp = 10.0 "Proportional gain";
  parameter Real kd = 2.0 "Derivative gain";

  input Real x_ref "Reference position";
  input Real v_ref "Reference velocity";
  input Real x_meas "Measured position";
  input Real v_meas "Measured velocity";
  input Real u_ff "Feedforward";

  output Real F "Control force";

  Real e "Position error";
  Real ev "Velocity error";
equation
  e = x_meas - x_ref;
  ev = v_meas - v_ref;
  F = u_ff - kp*e - kd*ev;
end PDController;

model ClosedLoopComposed "Composed closed-loop system"
  // Component instances - these create the prefixes!
  MassSpringDamper plant;
  PDController controller;

  // External inputs
  input Real x_ref "Reference position"
    annotation(__Dynacert(reference(derivative = "v_ref", start = 0)));
  input Real v_ref "Reference velocity"
    annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref "Reference acceleration" annotation(__Dynacert(reference));
  input Real d "Disturbance" annotation(__Dynacert(disturbance(bound = 1.0)));

  Real u_ff "Feedforward control";

  // Outputs (tracking errors)
  output Real e "Position error" annotation(__Dynacert(certify));
  output Real ev "Velocity error" annotation(__Dynacert(certify));
equation
  // Wire plant outputs to controller inputs
  controller.x_meas = plant.y_x;
  controller.v_meas = plant.y_v;

  // Wire controller output to plant input
  plant.F = controller.F;

  // External connections
  controller.x_ref = x_ref;
  controller.v_ref = v_ref;
  controller.u_ff = u_ff;
  plant.d = d;

  // Feedforward from the plant model and the reference
  u_ff = plant.m*a_ref + plant.c*v_ref + plant.k*x_ref;

  // Output the errors
  e = controller.e;
  ev = controller.ev;
end ClosedLoopComposed;
