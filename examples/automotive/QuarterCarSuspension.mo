// Active quarter-car suspension with skyhook damping, driven by road roughness.
//
// Classic two-mass quarter-car model written in deflection coordinates, so the road
// enters only through its vertical velocity:
//   susp_defl = z_body  - z_wheel   (suspension stroke, rattle space)
//   tire_defl = z_wheel - z_road    (tire compression, road holding)
// The actuator applies a skyhook force F = -c_sky * v_body in parallel with the passive
// spring and damper. The road vertical velocity is a bounded disturbance.
//
// Certified: suspension stroke and tire deflection stay bounded for every road profile whose
// vertical velocity stays within the bound (rattle space and road-holding requirements).
// All parameter values are illustrative (typical passenger-car order of magnitude).
model QuarterCarSuspension
  parameter Real m_s = 300.0 "Sprung (body) mass per corner [kg]";
  parameter Real m_u = 40.0 "Unsprung (wheel) mass [kg]";
  parameter Real k_s = 16000.0 "Suspension spring stiffness [N/m]";
  parameter Real c_s = 1000.0 "Passive suspension damping [N*s/m]";
  parameter Real k_t = 190000.0 "Tire vertical stiffness [N/m]";
  parameter Real c_sky = 3000.0 "Skyhook damping gain [N*s/m]";

  input Real w_road "Road vertical velocity [m/s]"
    annotation(__Dynacert(disturbance(bound = 0.3)));

  Real susp_defl(start = 0, fixed = true) "Suspension deflection z_body - z_wheel [m]"
    annotation(__Dynacert(certify));
  Real v_body(start = 0, fixed = true) "Body vertical velocity [m/s]";
  Real tire_defl(start = 0, fixed = true) "Tire deflection z_wheel - z_road [m]"
    annotation(__Dynacert(certify));
  Real v_wheel(start = 0, fixed = true) "Wheel vertical velocity [m/s]";
  Real F_act "Active suspension force on the body [N]";
  Real F_susp "Passive spring + damper force on the body [N]";
equation
  F_act = -c_sky*v_body;
  F_susp = -k_s*susp_defl - c_s*(v_body - v_wheel);
  der(susp_defl) = v_body - v_wheel;
  der(tire_defl) = v_wheel - w_road;
  m_s*der(v_body) = F_susp + F_act;
  m_u*der(v_wheel) = -F_susp - F_act - k_t*tire_defl;
end QuarterCarSuspension;
