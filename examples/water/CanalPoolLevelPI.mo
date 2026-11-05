// Irrigation canal pool, distant-downstream level control: the upstream gate flow is set
// by a PI controller on the downstream water level; the gate flow reaches the downstream
// end after a transport delay, modelled by a first-order Pade approximation
// (integrator-delay pool model). Illustrative numbers for a medium canal pool;
// time in minutes, flows in m3/min. Disturbance: unscheduled offtake. Deviation variables.
model CanalPoolLevelPI
  parameter Real As = 6000.0 "Pool backwater surface area [m2] (illustrative)";
  parameter Real tau = 8.0 "Transport delay [min] (illustrative)";
  parameter Real kp = 250.0 "PI proportional gain [m3/(min*m)]";
  parameter Real ki = 2.5 "PI integral gain [m3/(min2*m)]";

  input Real dqoff "Offtake flow deviation [m3/min] (0.5 m3/s)" annotation(__Dynacert(disturbance(bound = 30.0)));

  Real dy(start = 0, fixed = true) "Downstream level deviation [m]" annotation(__Dynacert(certify));
  Real xp(start = 0, fixed = true) "Pade delay state [m3/min]";
  Real z(start = 0, fixed = true) "Integral of level error [m*min]";
  Real dqc "Upstream gate flow command deviation [m3/min]" annotation(__Dynacert(certify));
  Real dqd "Delayed gate flow at the downstream end [m3/min]";
equation
  dqc = -kp*dy - ki*z;
  der(z) = dy;
  tau*der(xp) = 2*(dqc - xp);
  dqd = 2*xp - dqc;
  As*der(dy) = dqd - dqoff;
end CanalPoolLevelPI;
