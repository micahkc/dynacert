// Web (film / paper) tension control on a conveyor span between a speed-controlled leader
// roller and a torque-controlled follower roller. Linearized about the running condition;
// all variables are deviations. Illustrative parameters.
//
// Span: dT/dt = (E*A/L)*(v_f - v_lead) - (v0/L)*T  (strain transport, linearized)
// Follower roller (equivalent translational mass M = J/R^2): M dv_f/dt = F - T - b v_f
// Controller: PI on the tension error with speed damping (integrator as a state).
model WebTensionControl
  parameter Real EA = 5000.0 "Web axial stiffness E*A [N]";
  parameter Real L = 1.0 "Span length [m]";
  parameter Real v0 = 2.0 "Line speed [m/s]";
  parameter Real M = 5.0 "Follower roller equivalent mass J/R^2 [kg]";
  parameter Real b = 2.0 "Roller bearing friction [N*s/m]";
  parameter Real kp = 2.0 "Tension gain [N/N]";
  parameter Real ki = 20.0 "Tension integral gain [N/(N*s)]";
  parameter Real kv = 300.0 "Speed damping gain [N*s/m]";

  input Real v_lead "Leader roller speed fluctuation [m/s]"
    annotation(__Dynacert(disturbance(bound = 0.01)));
  input Real F_d "Torque disturbance on the follower (eccentricity, bearing drag) [N]"
    annotation(__Dynacert(disturbance(bound = 2.0)));

  Real T(start = 0, fixed = true) "Tension deviation [N]" annotation(__Dynacert(certify));
  Real v_f(start = 0, fixed = true) "Follower surface speed deviation [m/s]"
    annotation(__Dynacert(certify));
  Real xi(start = 0, fixed = true) "Integral of the tension error [N*s]"
    annotation(__Dynacert(certify));
  Real F "Follower drive force at the roller surface [N]";
equation
  F = -kp*T - ki*xi - kv*v_f;
  der(xi) = T;
  der(T) = (EA/L)*(v_f - v_lead) - (v0/L)*T;
  M*der(v_f) = F + F_d - T - b*v_f;
end WebTensionControl;
