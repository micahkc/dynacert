model BumpStopSuspension "Quarter-car body mode with a three-stage damper (rebound, compression, low-speed bleed) and a progressive bump stop: 3 x 2 = 6 linear modes"
  parameter Real m = 1.0 "sprung mass (normalized)";
  parameter Real k = 4.0 "main spring stiffness";
  parameter Real kStop = 4.0 "bump-stop stiffness added beyond the free travel";
  parameter Real xFree = 0.3 "free travel before the bump stop engages";
  parameter Real vKnee = 0.2 "velocity above which the high-speed valves open";
  parameter Real cReb = 2.0 "high-speed rebound damping";
  parameter Real cComp = 1.2 "high-speed compression damping";
  parameter Real cBleed = 3.0 "low-speed bleed damping";
  input Real f "road / load force" annotation(__Dynacert(disturbance(bound = 0.5)));
  Real x(start = 0, fixed = true) "body displacement" annotation(__Dynacert(certify));
  Real v(start = 0, fixed = true) "body velocity" annotation(__Dynacert(certify));
equation
  der(x) = v;
  m*der(v) = -(if abs(x) > xFree then k + kStop else k)*x
             - (if v > vKnee then cReb elseif v < -vKnee then cComp else cBleed)*v + f;
end BumpStopSuspension;
