model AsymmetricDamper "Quarter-car body mode with a two-stage damper: stiffer in rebound (extension) than in compression"
  parameter Real m = 1.0 "sprung mass (normalized)";
  parameter Real k = 4.0 "spring stiffness";
  parameter Real cComp = 0.8 "damping in compression";
  parameter Real cReb = 2.0 "damping in rebound";
  input Real f "road / load force" annotation(__Dynacert(disturbance(bound = 0.5)));
  Real x(start = 0, fixed = true) "body displacement" annotation(__Dynacert(certify));
  Real v(start = 0, fixed = true) "body velocity" annotation(__Dynacert(certify));
equation
  der(x) = v;
  m*der(v) = -k*x - (if v > 0 then cReb else cComp)*v + f;
end AsymmetricDamper;
