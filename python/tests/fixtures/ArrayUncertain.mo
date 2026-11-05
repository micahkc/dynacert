// Two damped axes with an uncertain damping array and an initial box on an array state
// (scalarization fixture: per-component uncertain(min, max) and initialSet).
model ArrayUncertain
  parameter Real c[2] = {1.0, 1.5} annotation(__Dynacert(uncertain(min = 0.8, max = {1.2, 1.8})));
  parameter Real k = 2.0;
  input Real d[2] annotation(__Dynacert(disturbance(bound = 0.3)));
  Real x[2](each start = 0, each fixed = true) annotation(__Dynacert(initialSet(min = -0.1, max = 0.1)));
  Real v[2](each start = 0, each fixed = true);
  Real s annotation(__Dynacert(certify));
equation
  der(x) = v;
  der(v) = -k * x - {c[1]*v[1], c[2]*v[2]} + d;
  s = x[1] + x[2];
end ArrayUncertain;
