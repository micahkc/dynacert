// Two planar (2-axis) oscillators with array states, weakly coupled; layered fixture for
// scalarization (each component's array elements stay in its layer).

model Oscillator2
  parameter Real k[2] = {1.0, 1.5};
  parameter Real c = 1.0;
  input Real F[2];
  Real x[2](each start = 0, each fixed = true) annotation(__Dynacert(certify));
  Real v[2](each start = 0, each fixed = true);
equation
  der(x) = v;
  for i in 1:2 loop
    der(v[i]) = -k[i]*x[i] - c*v[i] + F[i];
  end for;
end Oscillator2;

model ArrayLayered
  parameter Real kc = 0.2 "coupling spring";
  input Real d[2] annotation(__Dynacert(disturbance(bound = 0.5)));
  input Real w[2] annotation(__Dynacert(disturbance(bound = {0.2, 0.1})));
  Oscillator2 a(k = {1.0, 1.2}, c = 1.2);
  Oscillator2 b(k = {2.0, 2.5}, c = 1.5);
equation
  a.F = kc*(b.x - a.x) + d;
  b.F = kc*(a.x - b.x) + w;
end ArrayLayered;
