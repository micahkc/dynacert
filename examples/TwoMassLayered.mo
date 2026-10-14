// Two damped oscillators coupled by a weak spring, written as two instances of one
// component. `structure` reports the two sub-components as coupled layers; the `layered`
// approach certifies each with the other's position as a bounded disturbance and closes the
// loop with `Compose.assume_guarantee` (mutual first exit).

model Oscillator
  parameter Real k = 1.0;
  parameter Real c = 1.0;
  input Real F;
  Real x(start = 0, fixed = true) annotation(__Dynacert(certify));
  Real v(start = 0, fixed = true);
equation
  der(x) = v;
  der(v) = -k*x - c*v + F;
end Oscillator;

model TwoMassLayered
  parameter Real kc = 0.2 "coupling spring";
  input Real d1 annotation(__Dynacert(disturbance(bound = 1.0)));
  input Real d2 annotation(__Dynacert(disturbance(bound = 0.5)));
  Oscillator a(k = 1.0, c = 1.2);
  Oscillator b(k = 2.0, c = 1.5);
equation
  a.F = kc*(b.x - a.x) + d1;
  b.F = kc*(a.x - b.x) + d2;
end TwoMassLayered;
