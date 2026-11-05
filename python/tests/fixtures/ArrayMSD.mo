model ArrayMSD "Three decoupled-ish mass-spring-dampers with array variables"
  parameter Real m = 1.0;
  parameter Real K[3,3] = {{2.0, 0.1, 0}, {0, 3.0, 0}, {0.2, 0, 1.5}} "Stiffness matrix";
  parameter Real c[3] = {0.8, 1.0, 1.2} "Damping";
  parameter Real p0[3] = {0, 0, 0} "Initial positions";
  input Real d[3] annotation(__Dynacert(disturbance(bound = 0.5)));
  Real x[3](start = p0, each fixed = true);
  Real v[3](start = {0, 0, 0}, each fixed = true);
  Real e[3] annotation(__Dynacert(certify));
equation
  der(x) = v;
  for i in 1:3 loop
    m * der(v[i]) = -(K * x)[i] - c[i] * v[i] + d[i];
  end for;
  e = 2 * x;
end ArrayMSD;
