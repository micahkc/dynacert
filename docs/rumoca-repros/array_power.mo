model array_power
  input Real d;
  Real x[3](each start = 0, each fixed = true);
  Real y;
equation
  der(x) = -x + {d,d,d}; y = sum(x.^2);
end array_power;
