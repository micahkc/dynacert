model slice
  input Real d;
  Real x[3](each start = 0, each fixed = true);
  Real y[2];
equation
  der(x) = -x + {d,d,d}; y = x[2:3];
end slice;
