model fill
  input Real d;
  Real x[3](each start = 0, each fixed = true);
  
equation
  der(x) = -x + fill(d, 3);
end fill;
