model SwitchedUnstable "Two stable oscillators switched by quadrant: each mode is stable, the switched system is not (no common quadratic storage exists)"
  input Real d annotation(__Dynacert(disturbance(bound = 0.1)));
  Real x1(start = 0, fixed = true) annotation(__Dynacert(certify));
  Real x2(start = 0, fixed = true) annotation(__Dynacert(certify));
equation
  der(x1) = -0.1*x1 - (if x1*x2 > 0 then 1.0 else 2.0)*x2 + d;
  der(x2) = (if x1*x2 > 0 then 2.0 else 1.0)*x1 - 0.1*x2;
end SwitchedUnstable;
