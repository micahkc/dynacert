package NestedRedeclare
  partial model C input Real x; output Real u; end C;
  model C1 extends C; equation u = -x; end C1;
  model C2 extends C; equation u = -2*x; end C2;
  model Loop
    replaceable C1 ctrl constrainedby C;
    Real x(start = 1, fixed = true);
  equation ctrl.x = x; der(x) = ctrl.u;
  end Loop;
  model Outer Loop cl; end Outer;
  model Direct = Loop(redeclare C2 ctrl);        // works: u = -2*x
  model Nested = Outer(cl(redeclare C2 ctrl));   // expected u = -2*x; got C1
end NestedRedeclare;
