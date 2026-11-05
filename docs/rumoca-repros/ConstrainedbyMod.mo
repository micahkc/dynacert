package ConstrainedbyMod
  model Plant parameter Real x0 = 0; Real x(start = x0, fixed = true); equation der(x) = -x; end Plant;
  model Plant2 extends Plant; end Plant2;
  model Top
    replaceable Plant p constrainedby Plant(x0 = 5);   // MLS 7.3.2: x0 = 5 applies here too
  end Top;
  model Top2 = Top(redeclare Plant2 p);                // x0 = 5 (applied)
end ConstrainedbyMod;
