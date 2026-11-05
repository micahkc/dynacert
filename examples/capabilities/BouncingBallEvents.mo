// `when` and `reinit`: a state jump. rumoca's Lean export rejects discrete events, and dynacert
// reports that instead of dropping them from the claim.
//
//   dynacert examples/capabilities/BouncingBallEvents.mo
model BouncingBallEvents
  parameter Real g = 9.81;
  parameter Real e = 0.8 "Restitution";
  input Real d annotation(__Dynacert(disturbance(bound = 0.1)));
  Real h(start = 1, fixed = true) annotation(__Dynacert(certify));
  Real v(start = 0, fixed = true);
equation
  der(h) = v;
  der(v) = -g + d;
  when h < 0 then
    reinit(v, -e*pre(v));
  end when;
end BouncingBallEvents;
