// Two-area load-frequency control with a tie line (illustrative per-unit parameters).
// Each area: swing equation, first-order governor-turbine with droop, integral AGC on
// its own area control error ACE_i = beta_i*df_i +/- dPtie. Load steps in both areas are
// independent bounded disturbances. Deviation variables; time in seconds.
model TwoAreaTieLineLFC
  parameter Real H1 = 5.0 "Area 1 inertia constant [s] (illustrative)";
  parameter Real H2 = 4.0 "Area 2 inertia constant [s] (illustrative)";
  parameter Real D1 = 1.0 "Area 1 load damping [pu/pu] (illustrative)";
  parameter Real D2 = 1.0 "Area 2 load damping [pu/pu] (illustrative)";
  parameter Real Tg1 = 0.5 "Area 1 governor-turbine time constant [s] (illustrative)";
  parameter Real Tg2 = 0.6 "Area 2 governor-turbine time constant [s] (illustrative)";
  parameter Real R1 = 0.05 "Area 1 droop [pu/pu]";
  parameter Real R2 = 0.05 "Area 2 droop [pu/pu]";
  parameter Real beta1 = 21.0 "Area 1 frequency bias D1 + 1/R1 [pu/pu]";
  parameter Real beta2 = 21.0 "Area 2 frequency bias D2 + 1/R2 [pu/pu]";
  parameter Real Ki1 = 0.3 "Area 1 AGC integral gain [1/s] (illustrative)";
  parameter Real Ki2 = 0.3 "Area 2 AGC integral gain [1/s] (illustrative)";
  parameter Real Ts = 2.0 "Tie-line synchronizing coefficient [pu power/(pu frequency*s)] (illustrative)";

  input Real dPL1 "Area 1 load step [pu]" annotation(__Dynacert(disturbance(bound = 0.1)));
  input Real dPL2 "Area 2 load step [pu]" annotation(__Dynacert(disturbance(bound = 0.1)));

  Real df1(start = 0, fixed = true) "Area 1 frequency deviation [pu]" annotation(__Dynacert(certify));
  Real dPm1(start = 0, fixed = true) "Area 1 mechanical power deviation [pu]";
  Real dPc1(start = 0, fixed = true) "Area 1 AGC setpoint deviation [pu]";
  Real df2(start = 0, fixed = true) "Area 2 frequency deviation [pu]" annotation(__Dynacert(certify));
  Real dPm2(start = 0, fixed = true) "Area 2 mechanical power deviation [pu]";
  Real dPc2(start = 0, fixed = true) "Area 2 AGC setpoint deviation [pu]";
  Real dPtie(start = 0, fixed = true) "Tie-line power flow 1->2 deviation [pu]" annotation(__Dynacert(certify));
  Real ace1 "Area 1 control error [pu]";
  Real ace2 "Area 2 control error [pu]";
equation
  ace1 = beta1*df1 + dPtie;
  ace2 = beta2*df2 - dPtie;
  2*H1*der(df1) = dPm1 - dPL1 - D1*df1 - dPtie;
  2*H2*der(df2) = dPm2 - dPL2 - D2*df2 + dPtie;
  Tg1*der(dPm1) = -dPm1 + dPc1 - df1/R1;
  Tg2*der(dPm2) = -dPm2 + dPc2 - df2/R2;
  der(dPc1) = -Ki1*ace1;
  der(dPc2) = -Ki2*ace2;
  der(dPtie) = Ts*(df1 - df2);
end TwoAreaTieLineLFC;
