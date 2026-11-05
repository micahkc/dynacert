// Averaged synchronous buck converter with a cascaded PI voltage / P current loop that
// tracks a soft-start output-voltage reference (illustrative component values).
// Time is in milliseconds, inductance in mH and capacitance in mF, so that
// L*di/dt [V] and C*dv/dt [A] keep SI voltage and current.
// The reference chain v_ref' = dv_ref, dv_ref' = ddv_ref is declared; the feedforward
// (inductor-current and duty-cycle reference) is computed here from the reference and
// the nominal load. Duty-cycle saturation (0..1) is not modelled: the claim is about the
// averaged, unsaturated loop.
// C and Rload are chosen so that the error frame i - (C*dv_ref + v_ref/Rload) has integer
// coefficients: with C = 0.47 the generated Cert.lean fails to compile (`def vec` with a
// rational coefficient needs `noncomputable`; a dynacert emitter issue).
model BuckConverterPI
  parameter Real Vin = 12.0 "Input voltage [V]";
  parameter Real L = 0.1 "Inductance [mH] (100 uH, illustrative)";
  parameter Real C = 1.0 "Output capacitance [mF] (1000 uF, illustrative)";
  parameter Real Rload = 1.0 "Nominal load resistance [Ohm] (5 A at 5 V, illustrative)";
  parameter Real kc = 0.5 "Current-loop proportional gain [V/A]";
  parameter Real kv = 5.0 "Voltage-loop proportional gain [V/V]";
  parameter Real ki = 10.0 "Voltage-loop integral gain [V/(V*ms)]";

  input Real v_ref "Output voltage reference [V]"
    annotation(__Dynacert(reference(derivative = "dv_ref", start = 0)));
  input Real dv_ref "Reference slew rate [V/ms]"
    annotation(__Dynacert(reference(derivative = "ddv_ref", start = 0)));
  input Real ddv_ref "Reference slew acceleration [V/ms2]" annotation(__Dynacert(reference));
  input Real i_load "Load current step beyond the resistive load [A]"
    annotation(__Dynacert(disturbance(bound = 2.0)));

  Real i(start = 0, fixed = true) "Inductor current [A]";
  Real v(start = 0, fixed = true) "Output voltage [V]";
  Real z(start = 0, fixed = true) "Integral of voltage error [V*ms]" annotation(__Dynacert(certify));
  Real i_ref "Inductor current reference [A]";
  Real di_ref "Inductor current reference rate [A/ms]";
  Real duty "Duty cycle (unsaturated) [1]";
  Real e "Output voltage error [V]" annotation(__Dynacert(certify));
  Real ei "Inductor current error [A]" annotation(__Dynacert(certify));
equation
  i_ref = C*dv_ref + v_ref/Rload;
  di_ref = C*ddv_ref + dv_ref/Rload;
  e = v - v_ref;
  ei = i - i_ref;
  der(z) = e;
  duty*Vin = L*di_ref + v_ref - kc*ei - kv*e - ki*z;
  L*der(i) = duty*Vin - v;
  C*der(v) = i - v/Rload - i_load;
end BuckConverterPI;
