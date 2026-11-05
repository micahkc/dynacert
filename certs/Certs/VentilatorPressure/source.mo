// ILLUSTRATIVE, NOT CLINICAL. Pressure-controlled ventilation: a blower delivers flow into
// the patient circuit (tubing compliance Cc), which fills a single-compartment lung
// (airway resistance R, compliance C). Illustrative adult-like values.
//
// Units: pressure cmH2O, flow L/s, compliance L/cmH2O, resistance cmH2O/(L/s), time s.
// The lung pressure follows a smooth reference P_ref (chain P_ref -> dP_ref -> ddP_ref).
// Flatness feedforward: the circuit pressure that drives the lung along P_ref is
// Paw_ref = P_ref + R*C*dP_ref, and the blower flow is C*dP_ref + Cc*dPaw_ref.
// R*C = 1 s is chosen so that the error frame Paw - P_ref - R*C*dP_ref has integer
// coefficients: dynacert (at the time of writing) emitted fractional frame coefficients
// into a computable Lean `def` and the build failed (Real division is noncomputable).
// Feedback: PI on the circuit-pressure error. Disturbance: an unknown circuit leak.
model VentilatorPressure
  parameter Real R = 20.0 "Airway resistance, intubated patient [cmH2O/(L/s)]";
  parameter Real C = 0.05 "Lung compliance [L/cmH2O]";
  parameter Real Cc = 0.002 "Circuit (tubing) compliance [L/cmH2O]";
  parameter Real kp = 0.05 "Proportional gain [(L/s)/cmH2O]";
  parameter Real ki = 0.5 "Integral gain [(L/s)/(cmH2O*s)]";

  input Real P_ref "Lung pressure reference above PEEP [cmH2O]"
    annotation(__Dynacert(reference(derivative = "dP_ref", start = 0)));
  input Real dP_ref "Reference pressure rate [cmH2O/s]"
    annotation(__Dynacert(reference(derivative = "ddP_ref", start = 0)));
  input Real ddP_ref "Reference pressure acceleration [cmH2O/s2]" annotation(__Dynacert(reference));
  input Real q_leak "Circuit leak flow [L/s]" annotation(__Dynacert(disturbance(bound = 0.05)));

  Real Paw(start = 0, fixed = true) "Circuit (airway opening) pressure above PEEP [cmH2O]";
  Real Pl(start = 0, fixed = true) "Alveolar pressure above PEEP [cmH2O]";
  Real xi(start = 0, fixed = true) "Integral of the circuit-pressure error [cmH2O*s]";

  Real Paw_ref "Circuit pressure that drives the lung along P_ref [cmH2O]";
  Real q_ff "Feedforward blower flow [L/s]";
  Real q_b "Blower flow [L/s]";
  Real e "Circuit pressure error [cmH2O]" annotation(__Dynacert(certify));
  Real el "Lung pressure error [cmH2O]" annotation(__Dynacert(certify));
  Real ei "Integral of the circuit pressure error [cmH2O*s]" annotation(__Dynacert(certify));
equation
  Paw_ref = P_ref + R*C*dP_ref;
  q_ff = C*dP_ref + Cc*(dP_ref + R*C*ddP_ref);
  e = Paw - Paw_ref;
  el = Pl - P_ref;
  ei = xi;
  q_b = q_ff - kp*e - ki*xi;
  der(xi) = e;
  Cc*der(Paw) = q_b - (Paw - Pl)/R - q_leak;
  C*der(Pl) = (Paw - Pl)/R;
end VentilatorPressure;
