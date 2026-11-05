// Robot joint with a flexible transmission (harmonic drive / belt), two-mass model.
// Illustrative parameters, not taken from a specific robot.
//
// The link angle q_l follows a smooth reference with full flatness-based feedforward:
// with the transmission spring k between motor and link, the motor angle and motor torque
// that make q_l = q_ref exact are functions of q_ref and its derivatives up to snap, so the
// reference chain is q_ref -> w_ref -> a_ref -> j_ref -> s_ref (snap, free).
// Feedback: PD on the motor error plus link-velocity damping (link encoder).
// The certified motor-side coordinates are the spring-torque error k*(qm - ql) - tau_s_ref
// and its rate (physically: the torque carried by the transmission). With Jl = 1 and
// bl = 1 these have integer coefficients in the references; dynacert (at the time of
// writing) emitted fractional frame coefficients such as -1/400 into a computable Lean
// `def` and the build failed (Real division is noncomputable), so the motor-angle error
// qm - qm_ref (coefficients Jl/k, bl/k) could not be certified directly.
// Disturbances: load torque on the link (payload contact, gravity mismatch) and motor
// torque ripple.
model FlexibleJointServo
  parameter Real Jm = 0.05 "Motor inertia reflected to the link side [kg*m2]";
  parameter Real Jl = 1.0 "Link inertia [kg*m2]";
  parameter Real k = 200.0 "Transmission stiffness [N*m/rad]";
  parameter Real bm = 0.05 "Motor viscous friction [N*m*s/rad]";
  parameter Real bl = 1.0 "Link viscous friction [N*m*s/rad]";
  parameter Real kp = 100.0 "Motor position gain [N*m/rad]";
  parameter Real kd = 6.0 "Motor velocity gain [N*m*s/rad]";
  parameter Real kl = 10.0 "Link velocity damping gain [N*m*s/rad]";

  input Real q_ref "Link angle reference [rad]"
    annotation(__Dynacert(reference(derivative = "w_ref", start = 0)));
  input Real w_ref "Link rate reference [rad/s]"
    annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref "Link acceleration reference [rad/s2]"
    annotation(__Dynacert(reference(derivative = "j_ref", start = 0)));
  input Real j_ref "Link jerk reference [rad/s3]"
    annotation(__Dynacert(reference(derivative = "s_ref", start = 0)));
  input Real s_ref "Link snap reference [rad/s4]" annotation(__Dynacert(reference));
  input Real tau_load "Load torque on the link [N*m]"
    annotation(__Dynacert(disturbance(bound = 2.0)));
  input Real tau_rip "Motor torque ripple [N*m]"
    annotation(__Dynacert(disturbance(bound = 0.5)));

  Real ql(start = 0, fixed = true) "Link angle [rad]";
  Real wl(start = 0, fixed = true) "Link rate [rad/s]";
  Real qm(start = 0, fixed = true) "Motor angle (link side) [rad]";
  Real wm(start = 0, fixed = true) "Motor rate (link side) [rad/s]";

  Real qm_ref "Motor angle that realises q_ref [rad]";
  Real wm_ref "Motor rate that realises q_ref [rad/s]";
  Real am_ref "Motor acceleration that realises q_ref [rad/s2]";
  Real tau_ff "Feedforward torque [N*m]";
  Real tau "Motor torque [N*m]";

  Real e_l "Link angle error [rad]" annotation(__Dynacert(certify));
  Real ev_l "Link rate error [rad/s]" annotation(__Dynacert(certify));
  Real e_m "Motor angle error [rad]";
  Real ev_m "Motor rate error [rad/s]";
  Real e_s "Transmission torque error k*(qm - ql) - (Jl*a_ref + bl*w_ref) [N*m]"
    annotation(__Dynacert(certify));
  Real ev_s "Transmission torque rate error [N*m/s]" annotation(__Dynacert(certify));
equation
  // Flatness: Jl q'' = k (qm - ql) - bl q'  =>  qm = q + (Jl q'' + bl q')/k
  qm_ref = q_ref + (Jl*a_ref + bl*w_ref)/k;
  wm_ref = w_ref + (Jl*j_ref + bl*a_ref)/k;
  am_ref = a_ref + (Jl*s_ref + bl*j_ref)/k;
  tau_ff = Jm*am_ref + bm*wm_ref + k*(qm_ref - q_ref);

  e_l = ql - q_ref;
  ev_l = wl - w_ref;
  e_m = qm - qm_ref;
  ev_m = wm - wm_ref;
  e_s = k*(qm - ql) - (Jl*a_ref + bl*w_ref);
  ev_s = k*(wm - wl) - (Jl*j_ref + bl*a_ref);
  tau = tau_ff - kp*e_m - kd*ev_m - kl*ev_l;

  der(ql) = wl;
  Jl*der(wl) = k*(qm - ql) - bl*wl + tau_load;
  der(qm) = wm;
  Jm*der(wm) = tau + tau_rip - bm*wm - k*(qm - ql);
end FlexibleJointServo;
