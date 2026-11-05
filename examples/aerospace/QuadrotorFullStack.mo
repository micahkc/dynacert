// Full-stack quadrotor on SE₂(3), written against the LieGroups library
// (modelica_models/LieGroups; put it on MODELICAPATH or pass --source-root).
//
//   reference ──► ctrl: FlightController ──► mixer ──► motors ──► rigid body
//   (X̄, ω̄, f̄, ᾱ)      (f_cmd, τ_cmd)          (f_cmd,i)   (f_i)       (X, ω)
//
// The controller is replaceable. Everything else, including the certified outputs, is defined by
// the plant and the reference only, so every controller is judged against the same claim and only
// the bound changes:
//
//   ClosedLoop      log-linear SE₂(3) controller + rate loop (SE23LogLinear, the default)
//   ClosedLoopPID   ArduCopter-style cascade: position P → velocity PID → lean angles →
//                   angle P → rate PID (ArduPilotPID)
//
// To try another controller, extend FlightController and redeclare it:
//   model ClosedLoopMine = ClosedLoop(redeclare MyController ctrl);
//
// Frames: world z up, gravity {0, 0, -g}; body FLU, thrust along +z_b. Group element
// X = {p, v, q} (world position, world velocity, body→world quaternion), as in
// LieGroups.SE23.Quat. The vehicle and the reference satisfy the same SE₂(3) kinematics
//   ṗ = v,  v̇ = R a + g,  Ṙ = R·[ω]×
// with a = specific force in the body frame.

package QuadrotorFullStack

  // ───────────────────────────── plant ─────────────────────────────

  model RigidBody "6-DOF rigid body: SE₂(3) kinematics (quaternion chart) + Euler's equations"
    parameter Real m = 1.5 "mass [kg]";
    parameter Real g = 9.81;
    parameter Real Jxx = 0.02;
    parameter Real Jyy = 0.02;
    parameter Real Jzz = 0.04;
    parameter Real p0[3] = {0, 0, 0};
    parameter Real v0[3] = {0, 0, 0};
    parameter Real q0[4] = {1, 0, 0, 0};
    parameter Real w0[3] = {0, 0, 0};
    input Real F_b[3] "non-gravity force, body frame [N]";
    input Real tau_b[3] "torque, body frame [N·m]";
    Real p[3](start = p0, each fixed = true);
    Real v[3](start = v0, each fixed = true);
    Real q[4](start = q0, each fixed = true);
    Real w[3](start = w0, each fixed = true) "body rates";
    Real R[3,3] "body → world";
    Real X[10] "SE₂(3) element {p, v, q}";
  protected
    parameter Real J[3,3] = {{Jxx, 0, 0}, {0, Jyy, 0}, {0, 0, Jzz}};
  equation
    R = LieGroups.SO3.Quat.to_DCM(q);
    X = cat(1, p, v, q);
    der(p) = v;
    der(v) = R*F_b/m + {0, 0, -g};
    der(q) = LieGroups.SO3.Quat.kinematics(q, w);
    J*der(w) = tau_b - cross(w, J*w);
  end RigidBody;

  model Mixer "Quad-X allocation, exact inverse (the allocation matrix has orthogonal rows)"
    parameter Real l = 0.18 "motor offset along body x and y [m]";
    parameter Real km = 0.016 "yaw moment per unit thrust [m]";
    parameter Real m = 1.5;
    input Real f_cmd "specific thrust [m/s²]";
    input Real tau_cmd[3];
    output Real fm_cmd[4] "per-motor thrust commands [N]";
  protected
    // motor i at (x_i, y_i), spin sign s_i: 1 front-right, 2 rear-left, 3 front-left, 4 rear-right
    parameter Real x[4] = {l, -l, l, -l};
    parameter Real y[4] = {-l, l, l, -l};
    parameter Real s[4] = {1, 1, -1, -1};
    Real T "collective thrust [N]";
  equation
    T = m*f_cmd;
    for i in 1:4 loop
      fm_cmd[i] = T/4 + y[i]*tau_cmd[1]/(4*l^2) - x[i]*tau_cmd[2]/(4*l^2) + s[i]*tau_cmd[3]/(4*km);
    end for;
  end Mixer;

  model Motors "Four first-order thrust lags; output the body wrench"
    parameter Real tau_m = 0.02 "motor time constant [s]";
    parameter Real l = 0.18;
    parameter Real km = 0.016;
    parameter Real f0 = 1.5*9.81/4 "hover thrust per motor [N]";
    input Real fm_cmd[4];
    Real fm[4](each start = f0, each fixed = true) "motor thrusts [N]";
    output Real F_b[3];
    output Real tau_b[3];
  protected
    parameter Real x[4] = {l, -l, l, -l};
    parameter Real y[4] = {-l, l, l, -l};
    parameter Real s[4] = {1, 1, -1, -1};
  equation
    der(fm) = (fm_cmd - fm)/tau_m;
    F_b = {0, 0, sum(fm)};
    tau_b = {y*fm, -(x*fm), km*(s*fm)};
  end Motors;

  model Reference "Reference on SE₂(3): same kinematics, driven by feedforward thrust and ω̇"
    parameter Real g = 9.81;
    parameter Real p0[3] = {0, 0, 0};
    parameter Real v0[3] = {0, 0, 0};
    parameter Real q0[4] = {1, 0, 0, 0};
    parameter Real w0[3] = {0, 0, 0};
    input Real f "specific thrust along z_b [m/s²]";
    input Real alpha[3] "body angular acceleration [rad/s²]";
    Real p[3](start = p0, each fixed = true);
    Real v[3](start = v0, each fixed = true);
    Real q[4](start = q0, each fixed = true);
    Real w[3](start = w0, each fixed = true);
    Real R[3,3];
    Real X[10];
  equation
    R = LieGroups.SO3.Quat.to_DCM(q);
    X = cat(1, p, v, q);
    der(p) = v;
    der(v) = R*{0, 0, f} + {0, 0, -g};
    der(q) = LieGroups.SO3.Quat.kinematics(q, w);
    der(w) = alpha;
  end Reference;

  // ─────────────────────────── controllers ───────────────────────────

  partial model FlightController "What every controller sees and commands"
    parameter Real g = 9.81;
    parameter Real Jxx = 0.02 "inertia the controller assumes";
    parameter Real Jyy = 0.02;
    parameter Real Jzz = 0.04;
    input Real X[10] "vehicle state estimate {p, v, q}";
    input Real w[3] "gyro: body rates";
    input Real Xr[10] "reference {p̄, v̄, q̄}";
    input Real w_ref[3] "reference body rates ω̄";
    input Real f_ref "reference specific thrust f̄";
    input Real alpha_ref[3] "reference angular acceleration ᾱ";
    output Real f_cmd "specific thrust command [m/s²]";
    output Real tau_cmd[3] "body torque command [N·m]";
    output Real w_cmd[3] "rate setpoint (diagnostic; not part of the claim)";
  protected
    parameter Real J[3,3] = {{Jxx, 0, 0}, {0, Jyy, 0}, {0, 0, Jzz}};
  end FlightController;

  model SE23LogLinear "Log-linear SE₂(3) tracking controller + body-rate loop"
    // With the left error η = X̄⁻¹X gravity cancels exactly and ξ = log(η) obeys
    //   ξ̇ = (A_C − ad_n̄) ξ + J_r⁻¹(ξ) Δ,   Δ = (0, a − ā, ω − ω̄),   n̄ = (0, ā, ω̄),
    // with A_C ξ = (ξ_v, 0, 0). The law requests Δ = J_r(ξ)·B·(−K ξ) and realizes the actuated
    // part (thrust along z_b, the three body rates); K is LQR at hover on (A_C − ad_n̄, B). What
    // remains is the unactuated a_x, a_y part of J_r B K ξ (O(‖ξ‖²)), the rate loop's tracking
    // error ω − ω_cmd, and the motor lag.
    extends FlightController;
    parameter Real K[4,9] = {
      {0,    0,   1,   0,      0,      1.5811, 0,      0,      0},
      {0,   -0.5, 0,   0,     -0.7141, 0,      3.7763, 0,      0},
      {0.5,  0,   0,   0.7141, 0,      0,      0,      3.7763, 0},
      {0,    0,   0,   0,      0,      0,      0,      0,      1}}
      "LQR at hover; input order (δf, δω_x, δω_y, δω_z), state order (ξ_p, ξ_v, ξ_R)";
    parameter Real kw = 20 "rate bandwidth [rad/s]";
    Real xi[9] "log(X̄⁻¹X) = {ξ_p, ξ_v, ξ_R}";
    Real u[4] "linear law −K ξ";
    Real Bu[9];
    Real Jr[9,9] "right Jacobian J_r(ξ) = J_l(−ξ)";
    Real delta[9] "requested Δ = J_r(ξ) B u";
  equation
    xi = LieGroups.SE23.Quat.log_map(
           LieGroups.SE23.Quat.product(LieGroups.SE23.Quat.inverse(Xr), X));
    u = -K*xi;
    Bu = {0, 0, 0, 0, 0, u[1], u[2], u[3], u[4]};
    Jr = LieGroups.SE23.Quat.left_jacobian(-xi);
    delta = Jr*Bu;
    f_cmd = f_ref + delta[6];
    w_cmd = w_ref + delta[7:9];
    tau_cmd = J*(alpha_ref + kw*(w_cmd - w)) + cross(w, J*w);
  end SE23LogLinear;

  model ArduPilotPID "ArduCopter-style cascade (AC_PosControl + AC_AttitudeControl)"
    // position P → velocity PID (+ accel feedforward) → lean angles (accel_to_lean_angles, with
    // ANGLE_MAX) → target quaternion → angle P on the quaternion error (+ rate feedforward) →
    // rate PID with filtered D → torque. Thrust: (g + a_z)/cos(tilt) (angle boost).
    // Departures from ArduCopter: continuous time; plain P where ArduPilot uses sqrt_controller
    // (identical in its linear region); no I-term limits (IMAX) or input shaping; the z
    // accel PID is folded into a velocity PI; rate gains are in SI (rad/s² per rad/s), i.e.
    // ArduPilot's normalized gains times torque authority / inertia.
    extends FlightController;
    // AC_PosControl
    parameter Real kp_pos_xy = 1.0 "PSC_POSXY_P [1/s]";
    parameter Real kp_vel_xy = 2.0 "PSC_VELXY_P [1/s]";
    parameter Real ki_vel_xy = 1.0 "PSC_VELXY_I [1/s²]";
    parameter Real kd_vel_xy = 0.5 "PSC_VELXY_D [-]";
    parameter Real fc_vel_d = 5 "PSC_VELXY_FLTD [Hz]";
    parameter Real kp_pos_z = 1.0 "PSC_POSZ_P [1/s]";
    parameter Real kp_vel_z = 5.0 "PSC_VELZ_P [1/s]";
    parameter Real ki_vel_z = 2.0 "stands in for PSC_ACCZ_I [1/s²]";
    parameter Real angle_max = 0.5236 "ANGLE_MAX (30°) [rad]";
    // AC_AttitudeControl
    parameter Real kp_ang_rp = 4.5 "ATC_ANG_RLL_P / ATC_ANG_PIT_P [1/s]";
    parameter Real kp_ang_yaw = 4.5 "ATC_ANG_YAW_P [1/s]";
    parameter Real kp_rate_rp = 20 "ATC_RAT_RLL_P 0.135 × 144 [1/s]";
    parameter Real ki_rate_rp = 20 "ATC_RAT_RLL_I 0.135 × 144 [1/s²]";
    parameter Real kd_rate_rp = 0.5 "ATC_RAT_RLL_D 0.0036 × 144 [-]";
    parameter Real fc_rate_d = 20 "ATC_RAT_RLL_FLTD [Hz]";
    parameter Real kp_rate_yaw = 2.5 "ATC_RAT_YAW_P 0.18 × 13 [1/s]";
    parameter Real ki_rate_yaw = 0.25 "ATC_RAT_YAW_I 0.018 × 13 [1/s²]";
    // position / velocity loop
    Real Rr[3,3] "reference attitude";
    Real a_ff[3] "reference acceleration, world";
    Real v_tgt[3] "velocity target";
    Real ev[3] "velocity error";
    Real iv[3](each start = 0, each fixed = true) "∫ ev";
    Real evf[3](each start = 0, each fixed = true) "ev through the D filter";
    Real a_tgt[3] "acceleration target, world";
    // lean angles and attitude
    Real yaw_t "heading target (from the reference)";
    Real a_fwd "a_tgt along the heading";
    Real a_lft "a_tgt left of the heading";
    Real pitch_t;
    Real roll_t;
    Real q_t[4] "target attitude";
    Real e_att[3] "body-frame attitude error log(q⁻¹ q_t)";
    Real R33 "cos(tilt) of the vehicle";
    // rate loop
    Real ew[3] "rate error";
    Real iw[3](each start = 0, each fixed = true) "∫ ew";
    Real ewf[3](each start = 0, each fixed = true) "ew through the D filter";
    Real alpha_cmd[3] "angular-acceleration command";
  protected
    parameter Real wd_v = 2*3.14159265358979*fc_vel_d;
    parameter Real wd_r = 2*3.14159265358979*fc_rate_d;
  equation
    // AC_PosControl: position P → velocity PID → acceleration target
    Rr = LieGroups.SO3.Quat.to_DCM(Xr[7:10]);
    a_ff = Rr*{0, 0, f_ref} - {0, 0, g};
    v_tgt = Xr[4:6] + {kp_pos_xy*(Xr[1] - X[1]), kp_pos_xy*(Xr[2] - X[2]), kp_pos_z*(Xr[3] - X[3])};
    ev = v_tgt - X[4:6];
    der(iv) = ev;
    der(evf) = wd_v*(ev - evf);
    a_tgt[1:2] = a_ff[1:2] + kp_vel_xy*ev[1:2] + ki_vel_xy*iv[1:2] + kd_vel_xy*wd_v*(ev[1:2] - evf[1:2]);
    a_tgt[3] = a_ff[3] + kp_vel_z*ev[3] + ki_vel_z*iv[3];
    // accel_to_lean_angles (FLU, z up), limited to ANGLE_MAX
    yaw_t = atan2(Rr[2,1], Rr[1,1]);
    a_fwd = a_tgt[1]*cos(yaw_t) + a_tgt[2]*sin(yaw_t);
    a_lft = -a_tgt[1]*sin(yaw_t) + a_tgt[2]*cos(yaw_t);
    pitch_t = LieGroups.Util.saturate(atan(a_fwd/g), -angle_max, angle_max);
    roll_t = LieGroups.Util.saturate(atan(-a_lft*cos(pitch_t)/g), -angle_max, angle_max);
    q_t = LieGroups.SO3.EulerB321.to_Quat({yaw_t, pitch_t, roll_t});
    // throttle with angle boost (boost limited at ANGLE_MAX)
    R33 = X[7]^2 - X[8]^2 - X[9]^2 + X[10]^2 "entry (3,3) of to_DCM(q)";
    f_cmd = (g + a_tgt[3])/max(R33, cos(angle_max));
    // AC_AttitudeControl: angle P on the quaternion error, rate feedforward from the reference
    e_att = LieGroups.SO3.Quat.log_map(
              LieGroups.SO3.Quat.product(LieGroups.SO3.Quat.inverse(X[7:10]), q_t));
    w_cmd = w_ref + {kp_ang_rp*e_att[1], kp_ang_rp*e_att[2], kp_ang_yaw*e_att[3]};
    // rate PIDs (D on the filtered error), torque = J α
    ew = w_cmd - w;
    der(iw) = ew;
    der(ewf) = wd_r*(ew - ewf);
    alpha_cmd[1:2] = kp_rate_rp*ew[1:2] + ki_rate_rp*iw[1:2] + kd_rate_rp*wd_r*(ew[1:2] - ewf[1:2]);
    alpha_cmd[3] = kp_rate_yaw*ew[3] + ki_rate_yaw*iw[3];
    tau_cmd = J*alpha_cmd;
  end ArduPilotPID;

  // ─────────────────────────── closed loops ───────────────────────────

  model ClosedLoop "Reference + replaceable controller + mixer + motors + rigid body"
    parameter Real m = 1.5;
    parameter Real g = 9.81;
    input Real f_ref "reference specific thrust"
      annotation(__Dynacert(reference(min = 8.81, max = 10.81)));
    // A bound on ᾱ alone does not bound ω̄ = ∫ᾱ, which enters the error dynamics; a certificate
    // needs an envelope on the reference state (ref.w) as well.
    input Real alpha_ref[3] "reference body angular acceleration"
      annotation(__Dynacert(reference(min = -1, max = 1)));
    input Real d_a[3] "specific-force disturbance, body frame [m/s²]"
      annotation(__Dynacert(disturbance(bound = 0.5)));
    input Real d_tau[3] "torque disturbance, body frame [N·m]"
      annotation(__Dynacert(disturbance(bound = 0.005)));
    Reference ref(g = g);
    RigidBody body(m = m, g = g);
    replaceable SE23LogLinear ctrl constrainedby FlightController;
    Mixer mixer(m = m);
    Motors motors;
    // The claim: defined from plant and reference only, so it does not depend on the controller.
    Real pos_err "‖p − p̄‖" annotation(__Dynacert(certify));
    Real vel_err "‖v − v̄‖" annotation(__Dynacert(certify));
    Real att_err "rotation angle of R̄ᵀR" annotation(__Dynacert(certify));
    Real rate_err "‖ω − ω̄‖" annotation(__Dynacert(certify));
    Real motor_dev[4] "f_i − hover thrust" annotation(__Dynacert(certify));
  equation
    ref.f = f_ref;
    ref.alpha = alpha_ref;
    ctrl.X = body.X;
    ctrl.w = body.w;
    ctrl.Xr = ref.X;
    ctrl.w_ref = ref.w;
    ctrl.f_ref = f_ref;
    ctrl.alpha_ref = alpha_ref;
    mixer.f_cmd = ctrl.f_cmd;
    mixer.tau_cmd = ctrl.tau_cmd;
    motors.fm_cmd = mixer.fm_cmd;
    body.F_b = motors.F_b + m*d_a;
    body.tau_b = motors.tau_b + d_tau;
    pos_err = sqrt((body.p - ref.p)*(body.p - ref.p));
    vel_err = sqrt((body.v - ref.v)*(body.v - ref.v));
    att_err = sqrt(sum(LieGroups.SO3.Quat.log_map(
                LieGroups.SO3.Quat.product(LieGroups.SO3.Quat.inverse(ref.q), body.q)).^2));
    rate_err = sqrt((body.w - ref.w)*(body.w - ref.w));
    motor_dev = motors.fm - fill(m*g/4, 4);
  end ClosedLoop;

  model ClosedLoopPID = ClosedLoop(redeclare ArduPilotPID ctrl)
    "Same plant, reference and claim; ArduCopter-style PID cascade";

  // ─────────────────────────── simulation ───────────────────────────

  model Maneuver "Level slalom (roll φ̄ = A cos Ωt) with a yaw sweep, a gust and a torque bias"
    parameter Real A = 0.3 "roll amplitude [rad]";
    parameter Real Om = 1.0 "slalom rate [rad/s]";
    ClosedLoop cl(
      ref(q0 = {cos(A/2), sin(A/2), 0, 0}),
      body(p0 = {0.3, -0.2, 0.1}));
  equation
    cl.f_ref = cl.g/cl.ref.R[3,3] "altitude-holding thrust";
    cl.alpha_ref = {-A*Om^2*cos(Om*time), 0, 0.06*cos(0.3*time)};
    cl.d_a = {0.3*sin(2*time), 0.2*cos(1.3*time), if time > 5 then 0.4 else 0};
    cl.d_tau = {0.003, -0.002, 0.001*sin(time)};
    annotation(experiment(StopTime = 15, Interval = 0.01));
  end Maneuver;

  model ManeuverPID = Maneuver(cl(redeclare ArduPilotPID ctrl))
    "The same maneuver flown by the PID cascade";

  // ─────────────────────────── hover certification ───────────────────────────
  // Hover reference (f̄ = g, ᾱ = 0, so the reference stays at its start); the only inputs left
  // are the disturbances. These are the models the certificate methods take. The certified
  // outputs are the closed loop's (`cl.pos_err`, …).

  model ClosedLoopHover "Log-linear SE₂(3) controller holding hover"
    input Real d_a[3] "specific-force disturbance, body frame [m/s²]"
      annotation(__Dynacert(disturbance(bound = 0.5)));
    input Real d_tau[3] "torque disturbance, body frame [N·m]"
      annotation(__Dynacert(disturbance(bound = 0.005)));
    ClosedLoop cl;
  equation
    cl.f_ref = cl.g;
    cl.alpha_ref = zeros(3);
    cl.d_a = d_a;
    cl.d_tau = d_tau;
  end ClosedLoopHover;

  model ClosedLoopPIDHover "ArduCopter-style cascade holding hover"
    input Real d_a[3] "specific-force disturbance, body frame [m/s²]"
      annotation(__Dynacert(disturbance(bound = 0.5)));
    input Real d_tau[3] "torque disturbance, body frame [N·m]"
      annotation(__Dynacert(disturbance(bound = 0.005)));
    ClosedLoop cl(redeclare ArduPilotPID ctrl);
  equation
    cl.f_ref = cl.g;
    cl.alpha_ref = zeros(3);
    cl.d_a = d_a;
    cl.d_tau = d_tau;
  end ClosedLoopPIDHover;

end QuadrotorFullStack;
