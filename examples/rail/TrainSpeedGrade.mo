// Automatic train operation (ATO): position/speed tracking of a timetable profile on grades.
//
//   M*v' = F - b1*v + F_grade,   x' = v
// b1*v is the speed-proportional part of the running resistance (linearized Davis term; the
// constant part is assumed compensated in the traction command). F_grade = -M*g*sin(grade)
// is the unknown grade (and residual resistance) force, bounded by a 2 % grade.
// The timetable gives a smooth reference x_ref' = v_ref, v_ref' = a_ref with a_ref free
// (any accelerate/cruise/brake profile). The ATO computes the feedforward traction
//   F_ff = M*a_ref + b1*v_ref
// and adds PID feedback on position error (integral state xi' = e_x).
// Units: tonnes, kN, metres.
//
// Certified: position error (stopping accuracy), speed error and the integrator stay bounded
// along every timetable profile and every grade up to 2 %.
// Values are illustrative for a ~400 t multiple-unit train.
model TrainSpeedGrade
  parameter Real M = 400.0 "Train mass incl. rotating-mass allowance [t]";
  parameter Real b1 = 6.0 "Speed-proportional resistance [kN*s/m]";
  parameter Real kp = 80.0 "Position gain [kN/m]";
  parameter Real kd = 400.0 "Speed gain [kN*s/m]";
  parameter Real ki = 8.0 "Integral gain [kN/(m*s)]";

  input Real x_ref "Reference position [m]"
    annotation(__Dynacert(reference(derivative = "v_ref", start = 0)));
  input Real v_ref "Reference speed [m/s]"
    annotation(__Dynacert(reference(derivative = "a_ref", start = 0)));
  input Real a_ref "Reference acceleration [m/s2]" annotation(__Dynacert(reference));
  input Real F_grade "Grade force [kN] (|F| <= M*g*0.02)"
    annotation(__Dynacert(disturbance(bound = 78.5)));

  Real x(start = 0, fixed = true) "Train position [m]";
  Real v(start = 0, fixed = true) "Train speed [m/s]";
  Real xi(start = 0, fixed = true) "Integral of position error [m*s]"
    annotation(__Dynacert(certify));
  Real e_x "Position error [m]" annotation(__Dynacert(certify));
  Real e_v "Speed error [m/s]" annotation(__Dynacert(certify));
  Real F_ff "Feedforward traction [kN]";
  Real F "Traction/braking force [kN]";
equation
  e_x = x - x_ref;
  e_v = v - v_ref;
  F_ff = M*a_ref + b1*v_ref;
  F = F_ff - kp*e_x - kd*e_v - ki*xi;
  der(xi) = e_x;
  der(x) = v;
  M*der(v) = F - b1*v + F_grade;
end TrainSpeedGrade;
