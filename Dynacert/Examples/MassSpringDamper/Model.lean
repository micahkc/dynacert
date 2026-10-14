import Dynacert.Linear.LTI

/-!
# Mass-spring-damper under PD control (error dynamics)

Hand-written stand-in for rumoca's Lean export of
`cp_reach/examples/general/models/closed_loop.mo` (`m = 1`, `c = 0.2`, `k = 1`, `kp = 10`,
`kd = 2`), reduced to tracking-error coordinates `x = (e, ev)` with disturbance force `w = d`.

`system` is the trusted part: it transcribes the Modelica equations. `model` is a linear
form for the certificate machinery, and `model_toSystem` proves the two agree, so the matrix
extraction itself does not need to be trusted.
-/

namespace Dynacert.Examples.MassSpringDamper.Model

open Matrix Dynacert Dynacert.Linear

/-- Physical parameters, exactly as written in the Modelica source. -/
def m : ℚ := 1
def c : ℚ := 1/5
def k : ℚ := 1
def kp : ℚ := 10
def kd : ℚ := 2

/-- `der(e) = ev`, `der(ev) = (d - c*ev - k*e - kp*e - kd*ev) / m`. -/
noncomputable def system : System 2 1 where
  f x w := ![x 1, ((w 0 : ℝ) - c * x 1 - k * x 0 - kp * x 0 - kd * x 1) / m]

/-- Linear form `ẋ = A x + B w` (extracted by tooling; checked by `model_toSystem`). -/
def model : LTIModel 2 1 where
  A := !![0, 1; -11, -11/5]
  B := !![0; 1]

theorem model_toSystem : model.toSystem = system := by
  simp only [LTIModel.toSystem, system, model, m, c, k, kp, kd]
  congr 1
  funext x w i
  fin_cases i
  · simp [toReal, mulVec, dotProduct]
  · simp [toReal, mulVec, dotProduct]
    ring

end Dynacert.Examples.MassSpringDamper.Model
