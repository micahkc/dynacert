# Slide-by-slide guide

**Audience assumed:** engineers and technical managers who know control systems or safety
engineering but not formal proof tools. Tell the author if the audience is different.

**One-sentence pitch:** dynacert turns an annotated engineering model into a mathematical proof,
checked by computer, that the system stays within stated limits.

---

## Slide 1: Simulation can only show the cases you tried

**Image:** none (title or text slide)

**On slide**
- Testing and simulation sample some scenarios; a limit can still be crossed by one you missed
- dynacert proves a limit for *every* scenario in a stated range
- The proof is checked by a computer, not taken on trust

**Notes:** Set up the gap: a thousand clean simulations are evidence, not a guarantee. dynacert
produces a theorem that covers every disturbance within the stated bound, for all time.

---

## Slide 2: From a model to a machine-checked theorem

**Image:** `01-pipeline.png`

**On slide:** (image only, or one line) *You write the model. The computer finds the proof and
independently checks it.*

**Notes:** Walk left to right. The engineer writes a model in Modelica, a standard modeling language,
and marks what to certify. The rumoca compiler produces two views of the same equations. Python
searches numerically for a certificate. The Lean proof checker re-verifies every number in exact
arithmetic. The result is a theorem or nothing, never a weaker claim.

---

## Slide 3: The search doesn't have to be trusted

**Image:** `02-trust-boundary.png`

**On slide:** (image only)

**Notes:** This is the key design idea. Solvers and floating point make mistakes, but here a mistake
only makes the check fail. Be open about the left column: the proof is about rumoca's translation of
the model, so that translation is trusted, and a person still has to read the short claim.

---

## Slide 4: Engineers state the claim in the model

**Image:** `03-annotations-to-claim.png`

**On slide:** (image only)

**Notes:** Each annotation becomes a "for every" in the theorem, and `certify` is the conclusion. The
claim comes from these annotations only. No search result can change what is being claimed.

---

## Slide 5: What a result looks like

**Image:** `10-certificate-ellipse-ClosedLoop.png`

**On slide**
- `CERTIFIED  ClosedLoop.Cert.certified`
- Position error ≤ 0.8438, simulated peak 0.7337
- Velocity error ≤ 1.431, simulated peak 1.229

**Notes:** Left panel: the proved set (blue ellipse) with simulated trajectories inside it. Other
panels: signals over time against the proved bound (dashed). Example: a mass on a spring, tracking
a path under a disturbance force of up to 1 N.

---

## Slide 6: Eight proof methods, chosen automatically

**Image:** `05-method-support-matrix.png`

**On slide:** (image only, or) *Running `certify` tries every method that applies and keeps the
tightest bound for each output.*

**Notes:** Linear models have the fullest support. Nonlinear methods are newer and narrower. Be
upfront about the "no" cells. "Limited" for `funnel` means a built-in polynomial path, and for `lie`
a coasting circular-orbit reference. "Bug" is a known defect being reported.

---

## Slide 7: 73 certificates across 65 models

**Image:** `06-certificates-by-method.png`

**On slide**
- Automotive, aerospace, marine, rail, energy, process, buildings, water, robotics, biomedical,
  precision machines, agriculture
- Every theorem is limited to Lean's three standard axioms

**Notes:** Count as of 2026-11-02. Parameter values in the examples are illustrative, not from real
products, and the biomedical models are not clinical. Say this out loud.

---

## Slide 8: Tighter methods get close to the exact answer

**Image:** `07-polyhedral-vs-lmi.png`

**On slide:** *Polyhedral bounds: 1.0002 and 3.0005, against exact values of 1 and 3*

**Notes:** Two reservoirs in series. The ellipsoid method overestimates by 47% on the upper level and
7% on the lower. The polytope method is within 0.02%. This model favors polytopes because its modes
are real and well separated. On other models with more states, the ellipsoid is often tighter, which
is why the tool runs both.

---

## Slide 9: Nonlinear systems, with no new proof per model

**Image:** `15-montecarlo-envelope-PathFollow.png` (a quadrotor photo or sketch also works; none is included)

**On slide**
- Planar quadrotor with thrust-vector control: position error ≤ 0.160 m, pitch ≤ 0.146 rad
- Tighter than the published grid-based result (0.178 m, 0.164 rad)
- Lean checks the nonlinear bounds too: `sin`, `cos`, `√`, `atan2`
- Full 3D quadrotor at hover (`compose`): position error ≤ 0.055 m horizontally, 0.040 m vertically
- New examples: lunar hopper, path following, coupled pendula

**Notes:** Each nonlinear function has a lemma proved once. A new model reuses those lemmas, with only
data and wiring generated. This works near an equilibrium and for moderate disturbances. The
planar quadrotor certificate holds at 25% of the paper's full disturbance level and fails above about 26%. The 3D model is
at 10% of that full level. Its certificate is brand new (2026-11-02), so confirm it with the author.

---

## Slide 10: Large maneuvers, on a finite time window

**Image:** `16-funnel-RobotArm.png`

**On slide:** *A robot arm on a large swing: proved error bound grows from 0.010 to 0.025 rad; simulated peak 0.0056 rad*

**Notes:** Near-equilibrium methods don't apply on a large swing, so this method proves a bound for
each short time segment along the path. Blue: the proved bound per segment over 2 seconds. Gray:
40 of the 200 simulated runs. This bound is conservative, at about four times the simulated peak.

---

## Slide 11: Proved tubes follow any trajectory

**Image:** `11-tube-QuadcopterAltitude.png`

**On slide:** *The same error set is carried along every admissible reference path*

**Notes:** Shaded band: the proved tube. Gray: simulated runs. Colored: the worst cases found. All
stay inside. The reference is arbitrary within its stated derivative relations, so the guarantee
needs no re-proof for a new path.

---

## Slide 12: Evidence checks the proof, but never replaces it

**Image:** `12-montecarlo-envelope-Reservoir.png` (or `13-montecarlo-exceedance-Reservoir.png` for a
statistical audience)

**On slide**
- Monte Carlo: random admissible scenarios, compared with the bound
- Falsification: a directed search for the worst case
- These are labeled as evidence; only Lean produces a certificate

**Notes:** Two uses: catching a mismatch between model views, and showing how much slack a bound has.
The dashed lines in this figure are the ellipsoid bound, which is looser than the
polyhedral bound on slide 8. This is a known limitation of the current tool output.

---

## Slide 13: How much slack is in the bounds?

**Image:** `08-tightness.png`

**On slide:** *On 6 of 11 models, search reaches at least 90% of a proved bound; none exceeds it*

**Notes:** Each dot is one certified output. 1.0 means search reached the proved bound, so the bound
can't be much improved. A low dot means a loose bound or a search that missed the true worst case,
and the chart can't tell which. Left out: models with an initial box, because the search doesn't start
from the box, and four models where the search failed or timed out.

---

## Slide 14: When it can't prove something, it says why

**Image:** `09-honest-refusals.png`

**On slide:** *No certificate means nothing is claimed, and the tool names the gap*

**Notes:** These are real messages. Sound but not complete: failing to find a proof does not mean the
system is unsafe. The first case really is unstable; the others are features not yet supported.

---

## Slide 15: Where it stands today

**Image:** `04-six-layers.png` (optional)

**On slide**
- **Works:** linear, uncertain, switched, and layered models; nonlinear near equilibrium; finite-time
  funnels; one spacecraft class
- **Not yet:** discrete events, Euclidean-ball disturbances, general SE₂(3) controllers
- **Known gaps:** new examples exposed defects in the nonlinear tooling; these stop a proof, and can't produce a wrong one

**Notes:** Guarantees cover classical solutions; sliding motions at a switching surface are outside
the claim. A certificate covers the model, not the hardware: it is only as good as the model.

---

## Wording to keep accurate

| Say | Avoid |
|---|---|
| "proves the model stays within these bounds" | "proves the system is safe" |
| "for every disturbance within the stated bound" | "for all conditions" |
| "machine-checked" | "bug-free" or "guaranteed in the real world" |
| "Monte Carlo evidence" | "Monte Carlo certified" |

## Glossary (for speaker notes)

- **Modelica:** a standard language for writing engineering models as equations.
- **rumoca:** the compiler that translates Modelica for dynacert.
- **Lean / kernel:** a proof checker; the kernel is the small core that verifies each step.
- **Certificate:** numbers that make a proof checkable, such as the shape of a set the system can't leave.
- **Ellipsoid, polytope:** the shape of that set (`lmi` uses an ellipsoid, `polyhedral` a many-sided shape).
- **Monte Carlo:** random simulation. **Falsification:** a directed search for a violation.
- **Tube:** the proved region around a reference path. **Funnel:** a region proved over a finite time.
