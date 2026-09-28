import Sandpile.Continuum.Stopping
import Sandpile.Support.ContinuumPlanar
import LatticeProb.Prob.BrownianExitTime

/-!
# The ball Green function in occupation-density form

The Green function of a Euclidean ball for Brownian motion, in the
occupation-density form `thm:limiting-odometer-crossing`'s proof consumes
(`sandpile.tex:2074-2088` defines `𝒳_s` by the closed-form kernel;
`sandpile.tex:2499-2503` recalls it as "`(2d)⁻¹` times the white-noise average
against the expected occupation density" of the ball-stopped motion).  Cited
classical potential theory: Peter Mörters and Yuval Peres, *Brownian Motion*
(Cambridge University Press, 2010), Chapter 3, the Green's function of a ball.
The theorem number is left unstated: the citation has not been checked against
the printed text.

Statement.  For the paper's motion (generator `Δ/(2d)`) started at `u`, killed
on exiting the Euclidean ball `B(u,s)`, the EXPECTED occupation measure before
exit (a deterministic measure, since it is already an expectation over the
motion) has a density against Lebesgue measure, and that density at `z` is
`2d · ballKernel d s u z`.  This is stated in the tested (weak) form the proof
needs: for every bounded measurable `φ`, the expected accumulated reward
`∫_0^{τ} φ(B_r) dr` (a random variable, `τ` the exit time) is integrable and
its mean is `2d ∫ φ(z) ballKernel d s u z dz`.  Nothing about the white noise,
the field `Z`, or the limit `T → ∞` is in this statement; those stay in-repo.

Normalization.  For the STANDARD motion (generator `Δ/2`, one real Brownian
coordinate per dimension with no rescaling) the Green function of `B(0,s)` at
its centre is the classical `(1/π) log(s/|z|)` in `d = 2` and
`(1/(2π))(1/|z| − 1/s)` in `d = 3`.  The paper's motion runs `d` times
SLOWER (generator `Δ/(2d)` against `Δ/2`, `sandpile.tex:1069-1071`), which
multiplies every occupation time — hence every occupation density — by `d`:
occupying `[0,dt]` for the slow motion matches occupying `[0,t]` for the
standard one, after the time change `t ↦ dt`, and the ball radius, an
invariant of the PATH alone, is unaffected by that reparametrization.  So the
slow motion's occupation density at the centre is `d · (1/π) log(s/|z|) = 2d ·
(1/(2π)) log(s/|z|)` in `d = 2` and `d · (1/(2π))(1/|z| − 1/s) = 2d ·
(1/(4π))(1/|z| − 1/s)` in `d = 3`, which is exactly `2d · ballKernel d s 0 z`
with the paper's own kernels `(1/(2π)) log(s/|z|)` and
`(1/(4π))(1/|z| − 1/s)` (`Sandpile/Support/ContinuumPlanar.lean`).

Vacuity check.  At `d = 2` and `d = 3`, `u = 0`,
`s = 1`: `ballKernel d 1 0 z` is a genuine, positive, locally integrable
function of `z` (the log or inverse-distance singularity at `z = 0` is
integrable against Lebesgue measure in dimension two and three), not
identically zero and not forced to any junk value; a motion satisfying every
hypothesis exists by `Sandpile.Continuum.exists_isBrownian_cont`, whose exit
time from `B(0,1)` is almost surely finite (proved in this repository,
`Sandpile.Support.ballBlockEvent_measure_le`), so the accumulated reward is a
genuine, a.s. finite random variable for every bounded `φ` and the identity is
a real assertion, not one satisfied for a vacuous reason.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

-- FROZEN-STATEMENT-BEGIN
/-- The Green function of a Euclidean ball, in the occupation-density form the
proof of `thm:limiting-odometer-crossing` consumes: see the module docstring. -/
def Sandpile.External.BallOccupationDensity : Prop :=
  ∀ (d : ℕ), d = 2 ∨ d = 3 → ∀ (s : ℝ), 0 < s →
  ∀ (u : Space 2)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Space d),
    IsBrownian d (planePoint (d := d) u) B P →
    (∀ ω, Continuous fun t => B t ω) → (∀ t, StronglyMeasurable (B t)) →
  ∀ φ : Space d → ℝ, Measurable φ → (∃ M, ∀ z, |φ z| ≤ M) →
    Integrable (fun ω =>
      ∫ r in (0:ℝ)..(LatticeProb.exitTime B (planePoint (d := d) u) s ω).toReal,
        φ (B r.toNNReal ω)) P ∧
    (∫ ω, (∫ r in (0:ℝ)..(LatticeProb.exitTime B (planePoint (d := d) u) s ω).toReal,
        φ (B r.toNNReal ω)) ∂P)
      = 2 * (d : ℝ) * ∫ z, φ z * ballKernel d s u z
-- FROZEN-STATEMENT-END
