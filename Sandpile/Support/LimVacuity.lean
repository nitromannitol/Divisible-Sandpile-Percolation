import Sandpile.Support.LimApproxAssembly
import Sandpile.Support.MainExplBrownianCont

/-!
# Vacuity and junk-value checks for the crossing chain

Every statement of the crossing chain is an inequality or an identity about integrals of
kernels and about stopped Brownian motions, and each of those carries a junk value that
could satisfy it for the wrong reason: a Bochner integral is zero when its integrand is
not integrable, `ENNReal.toReal ⊤` is zero, and a supremum over an empty set is zero. The
theorems below rule those degenerate readings out: the exit time is genuinely finite with
positive probability, the relevant kernels have positive mass, and the hypotheses of the
chain are simultaneously satisfiable by an actual model.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal

namespace Sandpile.Support

/-! ### The cited occupation-density input is not satisfied for a vacuous reason

If the exit time were infinite almost surely the accumulated reward would be the junk
value `0`, and the external's identity would read `0 = 2d ∫ ballKernel`.  The mass of the
kernel is positive, so the external entails that the motion leaves the ball with positive
probability: the identity is an assertion about a genuine random variable. -/
/-- If the ball-occupation-density external held while the exit time from the unit ball
were almost surely infinite, its identity would read the vacuous `0 = 2d ∫ ballKernel`;
since the ball kernel has positive mass, the external instead forces the exit time to be
finite with positive probability. -/
theorem occupation_external_forces_finite_exit
    (hOcc : Sandpile.External.BallOccupationDensity) {d : ℕ} (hd : d = 2 ∨ d = 3)
    (u : Space 2) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Space d) (hB : IsBrownian d (planePoint u) B P)
    (hc : ∀ ω, Continuous fun t => B t ω) (hm : ∀ t, StronglyMeasurable (B t)) :
    0 < ∫ ω, (LatticeProb.exitTime B (planePoint u) 1 ω).toReal ∂P := by
  have hmass : 0 < ∫ y : Space d, ballKernel d 1 u y := by
    rw [integral_ballKernel_eq_centred d u]
    exact centredKernel_mass_pos hd
  have hd1 : 1 ≤ d := by rcases hd with h | h <;> omega
  have hd0 : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    linarith
  have h := (integrable_ball_exitTime_of_occupation hOcc hd one_pos u P B hB hc hm).2
  rw [h]
  positivity

/-! ### The kernel of the ball-stopped field is a genuine occupation density

Its mass is the expected truncated exit time, so it is positive as soon as that is: the
identification of the ball-stopped field with a white-noise average is not the trivial
`W 0 = 0`. -/
/-- The mass of `ballStoppedKernel` equals the expectation of the stop time
`ballStopTime`, so it is positive as soon as the stop time has positive expectation, which
shows the identification with a white-noise average is not the trivial `W 0 = 0`. -/
theorem stopped_kernel_mass_pos {ΩB : Type} [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hB : ∀ y, IsBrownian d y (B y) PB) (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) {s T : ℝ} (hT : 0 < T) (u : Space 2)
    (hpos : 0 < ∫ b, ((ballStopTime d B s T u b : ℝ)) ∂PB) :
    0 < ∫ y, ballStoppedKernel d PB B s T u y := by
  rw [integral_ballStoppedKernel hd PB hB hBc hBm hT u]
  exact hpos

/-! ### The ball field is not degenerate

The modulus and rate estimates of the chain bound the `L²` norms of differences of the
ball kernel and its stopped approximations.  Those statements would be empty if the ball
kernel were almost everywhere zero; it is not, since its mass is positive. -/
/-- `ballKernel d 1 u` is not almost everywhere `0` with respect to Lebesgue measure,
since its integral equals the positive mass of the centred kernel. -/
theorem ballKernel_not_ae_zero {d : ℕ} (hd : d = 2 ∨ d = 3) (u : Space 2) :
    ¬ (ballKernel d 1 u =ᵐ[(volume : Measure (Space d))] 0) := by
  intro hzero
  have hmass : 0 < ∫ y : Space d, ballKernel d 1 u y := by
    rw [integral_ballKernel_eq_centred d u]
    exact centredKernel_mass_pos hd
  have hzeroint : (∫ y : Space d, ballKernel d 1 u y) = 0 := by
    refine integral_eq_zero_of_ae ?_
    exact hzero
  rw [hzeroint] at hmass
  exact lt_irrefl 0 hmass

/-! ### A model satisfying every hypothesis exists

The theorems of the chain carry `IsBrownian`, continuity of every path and strong
measurability of every time slice at once; those are satisfiable simultaneously, so none
of the statements holds for want of a model. -/
/-- There is a probability space carrying, for every starting point `x`, a Brownian motion
`B x` from `x` whose paths are continuous and whose time slices are strongly measurable,
so the joint hypotheses of the chain are simultaneously satisfiable. -/
theorem motion_exists (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (B : Space d → ℝ≥0 → Ω → Space d), (∀ x, IsBrownian d x (B x) P) ∧
        (∀ y ω, Continuous fun t => B y t ω) ∧ (∀ y t, StronglyMeasurable (B y t)) :=
  Sandpile.Continuum.exists_isBrownian_cont d

/-! ### The measurable continuous version is not an empty construction

Its hypotheses are satisfiable by a field that is not almost surely zero: a measurable
field, continuous in the parameter, is its own version. -/
/-- For any measurable `g`, taking `Y u ω = g ω` constantly in `u` produces a version of
`g` that is measurable in `ω` for each `u`, continuous in `u` for each `ω`, and agrees
with `g` almost everywhere, so the hypotheses of the continuous-version construction are
satisfiable and not vacuous. -/
theorem version_hypotheses_satisfiable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {E : Type*} [MetricSpace E] [TopologicalSpace.SeparableSpace E] (g : Ω → ℝ)
    (hg : Measurable g) :
    ∃ Y : E → Ω → ℝ, (∀ u, Measurable (Y u)) ∧ (∀ ω, Continuous fun u => Y u ω) ∧
      ∀ᵐ ω ∂P, ∀ u, Y u ω = g ω := by
  refine exists_measurable_continuous_version (P := P) (fun _ ω => g ω) (fun _ ω => g ω)
    (fun _ => hg) (fun _ => Filter.EventuallyEq.rfl) ?_
  exact Filter.Eventually.of_forall fun ω => continuous_const

end Sandpile.Support
