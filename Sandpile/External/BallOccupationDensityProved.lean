import Sandpile.External.BallOccupationDensity
import Sandpile.External.PittGaussianFKGProved
import Sandpile.Frozen.LimitingOdometerCrossing
import Sandpile.Frozen.D23CriticalLevelPercolation
import LatticeProb.Prob.BrownianBallOccupation

/-!
# The occupation density of a ball, proved

This module discharges the external input `Sandpile.External.BallOccupationDensity`, the Green
function of a Euclidean ball for the paper's Brownian motion in occupation-density form, instead
of assuming it.

The shared library proves `LatticeProb.IsBrownianSpace.ballOccupation`: for Brownian motion with
generator `Δ/(2d)` in dimension two or three, started at `x`, with continuous and strongly
measurable paths, and killed on leaving the ball of radius `s` about `x`, the accumulated reward
of a bounded measurable `φ` up to the exit time is integrable and has mean
`2d ∫ φ(z) G(x, z) dz`, where `G = LatticeProb.ballGreen d s` is the Green kernel of the ball.
The repository's `Sandpile.Continuum.IsBrownian` has the same three fields as the library's
`LatticeProb.IsBrownianSpace`, and `ballKernel d s u` is by definition
`LatticeProb.ballGreen d s (planePoint u)`, so the statement is the library theorem at the centre
`planePoint u`.

The `Prop` and its name are left untouched, so no frozen statement changes.
`Sandpile.limiting_odometer_crossing` and `Sandpile.d23_critical_level_percolation` are
`thm:limiting-odometer-crossing` and `thm:d23-critical-level-percolation` without the hypotheses
`Sandpile.External.BallOccupationDensity` and `Sandpile.External.PittGaussianFKG`, both proved
in this repository.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

-- FROZEN-STATEMENT-BEGIN
/-- The Green function of a Euclidean ball, in the occupation-density form the proof of
`thm:limiting-odometer-crossing` consumes, proved rather than assumed. -/
theorem Sandpile.External.ballOccupationDensity_holds : Sandpile.External.BallOccupationDensity
-- FROZEN-STATEMENT-END
:= by
  intro d hd s hs u Ω _ P _ B hB hcont hm φ hφ hb
  exact LatticeProb.IsBrownianSpace.ballOccupation P hd (planePoint u) B
    ⟨hB.start, hB.coord, hB.indep⟩ hm hcont s hs φ hφ hb

/-- `thm:limiting-odometer-crossing` without the hypotheses
`Sandpile.External.PittGaussianFKG` and `Sandpile.External.BallOccupationDensity`, which
`Sandpile.External.pittGaussianFKG` and `Sandpile.External.ballOccupationDensity_holds` prove. -/
theorem Sandpile.limiting_odometer_crossing
    (hRSWc : Sandpile.External.ContinuumRSW)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (N : ℕ) (a b : Fin N → Fin 2 → ℝ)
    (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i) (dir : Fin N → Fin 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T H : ℝ, 0 < T ∧ 0 < H ∧
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W PW →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂PW,
          Continuous (fun u : Sandpile.Continuum.Space 2 =>
            Sandpile.Frozen.FixedScaleCrossings.ballField d W s u ω)) →
      ∀ (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ),
        (∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
          Z t x =ᵐ[PW] fun ω => Sandpile.Continuum.gaussianPotential d 1 W t x ω) →
        (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
          ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
            (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)))) →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
        (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB) →
        (∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun t => B y t ω) →
        (∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
      ENNReal.ofReal (1 - ε) ≤ PW {ω | ∀ j : Fin N,
        Sandpile.Frozen.LimitingOdometerCrossing.Crosses (a j) (b j) (dir j)
          {u : Sandpile.Continuum.Space 2 | H <
            Sandpile.Continuum.brownianValueBall
              (B (Sandpile.Frozen.LimitingOdometerCrossing.planePoint u)) PB
              (fun t z => Z t z ω) T 1
              (Sandpile.Frozen.LimitingOdometerCrossing.planePoint u)}} :=
  Sandpile.Frozen.limiting_odometer_crossing hRSWc Sandpile.External.pittGaussianFKG
    Sandpile.External.ballOccupationDensity_holds d hd N a b hab dir ε hε

/-- `thm:d23-critical-level-percolation` without the hypotheses
`Sandpile.External.PittGaussianFKG` and `Sandpile.External.BallOccupationDensity`, which
`Sandpile.External.pittGaussianFKG` and `Sandpile.External.ballOccupationDensity_holds` prove. -/
theorem Sandpile.d23_critical_level_percolation
    (hLSS : Sandpile.External.LSSDomination)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hCube : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
          LatticeProb.HasInfiniteComponent
            {z : Sandpile.Site 2 | c * (t : ℝ) ^ ((4 - (d : ℝ)) / 4) <
              Sandpile.odometer σ t (Sandpile.planeSite z)} :=
  Sandpile.Frozen.d23_critical_level_percolation hLSS hRSWc Sandpile.External.pittGaussianFKG
    Sandpile.External.ballOccupationDensity_holds hCube d hd ν₀ θ₀ K₀ hν₀ hθ₀
