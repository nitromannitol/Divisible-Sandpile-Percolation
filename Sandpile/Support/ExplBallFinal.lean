import Sandpile.Support.ExplBallResidual
import Sandpile.Support.ExplBallGaussian
import Sandpile.Support.ExplBallBound

/-!
# Ball localization from its two analytic residuals

The frozen statement of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`) from the
two analytic residuals of its proof, with the two realization spaces bound explicitly as the
frozen statement binds them (`brownian_ball_localization_of_residuals_frozen`).

The first residual is samplewise polynomial growth of the field on the time strip, with an
amplitude chosen after the noise sample (`BallGrowthResidual`); the second is the strong Markov
step at the exit time of the ball (`BallStepResidual`). Both are properties of the field and
the motion alone, and the reduction below is the whole of the frozen conclusion.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {d : ℕ}

/-- Samplewise polynomial growth of the actual continuous Gaussian heat potential on a time
strip, with an amplitude chosen after the noise sample. -/
def BallGrowthResidual (d : ℕ) : Prop :=
  ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ), IsWhiteNoise d W PW →
  ∀ ν2 : ℝ, 0 ≤ ν2 →
  ∀ (Z : ℝ → Space d → ΩW → ℝ),
    (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω) →
    (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) →
  ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
    ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d, ‖Z v y ω‖ ≤ C * (1 + ‖y‖) ^ p

/-- The strong Markov step of `lem:brownian-ball-localization` at the exit time of the ball,
for the actual continuous Gaussian heat potential. -/
def BallStepResidual (d : ℕ) : Prop :=
  ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ), IsWhiteNoise d W PW →
  ∀ ν2 : ℝ, 0 ≤ ν2 →
  ∀ (Z : ℝ → Space d → ΩW → ℝ),
    (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω) →
    (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) →
  ∀ T : ℝ, 0 < T → ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Space d), IsCompact K →
  ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Space d → ℝ≥0 → ΩB → Space d),
    (∀ y : Space d, IsBrownian d y (B y) PB) →
    (∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω) →
    (∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
  ∀ᵐ ω ∂PW, ∀ u ∈ K,
    BallExcessStep (B u) PB (fun t z => Z t z ω) T A u
      (sSup (farValues B PB (fun t z => Z t z ω) T A K))

/-- The frozen statement of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`) from
the two analytic residuals of its proof. -/
theorem brownian_ball_localization_of_residuals_frozen (d : ℕ) (_hd : d < 4)
    (hgrowth : BallGrowthResidual d) (hstep : BallStepResidual d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 0 < T →
      ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Space d), IsCompact K →
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Space d → ℝ) → ΩW → ℝ), IsWhiteNoise d W PW →
      ∀ ν2 : ℝ, 0 ≤ ν2 →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Space d → ℝ≥0 → ΩB → Space d),
        (∀ y : Space d, IsBrownian d y (B y) PB) →
        (∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω) →
        (∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
      ∀ (Z : ℝ → Space d → ΩW → ℝ),
        (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω) →
        (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
          ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) →
      ∀ᵐ ω ∂PW, ∀ u ∈ K,
        brownianValue (B u) PB (fun t z => Z t z ω) T u -
            brownianValueBall (B u) PB (fun t z => Z t z ω) T A u ≤
          C * Real.exp (-(c * A ^ 2 / T)) *
            sSup {v : ℝ | ∃ z : Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) ∧
              v = brownianValue (B z) PB (fun t x => Z t x ω) T z} := by
  obtain ⟨C, c, hC, hc, hmain⟩ := ball_localization_of_input d
  refine ⟨C, c, hC, hc, ?_⟩
  intro T hT A hA K hK ΩW mΩW PW hPW W hW ν2 hν2 ΩB mΩB PB hPB B hBrown hcont hmeas Z hmod hcontZ
  have hg := hgrowth ΩW PW W hW ν2 hν2 Z hmod hcontZ T hT
  have hs := hstep ΩW PW W hW ν2 hν2 Z hmod hcontZ T hT A hA K hK ΩB PB B hBrown hcont hmeas
  have hfar := bddAbove_farValues_of_samplewise_growth_uniform hBrown hcont
    (fun y t => (hmeas y t).measurable) Z T A hT.le K hK hg (hcontZ T hT)
  have hinput := ballInput_of_samplewise_growth hBrown hcont
    (fun y t => (hmeas y t).measurable) Z T A hT.le K hK hg (hcontZ T hT) hfar hs
  filter_upwards [hinput] with ω hω
  intro u hu
  exact hmain T hT A hA K ΩB PB B hBrown hcont (fun t z => Z t z ω) u hu (hω u hu)

end Sandpile.Continuum
