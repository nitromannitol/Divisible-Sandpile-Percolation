/-
The two assemblies of the crossing chain with the law of the finite-scale maximum
discharged.

`Sandpile.Support.MaxBallFieldLaw` was assumed while the determination of a
centred Gaussian law by its covariance was available only on ONE probability
space.  It is now proved (`Sandpile.Support.maxBallFieldLaw`), so the two
assemblies of `lem:finite-scale-extraction` and `thm:limiting-odometer-crossing`
rest on strictly fewer inputs: the zero-one upgrade of Step 1
(`ScaleCrossingAS`), the two facts of `sandpile.tex:2499-2511`
(`LocalizedValueApproximation`), and the propositions the paper itself cites.

The statements are those of `Sandpile.Support.finite_scale_extraction_of_inputs`
and `Sandpile.Support.limiting_odometer_crossing_of_inputs` with the hypothesis
`hLaw` removed; nothing else changes.
-/
import Sandpile.Support.LimCrossing
import Sandpile.Support.LimJoint

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- `lem:finite-scale-extraction` from `prop:fixed-scale-crossings` and Step 1 alone: the
law of the finite-scale maximum is no longer an input. -/
theorem finite_scale_extraction_of_scale_crossing
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {d : ℕ} (hd : d = 2 ∨ d = 3) (hZ : ScaleCrossingAS d)
    {N : ℕ} (a b : Fin N → Fin 2 → ℝ) (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i)
    (dir : Fin N → Fin 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℝ) (k : ℕ) (s : Fin k → ℚ), 0 < c ∧ 0 < k ∧
      (∀ i : Fin k, 0 < s i ∧ s i < 1) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W P →
        (∀ t : ℝ, 0 < t → t ≤ 1 → ∀ᵐ ω ∂P, Continuous fun u => ballField d W t u ω) →
      ENNReal.ofReal (1 - ε) ≤ P {ω | ∀ j : Fin N,
        Crosses (a j) (b j) (dir j)
          {u | 4 * c ≤ ⨆ i : Fin k, ballField d W (s i : ℝ) u ω}} :=
  finite_scale_extraction_of_inputs hRSWc hPitt hGauss hd hZ (maxBallFieldLaw hd) a b hab dir ε hε

/-- `thm:limiting-odometer-crossing` from Step 1 and the value approximation alone. -/
theorem limiting_odometer_crossing_of_scale_crossing
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {d : ℕ} (hd : d = 2 ∨ d = 3) (hZ : ScaleCrossingAS d)
    (hApp : LocalizedValueApproximation d)
    {N : ℕ} (a b : Fin N → Fin 2 → ℝ)
    (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i) (dir : Fin N → Fin 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T H : ℝ, 0 < T ∧ 0 < H ∧
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W PW →
        (∀ t : ℝ, 0 < t → t ≤ 1 → ∀ᵐ ω ∂PW, Continuous fun u => ballField d W t u ω) →
      ∀ (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ),
        (∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
          Z t x =ᵐ[PW] fun ω => Sandpile.Continuum.gaussianPotential d 1 W t x ω) →
        ContinuousHeatPotential d Z PW →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
        (∀ y, Sandpile.Continuum.IsBrownian d y (B y) PB) →
        (∀ y ω, Continuous fun t => B y t ω) →
        (∀ y t, StronglyMeasurable (B y t)) →
      ENNReal.ofReal (1 - ε) ≤ PW {ω | ∀ j : Fin N,
        Crosses (a j) (b j) (dir j) {u | H < localizedValue d Z PB B T u ω}} :=
  limiting_odometer_crossing_of_inputs hRSWc hPitt hGauss hd hZ (maxBallFieldLaw hd) hApp
    a b hab dir ε hε

end Sandpile.Support
