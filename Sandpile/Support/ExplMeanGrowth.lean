import Sandpile.Support.ContMeanGrowth
import Sandpile.Support.MeanAValue
import Sandpile.Continuum.WhiteNoiseExists
import Sandpile.Continuum.BrownianExists

/-!
# Theorem 1.3(i)(a): the mean growth rate from the mean asymptotic

Theorem 1.3(i)(a) of `sandpile.tex` (`sandpile.tex:206-217`) from `cor:dlt4-mean-asymptotic`
(`sandpile.tex:2034-2052`), which the proof of `thm:main-explosion` names at `sandpile.tex:299`:
"Part (i)(a) is Corollary~\ref{cor:dlt4-mean-asymptotic}".

The corollary ends with `E u_t(0) ∼ E𝒰(1,0) t^{(4-d)/4}`, and `prop:continuum-value-selfsimilar`
(`sandpile.tex:1961-1980`) supplies `0 < E𝒰(1,0)^p < ∞` for every `p > 0`, hence at `p = 1` the
positivity of the constant. Part (i)(a) asks for a limit of `t^{-(4-d)/4} E u_t(0)` in `(0,∞)`,
which is exactly those two facts with `L = E𝒰(1,0)`: `Sandpile.Support.exists_growth_limit_of_ratio`
is that step.

Both inputs are stated for an arbitrary space carrying white noise and an arbitrary space carrying
the family of Brownian motions, so the assembly instantiates them at the spaces built by
`Sandpile.Continuum.exists_isWhiteNoise` and `Sandpile.Continuum.exists_isBrownian`. The constant
`L` is then `∫ 𝒰(1,0) dP_W` on those spaces.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

/-- **Theorem 1.3(i)(a) from the mean asymptotic and the positivity of the
limiting mean.**  The hypothesis is the ninth clause of
`cor:dlt4-mean-asymptotic` together with the positivity of the limiting mean,
both read at a continuous version `Z` of the Gaussian heat potential on an
arbitrary pair of realization spaces. -/
theorem mean_growth_le_three_of
    (d : ℕ) (ν : Measure ℝ)
    (h : ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W PW →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
        (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB) →
      ∃ Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ,
        0 < (∫ ω, Sandpile.Continuum.continuumValue d Z B PB 1 0 ω ∂PW) ∧
        Tendsto (fun t : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t /
            ((∫ ω, Sandpile.Continuum.continuumValue d Z B PB 1 0 ω ∂PW) *
              (t : ℝ) ^ ((4 - (d : ℝ)) / 4)))
          atTop (𝓝 1)) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 L) := by
  obtain ⟨ΩW, mW, PW, hPW, W, hW⟩ := Sandpile.Continuum.exists_isWhiteNoise d
  obtain ⟨ΩB, mB, PB, hPB, B, hB⟩ := Sandpile.Continuum.exists_isBrownian d
  letI := mW
  letI := hPW
  letI := mB
  letI := hPB
  obtain ⟨Z, hPos, hRatio⟩ := h ΩW PW W hW ΩB PB B hB
  exact exists_growth_limit_of_ratio ((4 - (d : ℝ)) / 4) _ hPos _ hRatio

end Sandpile.Support
