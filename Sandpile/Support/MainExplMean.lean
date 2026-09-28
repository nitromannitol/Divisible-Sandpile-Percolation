import Sandpile.Support.MainExplScaling
import Sandpile.Support.MeanAAssembly
import Sandpile.Support.MeanAVersion
import Sandpile.Support.MeanAMean
import Sandpile.Support.MeanAExpLimit
import Sandpile.Support.Dgt4OriginProb

/-! # Positivity of the limiting mean at the origin

The positive mean limit in dimensions one through three, derived from the
parabolic scaling limit and the concentration estimates for the rescaled odometer.
Compact tightness bounds its means, so the centered exponential estimate gives a
uniform exponential moment. Passing that bound through the weak limit yields
convergence of the first two moments and positivity of the limiting mean.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

/-- **The mean limit and the positivity of the limiting mean and variance at the
origin**, on an arbitrary pair of realization spaces, from the scaling limit at
`T = 1`, compact tightness, and the uniform exponential concentration bound. -/
theorem mean_variance_limit_at_origin_of_localCLT
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Space d → ℝ≥0 → ΩB → Space d)
    (hB : ∀ y : Space d, IsBrownian d y (B y) PB)
    (hBc : ∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) :
    ∃ Z : ℝ → Space d → ΩW → ℝ,
      MemLp (fun ω => continuumValue d Z B PB 1 0 ω) 2 PW ∧
      (∀ᵐ ω ∂PW, 0 ≤ continuumValue d Z B PB 1 0 ω) ∧
      0 < variance (fun ω => continuumValue d Z B PB 1 0 ω) PW ∧
      0 < ∫ ω, continuumValue d Z B PB 1 0 ω ∂PW ∧
      Tendsto (fun R : ℝ => ∫ σ, Sandpile.Continuum.rescaledOdometer d R 1 0 σ
        ∂(Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (∫ ω, continuumValue d Z B PB 1 0 ω ∂PW)) ∧
      Tendsto (fun R : ℝ => variance
        (fun σ => Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
        (Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (variance (fun ω => continuumValue d Z B PB 1 0 ω) PW)) := by
  have hν2 : 0 < variance (id : ℝ → ℝ) ν := ENNReal.toReal_pos hvar.ne' hvar'.ne
  have hsq : Integrable (fun z : ℝ => z ^ 2) ν := integrable_sq_of_evariance ν hvar'
  obtain ⟨Z, hZmod, hZcont, hZgrow⟩ :=
    exists_continuous_version_growth hd hd3 hν2.le PW W hW
  have hib := Sandpile.brownian_scaling_limit_of_localCLT hLocalCLT hStab d hd hd3 ν hmean hvar
    hvar' θ₀ hθ₀ hexp ΩW PW W hW Z hZmod hZcont hZgrow ΩB PB B hB hBc hBm 1 one_pos
  have hres := tendstoInDistribution_rescaled_one_zero d ν PW PB Z B
    (hib.1 1 (fun _ => (0 : Space d)))
  obtain ⟨K, hK⟩ := exists_uniform_mean_rescaled_of_tightness d hd hd3 ν hsq
    ((hib.2 {0} isCompact_singleton).1)
  obtain ⟨θ, A, hθ, hA⟩ := exists_uniform_exp_moment_rescaled_mass d hd hd3
    θ₀ (∫ z, Real.exp (θ₀ * |z|) ∂ν) hθ₀
  have hD := hA ν inferInstance hexp le_rfl K hK
  let C := Real.exp (θ * K) * A
  have hC : 0 ≤ C := (integral_nonneg fun σ =>
    Real.exp_nonneg (θ * rescaledOdometer d 1 1 0 σ)).trans (hD 1 le_rfl).2
  have hnn : ∀ᵐ ω ∂PW, 0 ≤ continuumValue d Z B PB 1 0 ω :=
    ae_nonneg_of_tendstoInDistribution hres (fun r => ae_of_all _ fun σ =>
      rescaledOdometer_nonneg d (lt_of_lt_of_le zero_lt_one r.2) 1 0 σ)
  have hE := integrable_exp_of_uniform_exp hres hnn θ C hθ.le hC
    (Eventually.of_forall fun r => ⟨ae_of_all _ fun σ =>
      rescaledOdometer_nonneg d (lt_of_lt_of_le zero_lt_one r.2) 1 0 σ, hD r r.2⟩)
  obtain ⟨hZL2, hZnn, hmean0, hvar0⟩ :=
    tendsto_moments_rescaled_of_conv d hd ν hsq PW PB Z B hres θ C hθ
      (fun R hR => (hD R hR).1)
      (fun R hR => (hD R hR).2) hE.1 hE.2
  have hVpos : 0 < variance (fun ω => continuumValue d Z B PB 1 0 ω) PW :=
    variance_continuumValue_pos PW PB W hW hd hd3 hν2 Z hZmod hZcont B hZL2
  exact ⟨Z, hZL2, hZnn, hVpos,
    integral_pos_of_ae_nonneg_of_variance_pos PW _ hZL2 hZnn hVpos, hmean0, hvar0⟩

/-- The rescaled mean converges to a positive limit, from the parabolic limit
and uniform exponential concentration (`sandpile.tex:1995-2052`). -/
theorem mean_growth_le_three_of_localCLT
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 L) := by
  haveI := hprob
  refine mean_growth_le_three_of_variance_pos d ν ?_
  intro ΩW _ PW _ W hW ΩB _ PB _ B hB hBc hBm
  obtain ⟨Z, hZL2, hZnn, hVpos, hLpos, hmean0, _⟩ :=
    mean_variance_limit_at_origin_of_localCLT hLocalCLT hStab d hd hd3 ν hmean hvar hvar'
      θ₀ hθ₀ hexp ΩW PW W hW ΩB PB B hB hBc hBm
  exact ⟨Z, hZL2, hZnn, hVpos,
    tendsto_mean_ratio_of_rescaled d ν _ (ne_of_gt hLpos) hmean0⟩

end Sandpile.Support
