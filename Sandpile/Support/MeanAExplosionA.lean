import Sandpile.Support.MeanAAssembly
import Sandpile.Support.MeanAVersion
import Sandpile.Support.Dgt4OriginProb
import Sandpile.Frozen.BrownianScalingLimit
import Sandpile.Frozen.ContinuumValueSelfSimilar

/-!
# Theorem 1.3(i)(a): the mean odometer growth rate at the origin

Theorem 1.3(i)(a) of `sandpile.tex` (`sandpile.tex:206-217`) wired to the two
statements its proof names, on the spaces the repository builds.

The paper's proof of `thm:main-explosion` says at `sandpile.tex:299` "Part (i)(a)
is Corollary~\ref{cor:dlt4-mean-asymptotic}", and the corollary's ninth clause is
`E u_t(0) ∼ E𝒰(1,0)t^{(4-d)/4}`.  Only the point `(1,0)` enters, so the
self-similarity of the limit is not needed here: what is needed is the mean limit
at the origin, the positivity of the limiting mean, and the two inputs that give
them, namely the parabolic scaling limit `thm:main-explosion`(i)(b) at `T = 1`
and the uniform exponential moment of `prop:continuum-value-selfsimilar`.

The field `Z` is the continuous version of the Gaussian heat potential built in
`MeanAVersion`; the white-noise space and the family of Brownian motions are
those of `Sandpile.Continuum.exists_isWhiteNoise` and
`Sandpile.Continuum.exists_isBrownian`, which `mean_growth_le_three_of_variance_pos`
supplies.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

/-- **The mean limit and the positivity of the limiting mean and variance at the
origin**, on an arbitrary pair of realization spaces, from the scaling limit at
`T = 1` and the exponential moments of `prop:continuum-value-selfsimilar`. -/
theorem mean_variance_limit_at_origin
    (_hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (_hVarScale : Sandpile.External.VarianceScale)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hOS : Sandpile.External.ContinuumOptimalStopping ΩB)
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
  have hd0 : 0 < d := hd
  have hν2 : 0 < variance (id : ℝ → ℝ) ν := ENNReal.toReal_pos hvar.ne' hvar'.ne
  have hsq : Integrable (fun z : ℝ => z ^ 2) ν := integrable_sq_of_evariance ν hvar'
  obtain ⟨Z, hZmod, hZcont, hZgrow⟩ :=
    exists_continuous_version_growth hd hd3 hν2.le PW W hW
  have hib := Sandpile.Frozen.brownian_scaling_limit hStab d hd hd3 ν hmean hvar hvar'
    θ₀ hθ₀ hexp ΩW PW W hW Z hZmod hZcont hZgrow ΩB PB B hB hBc hBm 1 one_pos
  have hres := tendstoInDistribution_rescaled_one_zero d ν PW PB Z B
    (hib.1 1 (fun _ => (0 : Space d)))
  have hself := Sandpile.Frozen.continuum_value_self_similar hStab d hd0 hd3 ν hmean
    hvar hvar' θ₀ hθ₀ hexp PW W hW Z hZmod hZcont hZgrow PB hOS B hB hBc hBm
  obtain ⟨θ, hθ, ⟨M, hM⟩, hZexp⟩ := hself.2.1
  set C : ℝ := max M (∫ ω, Real.exp (θ * continuumValue d Z B PB 1 0 ω) ∂PW) with hC
  obtain ⟨hZL2, hZnn, hmean0, hvar0⟩ :=
    tendsto_moments_rescaled_of_conv d hd ν hsq PW PB Z B hres θ C hθ
      (fun R hR => (hM R hR).1)
      (fun R hR => le_trans (hM R hR).2 (le_max_left _ _))
      hZexp (le_max_right _ _)
  have hVpos : 0 < variance (fun ω => continuumValue d Z B PB 1 0 ω) PW :=
    variance_continuumValue_pos PW PB W hW hd hd3 hν2 Z hZmod hZcont B hZL2
  exact ⟨Z, hZL2, hZnn, hVpos,
    integral_pos_of_ae_nonneg_of_variance_pos PW _ hZL2 hZnn hVpos, hmean0, hvar0⟩

/-- **Theorem 1.3(i)(a), fully wired.**  The rescaled mean converges to a limit in
`(0,∞)`. -/
theorem mean_growth_le_three_wired
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (hVarScale : Sandpile.External.VarianceScale)
    (hOS : ∀ (ΩB : Type) [MeasurableSpace ΩB], Sandpile.External.ContinuumOptimalStopping ΩB)
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
    mean_variance_limit_at_origin hLocalCLT hStab hVarScale d hd hd3 ν hmean hvar hvar'
      θ₀ hθ₀ hexp ΩW PW W hW ΩB PB (hOS ΩB) B hB hBc hBm
  exact ⟨Z, hZL2, hZnn, hVpos,
    tendsto_mean_ratio_of_rescaled d ν _ (ne_of_gt hLpos) hmean0⟩

end Sandpile.Support
