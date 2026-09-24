/-
The limit of the mean and of the variance of the rescaled odometer at `(1,0)`.

`cor:dlt4-mean-asymptotic` (`sandpile.tex:2034-2052`) is stated in the paper as
an immediate consequence of the uniform exponential moment of
`prop:continuum-value-selfsimilar`: convergence in distribution upgrades to
convergence of the first two moments as soon as the family is uniformly
exponentially integrable on the nonnegative half-line, which is the content of
`MeanAMoment`.  Two bookkeeping steps separate that from the frozen statements.

* The moment theorems ask their hypotheses at EVERY index, while the rescaled
  odometer is nonnegative with a uniform exponential moment only for `R ≥ 1`.
  The family is therefore restricted to `[1,∞)` through `MeanAIndex` and the
  limit carried back to `atTop` on `ℝ` at the end.
* The square integrability of the limiting value is not assumed: it follows from
  the exponential moment, since the value is almost surely nonnegative as a limit
  in distribution of nonnegative variables.
-/
import Sandpile.Support.MeanAIndex
import Sandpile.Support.MeanAMoment
import Sandpile.Support.MeanAPositive
import Sandpile.Support.ContMeanAsymptotic
import Sandpile.Support.Odometer

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The rescaled odometer is nonnegative at every positive scale. -/
theorem rescaledOdometer_nonneg (d : ℕ) {R : ℝ} (hR : 0 < R) (T : ℝ) (x : Space d)
    (σ : Sandpile.Site d → ℝ) : 0 ≤ Sandpile.Continuum.rescaledOdometer d R T x σ := by
  unfold Sandpile.Continuum.rescaledOdometer
  exact mul_nonneg (Real.rpow_nonneg hR.le _) (Sandpile.odometer_nonneg _ _ _)

/-- **The two moment limits at `(1,0)`**, together with the square integrability and
the nonnegativity of the limiting value.  Everything is read off the convergence in
distribution of the rescaled odometer at the origin and the uniform exponential
moment of the family, at the scales `R ≥ 1` where both hold. -/
theorem tendsto_moments_rescaled_of_conv {ΩW ΩB : Type*} [MeasurableSpace ΩW]
    [MeasurableSpace ΩB] (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    (PW : Measure ΩW) [IsProbabilityMeasure PW] (PB : Measure ΩB)
    (Z : ℝ → Space d → ΩW → ℝ) (B : Space d → ℝ≥0 → ΩB → Space d)
    (hres : TendstoInDistribution
      (fun (r : Set.Ici (1 : ℝ)) (σ : Sandpile.Site d → ℝ) =>
        Sandpile.Continuum.rescaledOdometer d (r : ℝ) 1 0 σ)
      atTop (fun ω => continuumValue d Z B PB 1 0 ω)
      (fun _ => Sandpile.centeredMassLaw d ν) PW)
    (θ C : ℝ) (hθ : 0 < θ)
    (hXexp : ∀ R : ℝ, 1 ≤ R →
      Integrable (fun σ => Real.exp (θ * Sandpile.Continuum.rescaledOdometer d R 1 0 σ))
        (Sandpile.centeredMassLaw d ν))
    (hXexpC : ∀ R : ℝ, 1 ≤ R →
      ∫ σ, Real.exp (θ * Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
        ∂(Sandpile.centeredMassLaw d ν) ≤ C)
    (hZexp : Integrable (fun ω => Real.exp (θ * continuumValue d Z B PB 1 0 ω)) PW)
    (hZexpC : ∫ ω, Real.exp (θ * continuumValue d Z B PB 1 0 ω) ∂PW ≤ C) :
    MemLp (fun ω => continuumValue d Z B PB 1 0 ω) 2 PW ∧
      (∀ᵐ ω ∂PW, 0 ≤ continuumValue d Z B PB 1 0 ω) ∧
      Tendsto (fun R : ℝ => ∫ σ, Sandpile.Continuum.rescaledOdometer d R 1 0 σ
        ∂(Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (∫ ω, continuumValue d Z B PB 1 0 ω ∂PW)) ∧
      Tendsto (fun R : ℝ => variance
        (fun σ => Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
        (Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (variance (fun ω => continuumValue d Z B PB 1 0 ω) PW)) := by
  classical
  set ι := (Set.Ici (1 : ℝ))
  have hXnn : ∀ r : ι, ∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
      0 ≤ Sandpile.Continuum.rescaledOdometer d (r : ℝ) 1 0 σ := fun r =>
    Filter.Eventually.of_forall fun σ =>
      rescaledOdometer_nonneg d (lt_of_lt_of_le zero_lt_one r.2) 1 0 σ
  have hZnn : ∀ᵐ ω ∂PW, 0 ≤ continuumValue d Z B PB 1 0 ω :=
    ae_nonneg_of_tendstoInDistribution hres hXnn
  -- square integrability of the limit from its exponential moment
  have hZmeas : AEMeasurable (fun ω => continuumValue d Z B PB 1 0 ω) PW :=
    hres.aemeasurable_limit
  have hZabs : Integrable (fun ω =>
      Real.exp (θ * |continuumValue d Z B PB 1 0 ω|)) PW := by
    refine hZexp.congr ?_
    filter_upwards [hZnn] with ω hω
    rw [abs_of_nonneg hω]
  have hZL2 : MemLp (fun ω => continuumValue d Z B PB 1 0 ω) 2 PW :=
    memLp_continuumValue_of_exp_moment d Z B PB PW θ hθ hZmeas hZabs
  have hXL2 : ∀ r : ι, MemLp (fun σ =>
      Sandpile.Continuum.rescaledOdometer d (r : ℝ) 1 0 σ) 2
      (Sandpile.centeredMassLaw d ν) := fun r =>
    memLp_rescaledOdometer_centered d hd ν hsq (r : ℝ) 1 0
  have hXe : ∀ r : ι, Integrable (fun σ =>
      Real.exp (θ * Sandpile.Continuum.rescaledOdometer d (r : ℝ) 1 0 σ))
      (Sandpile.centeredMassLaw d ν) := fun r => hXexp (r : ℝ) r.2
  have hXeC : ∀ r : ι, ∫ σ, Real.exp (θ *
      Sandpile.Continuum.rescaledOdometer d (r : ℝ) 1 0 σ)
      ∂(Sandpile.centeredMassLaw d ν) ≤ C := fun r => hXexpC (r : ℝ) r.2
  have hmean := tendsto_integral_of_uniform_exp hres hXnn hZnn
    (fun r => (hXL2 r).integrable one_le_two) (hZL2.integrable one_le_two)
    θ C hθ hXe hXeC hZexp hZexpC
  have hvar := tendsto_variance_of_uniform_exp hres hXnn hZnn hXL2 hZL2
    θ C hθ hXe hXeC hZexp hZexpC
  exact ⟨hZL2, hZnn,
    tendsto_of_tendsto_val_Ici 1 _ _ hmean,
    tendsto_of_tendsto_val_Ici 1 _ _ hvar⟩

end Sandpile.Support
