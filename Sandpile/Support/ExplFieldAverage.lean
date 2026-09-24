/-
Averaging the continuous Gaussian heat potential over a finite measure.

Bounded measurable time-space families have integrable Green kernels in both
spatial L1 and L2. Their pointwise spatial integrals represent the Bochner L2
integral, so white-noise Fubini holds for the actual continuous field. In
particular the Brownian heat-kernel density defines a probability measure.
-/
import Sandpile.Support.ExplGreenFubini
import Sandpile.Support.ExplGreenSemigroup

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile.Support Sandpile.Continuum

theorem isProbabilityMeasure_heatKernelBM {d : ℕ} (hd : 1 ≤ d) {r : ℝ}
    (hr : 0 < r) (x : Space d) :
    IsProbabilityMeasure ((volume : Measure (Space d)).withDensity
      (fun y => ENNReal.ofReal (heatKernelBM d r x y))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernelBM_space hd hr x)
    (Eventually.of_forall fun y => heatKernelBM_nonneg d hr.le x y)]
  rw [integral_heatKernelBM_eq_one hd hr x, ENNReal.ofReal_one]

end Sandpile.Support

namespace Sandpile.Continuum

open Sandpile.Support Sandpile.Continuum

theorem gaussianPotential_family_integral_comm_pointwise {ΩW U : Type*}
    [MeasurableSpace ΩW] [MeasurableSpace U] {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {PW : Measure ΩW} [IsProbabilityMeasure PW] {W : (Space d → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise d W PW) (ν2 : ℝ) (Z : ℝ → Space d → ΩW → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[PW] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (μ : Measure U) [IsFiniteMeasure μ] (q : U → ℝ≥0 × Space d) (hq : Measurable q)
    (T : ℝ≥0) (hT : ∀ u, (q u).1 ≤ T) :
    (∀ᵐ ω ∂PW, Integrable (fun u => Z (q u).1 (q u).2 ω) μ) ∧
      W (fun y => ∫ u, Real.sqrt ν2 * greenTimeBM d (q u).1 (q u).2 y ∂μ) =ᵐ[PW]
        fun ω => ∫ u, Z (q u).1 (q u).2 ω ∂μ := by
  let F (b : U) : Lp ℝ 2 (volume : Measure (Space d)) := Real.sqrt ν2 •
    (memLp_greenTimeBM hd hd3 (q b).1.property (q b).2).toLp (greenTimeBM d (q b).1 (q b).2)
  let f (b : U) (y : Space d) := Real.sqrt ν2 * greenTimeBM d (q b).1 (q b).2 y
  have hF : Integrable F μ :=
    (integrable_greenTimeBM_toLp_of_bounded_time μ hd hd3 q hq T hT).smul (Real.sqrt ν2)
  have hf : Integrable (Function.uncurry f) (μ.prod (volume : Measure (Space d))) :=
    (integrable_greenTimeBM_product μ hd q hq T hT).const_mul (Real.sqrt ν2)
  have he (b : U) : f b =ᵐ[volume] (fun y => F b y) := by
    filter_upwards [Lp.coeFn_smul (Real.sqrt ν2)
      ((memLp_greenTimeBM hd hd3 (q b).1.property (q b).2).toLp (greenTimeBM d (q b).1 (q b).2)),
      (memLp_greenTimeBM hd hd3 (q b).1.property (q b).2).coeFn_toLp] with y h1 h2
    change f b y = (Real.sqrt ν2 •
      (memLp_greenTimeBM hd hd3 (q b).1.property (q b).2).toLp (greenTimeBM d (q b).1 (q b).2)) y
    exact (congrArg (fun a : ℝ => Real.sqrt ν2 * a) h2).symm.trans h1.symm
  have hrep := coe_integral_L2_eq_integral_of_integrable μ volume F hF f hf he
  have hmem : MemLp (fun y => ∫ b, f b y ∂μ) 2 volume := MemLp.ae_eq hrep (Lp.memLp (∫ b, F b ∂μ))
  have hnoise : W (fun y => (∫ b, F b ∂μ) y) =ᵐ[PW] W (fun y => ∫ b, f b y ∂μ) := by
    apply ((hW.gaussian.hasGaussianLaw_eval _).memLp_two.toLp_eq_toLp_iff
      (hW.gaussian.hasGaussianLaw_eval _).memLp_two).mp
    exact toLp_eq_of_covariance_of_ae_eq volume PW W
      (fun a => (hW.gaussian.hasGaussianLaw_eval a).memLp_two) hW.cov _ _ (Lp.memLp _) hmem hrep
  have hmain := gaussian_whiteNoise_integral_comm_continuous hd hd3 hW ν2 Z hmod hc μ q hq T hT
  exact ⟨hmain.1, hnoise.symm.trans hmain.2⟩

end Sandpile.Continuum

