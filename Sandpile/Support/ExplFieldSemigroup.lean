import Sandpile.Support.ExplFieldAverage
import Sandpile.Support.ExplGreenSemigroup

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support
open Sandpile.Support Sandpile.Continuum
/-- Integration against the Brownian transition measure. -/
theorem integral_heatKernelBM_measure {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (x : Space d)
    (f : Space d → ℝ) :
    (∫ y, f y ∂((volume : Measure (Space d)).withDensity
      (fun y => ENNReal.ofReal (heatKernelBM d r x y)))) =
      ∫ y, heatKernelBM d r x y * f y := by
  have hm : Measurable (fun y => ENNReal.ofReal (heatKernelBM d r x y)) := by
    unfold heatKernelBM
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [ENNReal.toReal_ofReal (heatKernelBM_nonneg d hr x y), smul_eq_mul]
end Sandpile.Support

namespace Sandpile.Support
open Sandpile.Support Sandpile.Continuum
/-- White noise identifies spatially almost-everywhere equal square-integrable indices. -/
theorem whiteNoise_index_congr {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    {f g : Space d → ℝ} (hf : MemLp f 2 volume) (hfg : f =ᵐ[volume] g) :
    W f =ᵐ[P] W g := by
  have hg : MemLp g 2 volume := hf.ae_eq hfg
  apply ((hW.gaussian.hasGaussianLaw_eval f).memLp_two.toLp_eq_toLp_iff
    (hW.gaussian.hasGaussianLaw_eval g).memLp_two).mp
  exact toLp_eq_of_covariance_of_ae_eq volume P W
    (fun q => (hW.gaussian.hasGaussianLaw_eval q).memLp_two) hW.cov f g hf hg hfg
end Sandpile.Support

namespace Sandpile.Continuum
open Sandpile.Support

/-- The heat semigroup identity for a continuous modification, at fixed parameters. -/
theorem gaussianPotential_heat_semigroup {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (ν2 : ℝ) (Z : ℝ → Space d → Ω → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[P] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (x : Space d) :
    ∀ᵐ ω ∂P, Integrable (fun y => heatKernelBM d r x y * Z s y ω) volume ∧
      (∫ y, heatKernelBM d r x y * Z s y ω) = Z (r + s) x ω - Z r x ω := by
  let μ : Measure (Space d) := volume.withDensity (fun y => ENNReal.ofReal (heatKernelBM d r x y))
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_heatKernelBM hd hr x
  have hmain := gaussianPotential_family_integral_comm_pointwise hd hd3 hW ν2 Z hmod hc μ
    (fun y => ((⟨s, hs⟩ : ℝ≥0), y)) (by fun_prop) ⟨s, hs⟩ (fun _ => le_rfl)
  have hrs : 0 ≤ r + s := add_nonneg hr.le hs
  have hplus := memLp_greenTimeBM hd hd3 hrs x
  have hzero := memLp_greenTimeBM hd hd3 hr.le x
  let f : Space d → ℝ := greenTimeBM d (r + s) x - greenTimeBM d r x
  have hf : MemLp f 2 volume := hplus.sub hzero
  have hk : Real.sqrt ν2 • f =ᵐ[volume]
      (fun z => ∫ y, Real.sqrt ν2 * greenTimeBM d s y z ∂μ) := by
    filter_upwards [integral_heatKernelBM_mul_greenTimeBM_ae_eq_sub hd hr hs x] with z hz
    change Real.sqrt ν2 * (greenTimeBM d (r + s) x z - greenTimeBM d r x z) = _
    calc Real.sqrt ν2 * (greenTimeBM d (r + s) x z - greenTimeBM d r x z)
        = Real.sqrt ν2 * ∫ y, heatKernelBM d r x y * greenTimeBM d s z y := by rw [hz]
      _ = Real.sqrt ν2 * ∫ y, heatKernelBM d r x y * greenTimeBM d s y z := by
          congr 1
          apply integral_congr_ae
          exact Eventually.of_forall fun y => congrArg (fun a => heatKernelBM d r x y * a)
            (greenTimeBM_symm d s z y)
      _ = ∫ y, Real.sqrt ν2 * greenTimeBM d s y z ∂μ := by
          rw [integral_const_mul]
          congr 1
          exact (integral_heatKernelBM_measure hr.le x _).symm
  have heq := whiteNoise_index_congr hW (hf.const_smul (Real.sqrt ν2)) hk
  have ha := hW.add f (greenTimeBM d r x) hf hzero
  have hfg : f + greenTimeBM d r x = greenTimeBM d (r + s) x := sub_add_cancel _ _
  rw [hfg] at ha
  have hm := hW.smul (Real.sqrt ν2) f hf
  have hdm : Measurable (fun y => ENNReal.ofReal (heatKernelBM d r x y)) := by
    unfold heatKernelBM
    fun_prop
  filter_upwards [hmain.1, hmain.2, heq, ha, hm, hmod r hr.le x, hmod (r + s) hrs x]
    with ω hi hcomm heqω haω hmω hrω hrsω
  have hI := (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure (Space d)))
    (g := fun y : Space d => Z s y ω) hdm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hi
  have hIf : Integrable (fun y => heatKernelBM d r x y * Z s y ω) volume := by
    simpa only [ENNReal.toReal_ofReal (heatKernelBM_nonneg d hr.le x _), smul_eq_mul] using hI
  refine ⟨hIf, ?_⟩
  calc (∫ y, heatKernelBM d r x y * Z s y ω) = ∫ y, Z s y ω ∂μ :=
        (integral_heatKernelBM_measure hr.le x _).symm
    _ = W (fun z => ∫ y, Real.sqrt ν2 * greenTimeBM d s y z ∂μ) ω := hcomm.symm
    _ = Real.sqrt ν2 * W f ω := heqω.symm.trans hmω
    _ = Z (r + s) x ω - Z r x ω := by
        rw [hrsω, hrω]
        unfold gaussianPotential
        rw [haω]
        ring
end Sandpile.Continuum
