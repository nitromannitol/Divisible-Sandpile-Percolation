import Sandpile.Support.SquareSummableTransferCLT

/-!
# Weighted central limits under the centered mass law

The centered mass law transports to the i.i.d. scenery law under the scenery
map. Thus the weighted central limit theorem with square-summable defect also
holds when the weighted sums are read from the centered mass configuration.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped lp ENNReal

namespace Sandpile.Support

/-- The square-summable defect central limit theorem under the centered mass
law of `σ = 1 + 2dζ`. -/
theorem tendstoInDistribution_linear_of_sq_defect_mass
    {d : ℕ} (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (a b : ℝ → ℓ²(Sandpile.Site d, ℝ)) (s : ℝ → Finset (Sandpile.Site d))
    (hs : ∀ R x, x ∉ s R → a R x = 0)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, ∀ x, |b R x| ≤ δ)
    (B : ℝ) (hB : Tendsto (fun R => ‖b R‖) atTop (𝓝 B))
    (hdefect : Tendsto (fun R => ∑' x, ENNReal.ofReal ((a R x - b R x) ^ 2))
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) =>
        ∑ x ∈ s R, a R x * Sandpile.scenery d σ x)
      atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
      (gaussianReal 0 (Real.toNNReal ((∫ z, z ^ 2 ∂ν) * B ^ 2))) := by
  have hclt := tendstoInDistribution_linear_of_sq_defect ν hsq hmean a b s hs
    hsmall B hB hdefect
  have hm (R : ℝ) : Measurable (fun ζ : Sandpile.Site d → ℝ =>
      ∑ x ∈ s R, a R x * ζ x) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (measurable_pi_apply i)
  have hmp : MeasurePreserving (Sandpile.scenery d) (Sandpile.centeredMassLaw d ν)
      (LatticeProb.iidLaw d ν) :=
    ⟨Sandpile.measurable_scenery d, Sandpile.map_scenery_centeredMassLaw d ν hd⟩
  refine ⟨fun R => ((hm R).comp hmp.measurable).aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  refine Filter.Tendsto.congr (fun R => ?_) hclt.tendsto
  apply ProbabilityMeasure.toMeasure_injective
  have hmap := Measure.map_map (μ := Sandpile.centeredMassLaw d ν) (hm R) hmp.measurable
  rw [hmp.map_eq] at hmap
  exact hmap

end Sandpile.Support
