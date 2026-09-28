import Sandpile.Support.Dgt4AConditionScenery

/-!
# Integrability of the conditional expectation in Step 2

**The integrability that the comparison of Step 2 needs** (`sandpile.tex:5125-5131`).

`abs_integral_sub_avgIntegral_le` compares the conditional expectation at a level with its
average over the level.  Both the inner conditional expectation, for almost every level, and
the average over the level are integrals of the SAME function on the product of the level and
the residual, because the law of the scenery is the image of `N(0,1)\otimes\rho` under the
shift `(s,r)\mapsto r+se` (`gaussLaw_eq_map_prod`).  So one integrability statement on that
product, which is what `integral_gaussLaw_shift` already establishes inside its proof,
supplies both: `Integrable.prod_right_ae` gives the inner one and
`Integrable.integral_prod_left` the outer one.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The conditioned integrand on the product of the level and the residual. -/
theorem integrable_prod_gaussLaw_shift (hd : 5 ≤ d) (F : (Site d → ℝ) → ℝ)
    (hF : Integrable F (LatticeProb.gaussLaw (Site d))) :
    Integrable (fun p : ℝ × (Site d → ℝ) =>
        F (fun z => p.2 z + p.1 * (greenUnit d hd : Site d → ℝ) z))
      ((gaussianReal 0 1).prod ((LatticeProb.gaussLaw (Site d)).map (residField d hd))) := by
  have hPhi := measurable_shiftPair hd
  haveI : IsProbabilityMeasure ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) :=
    Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  have hmap := gaussLaw_eq_map_prod hd
  have hFm : AEStronglyMeasurable F
      (Measure.map (fun p : ℝ × (Site d → ℝ) =>
          fun z => p.2 z + p.1 * (greenUnit d hd : Site d → ℝ) z)
        ((gaussianReal 0 1).prod ((LatticeProb.gaussLaw (Site d)).map (residField d hd)))) := by
    rw [← hmap]; exact hF.1
  have hmm : Integrable F
      (Measure.map (fun p : ℝ × (Site d → ℝ) =>
          fun z => p.2 z + p.1 * (greenUnit d hd : Site d → ℝ) z)
        ((gaussianReal 0 1).prod
          ((LatticeProb.gaussLaw (Site d)).map (residField d hd)))) := by
    rw [← hmap]; exact hF
  exact (integrable_map_measure hFm hPhi.aemeasurable).mp hmm

/-- **The conditional expectation of Step 2 exists for almost every level.** -/
theorem ae_integrable_gaussLaw_shift (hd : 5 ≤ d) (F : (Site d → ℝ) → ℝ)
    (hF : Integrable F (LatticeProb.gaussLaw (Site d))) :
    ∀ᵐ s ∂(gaussianReal 0 1),
      Integrable (fun r : Site d → ℝ => F (fun z => r z + s * (greenUnit d hd : Site d → ℝ) z))
        ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) :=
  (integrable_prod_gaussLaw_shift hd F hF).prod_right_ae

/-- **The conditional expectation of Step 2 is integrable in the level**, which is the
hypothesis `abs_integral_sub_avgIntegral_le` needs to compare it with its average. -/
theorem integrable_integral_gaussLaw_shift (hd : 5 ≤ d) (F : (Site d → ℝ) → ℝ)
    (hF : Integrable F (LatticeProb.gaussLaw (Site d))) :
    Integrable (fun s : ℝ =>
        ∫ r, F (fun z => r z + s * (greenUnit d hd : Site d → ℝ) z)
          ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)))
      (gaussianReal 0 1) :=
  (integrable_prod_gaussLaw_shift hd F hF).integral_prod_left

/-- The scenery integrand transported to the standard Gaussian product. -/
theorem integrable_comp_scale (v : ℝ≥0) (F : (Site d → ℝ) → ℝ)
    (hF : Integrable F (LatticeProb.iidLaw d (gaussianReal 0 v))) :
    Integrable (fun ω : Site d → ℝ => F (fun z => Real.sqrt (v : ℝ) * ω z))
      (LatticeProb.gaussLaw (Site d)) := by
  have hS : Measurable (fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z) := by
    fun_prop
  rw [iidLaw_gaussianReal_eq_map d v] at hF
  exact (integrable_map_measure hF.1 hS.aemeasurable).mp hF

/-- **The two integrability statements of Step 2 at the scenery**: the conditional
expectation of an integrable functional of the scenery exists for almost every level and is
integrable in the level. -/
theorem ae_integrable_iidLaw_gauss_shift (hd : 5 ≤ d) (v : ℝ≥0) (F : (Site d → ℝ) → ℝ)
    (hF : Integrable F (LatticeProb.iidLaw d (gaussianReal 0 v))) :
    ∀ᵐ s ∂(gaussianReal 0 1),
      Integrable (fun r : Site d → ℝ =>
          F (fun z => Real.sqrt (v : ℝ) * (r z + s * (greenUnit d hd : Site d → ℝ) z)))
        ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) :=
  ae_integrable_gaussLaw_shift hd _ (integrable_comp_scale v F hF)

/-- The variance-`v` analogue of `integrable_integral_gaussLaw_shift`: the conditional
expectation of an integrable functional `F` of the `iidLaw d (gaussianReal 0 v)`-scenery is
integrable in the level `s`, by transporting `F` to the standard Gaussian product with
`integrable_comp_scale` and applying `integrable_integral_gaussLaw_shift`. -/
theorem integrable_integral_iidLaw_gauss_shift (hd : 5 ≤ d) (v : ℝ≥0) (F : (Site d → ℝ) → ℝ)
    (hF : Integrable F (LatticeProb.iidLaw d (gaussianReal 0 v))) :
    Integrable (fun s : ℝ =>
        ∫ r, F (fun z => Real.sqrt (v : ℝ) * (r z + s * (greenUnit d hd : Site d → ℝ) z))
          ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)))
      (gaussianReal 0 1) :=
  integrable_integral_gaussLaw_shift hd _ (integrable_comp_scale v F hF)

end Sandpile
