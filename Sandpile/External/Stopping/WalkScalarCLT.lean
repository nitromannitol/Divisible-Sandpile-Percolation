import Sandpile.External.Stopping.WalkStepMoments
import LatticeProb.Walk.MaxDisp
import Mathlib.Probability.CentralLimitTheorem

/-!
# Central limit theorem for walk projections

A fixed linear projection of the sum of independent walk increments, scaled by
`√n`, converges in law to a centered Gaussian with variance `∑ᵢ aᵢ² / d`.
This is the scalar i.i.d. central limit theorem applied to the step law.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.External.Stopping

/-- A fixed linear projection of the simple walk obeys the scalar central limit theorem. -/
theorem tendstoInDistribution_projected_increments (d : ℕ) [NeZero d]
    (a : Fin d → ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) (ξ : ℕ → LatticeProb.Site d) =>
        (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, LatticeProb.dotSite a (ξ k))
      atTop (id : ℝ → ℝ) (fun _ => LatticeProb.incPathLaw d)
      (gaussianReal 0 (Real.toNNReal ((∑ i, (a i) ^ 2) / d))) := by
  let X : ℕ → (ℕ → LatticeProb.Site d) → ℝ :=
    fun k ξ => LatticeProb.dotSite a (ξ k)
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hdot : Integrable (LatticeProb.dotSite a) (LatticeProb.incLaw d) :=
    LatticeProb.integrable_incLaw hd _
  have hmeas : Measurable (LatticeProb.dotSite a) := measurable_of_countable _
  have hcoord : iIndepFun (fun (k : ℕ) (ξ : ℕ → LatticeProb.Site d) => ξ k)
      (LatticeProb.incPathLaw d) := by
    unfold LatticeProb.incPathLaw
    exact iIndepFun_infinitePi (X := fun _ z => z) fun _ => measurable_id
  have hindep : iIndepFun X (LatticeProb.incPathLaw d) :=
    hcoord.comp (fun _ => LatticeProb.dotSite a) (fun _ => hmeas)
  have hident0 (k : ℕ) : IdentDistrib (X k) (LatticeProb.dotSite a)
      (LatticeProb.incPathLaw d) (LatticeProb.incLaw d) := by
    refine ⟨(hmeas.comp (measurable_pi_apply k)).aemeasurable, hmeas.aemeasurable, ?_⟩
    change (LatticeProb.incPathLaw d).map (LatticeProb.dotSite a ∘ fun ξ => ξ k) = _
    rw [← Measure.map_map hmeas (measurable_pi_apply k)]
    rw [LatticeProb.incPathLaw, Measure.infinitePi_map_eval]
  have hident (k : ℕ) : IdentDistrib (X k) (X 0)
      (LatticeProb.incPathLaw d) (LatticeProb.incPathLaw d) :=
    (hident0 k).trans (hident0 0).symm
  have hmean : (∫ ξ, X 0 ξ ∂(LatticeProb.incPathLaw d)) = 0 := by
    rw [(hident0 0).integral_eq, integral_dotSite_incLaw]
  have hvar : variance (X 0) (LatticeProb.incPathLaw d) = (∑ i, (a i) ^ 2) / d := by
    rw [(hident0 0).variance_eq, variance_eq_integral hmeas.aemeasurable,
      integral_dotSite_incLaw]
    simp only [sub_zero, integral_dotSite_sq_incLaw]
  have hmem : MemLp (X 0) 2 (LatticeProb.incPathLaw d) := by
    apply (hident0 0).memLp_iff.mpr
    apply (memLp_two_iff_integrable_sq hdot.aestronglyMeasurable).mpr
    exact LatticeProb.integrable_incLaw hd _
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := X)
    (Y := (id : ℝ → ℝ)) (P := LatticeProb.incPathLaw d)
    (P' := gaussianReal 0 (Real.toNNReal ((∑ i, (a i) ^ 2) / d)))
    (by rw [hvar]; exact HasLaw.id) hmem hindep hident
  simpa only [hmean, mul_zero, sub_zero] using h

end Sandpile.External.Stopping
