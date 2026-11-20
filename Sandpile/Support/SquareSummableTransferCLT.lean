import Sandpile.Support.SquareSummableCLT
import Sandpile.Support.SquareSummableDefect

/-!
# Central limit theorem under square-summable perturbations

For finite weighted rows, a perturbation vanishing in `ℓ²` transfers the
small-coefficient and variance hypotheses from a square-summable reference
row. The weighted independent-row central limit theorem then applies directly.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped lp ENNReal

namespace Sandpile.Support

/-- The squared norm of an `ℓ²` vector supported on a finite set is the sum of
its squared coordinates on that set. -/
theorem finset_sum_sq_eq_norm_sq {ι : Type*} (v : ℓ²(ι, ℝ)) (s : Finset ι)
    (hs : ∀ i ∉ s, v i = 0) : (∑ i ∈ s, v i ^ 2) = ‖v‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) v
  have heq : (∑' i, v i ^ 2) = ∑ i ∈ s, v i ^ 2 := by
    exact tsum_eq_sum (fun i hi => by rw [hs i hi, zero_pow (by decide : 2 ≠ 0)])
  simpa only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs, heq] using h.symm

/-- A finite weighted row has the same Gaussian limit as a square-summable
reference row when their squared difference has extended sum tending to zero. -/
theorem tendstoInDistribution_linear_of_sq_defect
    {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (a b : ℝ → ℓ²(Sandpile.Site d, ℝ)) (s : ℝ → Finset (Sandpile.Site d))
    (hs : ∀ R x, x ∉ s R → a R x = 0)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, ∀ x, |b R x| ≤ δ)
    (B : ℝ) (hB : Tendsto (fun R => ‖b R‖) atTop (𝓝 B))
    (hdefect : Tendsto (fun R => ∑' x, ENNReal.ofReal ((a R x - b R x) ^ 2))
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (R : ℝ) (ζ : Sandpile.Site d → ℝ) => ∑ x ∈ s R, a R x * ζ x)
      atTop (id : ℝ → ℝ) (fun _ => LatticeProb.iidLaw d ν)
      (gaussianReal 0 (Real.toNNReal ((∫ z, z ^ 2 ∂ν) * B ^ 2))) := by
  have hsub : Tendsto (fun R => ‖a R - b R‖) atTop (𝓝 0) := by
    apply tendsto_norm_zero_of_tsum_ofReal_sq_tendsto_zero atTop (fun R => a R - b R)
    simpa only [lp.coeFn_sub, Pi.sub_apply] using hdefect
  have ha := tendsto_norm_of_sub_norm_tendsto_zero atTop a b B hB hsub
  have hasmall := eventually_coordinate_bound_of_sub_norm_tendsto_zero atTop a b hsmall hsub
  have hmass : Tendsto (fun R => ∑ x ∈ s R, a R x ^ 2) atTop (𝓝 (B ^ 2)) := by
    have heq : (fun R => ∑ x ∈ s R, a R x ^ 2) = (fun R => ‖a R‖ ^ 2) := by
      funext R
      exact finset_sum_sq_eq_norm_sq (a R) (s R) (hs R)
    rw [heq]
    exact ha.pow 2
  have hclt := tendstoInDistribution_linear_pick ν hsq hmean (fun R => (s R).card)
    (fun R i => a R (Sandpile.siteEnum (s R) i))
    (fun R => Sandpile.siteEnum (s R)) (fun R => Sandpile.siteEnum_injective (s R))
    (fun δ hδ => (hasmall δ hδ).mono fun _ h i => h _) (B ^ 2) ?_
  · convert hclt using 1
    funext R ζ
    exact (Sandpile.sum_siteEnum (s R) (fun x => a R x * ζ x)).symm
  · convert hmass using 1
    funext R
    exact Sandpile.sum_siteEnum (s R) (fun x => a R x ^ 2)

end Sandpile.Support
