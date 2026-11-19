import Sandpile.External.Stopping.WalkTimeBlockCLT
import Sandpile.External.Stopping.GaussianBlockCharacteristic

/-!
# Characteristic limits for walk interval increments

Finite sums of projected walk increments on disjoint time intervals have the
characteristic function of a centered Gaussian in the diffusive limit.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Characteristic functions converge for projected increments on disjoint intervals. -/
theorem tendsto_charFun_time_interval_increments
    {ι : Type*} [Fintype ι] (d : ℕ) [NeZero d] (a : ι → Fin d → ℝ)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (s t : ι → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hst : ∀ i, s i < t i)
    (hdisj : ∀ i j, i ≠ j → t i ≤ s j ∨ t j ≤ s i) (u : ℝ) :
    Tendsto (fun n => charFun ((LatticeProb.incPathLaw d).map
      (fun ξ : ℕ → LatticeProb.Site d => ∑ i,
        (R n)⁻¹ * ∑ k ∈ Finset.range (⌊t i * (R n) ^ 2⌋₊ - ⌊s i * (R n) ^ 2⌋₊),
          LatticeProb.dotSite (a i) (ξ (⌊s i * (R n) ^ 2⌋₊ + k)))) u)
      atTop (𝓝 (Complex.exp (-(((∑ i, ((∑ j, (a i j) ^ 2) / d) * (t i - s i) : ℝ)
        : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2))) := by
  have h := tendstoInDistribution_time_interval_blocks d a R hR s t hs hst hdisj
  have hsum := h.continuous_comp (g := fun z : ι → ℝ => ∑ i, z i) (by fun_prop)
  have hchar := hsum.tendsto_charFun u
  have hv (i : ι) : 0 ≤ (∑ j, (a i j) ^ 2) / d := by positivity
  have hvariance : (∑ i, ((Real.toNNReal ((∑ j, (a i j) ^ 2) / d) : ℝ≥0) : ℝ) *
      (Real.sqrt (t i - s i)) ^ 2) =
      ∑ i, ((∑ j, (a i j) ^ 2) / d) * (t i - s i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.coe_toNNReal _ (hv i), Real.sq_sqrt (sub_nonneg.mpr (hst i).le)]
  have hlimit := charFun_weighted_gaussian_blocks
    (fun i => Real.toNNReal ((∑ j, (a i j) ^ 2) / d))
    (fun i => Real.sqrt (t i - s i)) u
  rw [hvariance] at hlimit
  simp only [Function.comp_def] at hchar
  convert hchar using 1
  congr 2
  simpa only [mul_comm] using hlimit.symm

end Sandpile.External.Stopping
