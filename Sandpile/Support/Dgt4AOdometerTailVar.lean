import Sandpile.Support.Dgt4AOdometerTailMoment

/-!
# Variance decay of the iterated odometer average

The variance of `P^ju_n(0)` decays like `j^{(4-d)/2}`, uniformly in `n`: the square sum of
the tail kernel is `O(j^{(4-d)/2})` (`eq:dgt4-tail-kernel`, `sandpile.tex:1303-1306`), and
the product moment bound at `p=2` turns that into the variance.
-/

open LatticeProb

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `\Var(P^ju_n(0))\leq Cj^{(4-d)/2}`, uniformly in `n` (`sandpile.tex:5058-5066`). -/
theorem exists_integral_avgIterate_odometerOf_sq_le
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hmom : Integrable (fun z : ℝ => |z| ^ (2 : ℝ)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n j : ℕ, 1 ≤ j →
      (∫ ζ, |(avg^[j] (fun y => odometerOf ζ n y)) 0
          - ∫ η, (avg^[j] (fun y => odometerOf η n y)) 0 ∂(LatticeProb.iidLaw d ν)| ^ (2 : ℝ)
          ∂(LatticeProb.iidLaw d ν))
        ≤ C * pairMoment ν 2 * (j : ℝ) ^ ((4 - (d : ℝ)) / 2) := by
  obtain ⟨C0, hC0, h0⟩ := Sandpile.exists_integral_avgIterate_odometerOf_moment_le hGH hd ν
    (p := (2 : ℝ)) le_rfl hmom
  obtain ⟨Ct, hCt, htail⟩ := (hGH d hd).2.2.1
  refine ⟨C0 * Ct, mul_pos hC0 hCt, fun n j hj => ?_⟩
  have h1 := h0 n j hj
  have hpow : (∑' z : Site d, Sandpile.External.tailKernel d j z ^ 2) ^ ((2 : ℝ) / 2)
      = ∑' z : Site d, Sandpile.External.tailKernel d j z ^ 2 := by
    rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  rw [hpow] at h1
  have h2 : (∑' z : Site d, Sandpile.External.tailKernel d j z ^ 2)
      ≤ Ct * (j : ℝ) ^ ((4 - (d : ℝ)) / 2) := (htail j hj).2.2
  have hm0 : 0 ≤ LatticeProb.pairMoment ν 2 := LatticeProb.pairMoment_nonneg ν 2
  have h3 : C0 * LatticeProb.pairMoment ν 2
      * (∑' z : Site d, Sandpile.External.tailKernel d j z ^ 2)
      ≤ C0 * Ct * LatticeProb.pairMoment ν 2 * (j : ℝ) ^ ((4 - (d : ℝ)) / 2) := by
    have hcm : 0 ≤ C0 * LatticeProb.pairMoment ν 2 := mul_nonneg hC0.le hm0
    nlinarith [mul_le_mul_of_nonneg_left h2 hcm]
  exact h1.trans h3

end Sandpile
