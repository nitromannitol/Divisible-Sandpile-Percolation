import Sandpile.External.Stopping.WalkBrownianVectorIntervals

/-!
# Cumulative limits for walk increments

Joint convergence of disjoint interval increments is preserved by finite
cumulative sums. This is the continuous mapping step in reconstructing
finite-dimensional positions from successive increments.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Cumulative sums of disjoint walk increments converge to the corresponding
cumulative sums of Brownian increments. -/
theorem tendstoInDistribution_walk_brownian_cumulative_intervals
    {d m : ℕ} [NeZero d] (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (s t : Fin m → ℝ≥0) (hst : ∀ i, s i < t i)
    (hdisj : ∀ i j, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    TendstoInDistribution
      (fun n (ξ : ℕ → LatticeProb.Site d) (p : Fin (m + 1) × Fin d) =>
        ∑ i : Fin m, if i.val < p.1.val then
          (R n)⁻¹ * ∑ k ∈ Finset.range (⌊(t i : ℝ) * (R n) ^ 2⌋₊ -
            ⌊(s i : ℝ) * (R n) ^ 2⌋₊),
            ((ξ (⌊(s i : ℝ) * (R n) ^ 2⌋₊ + k) p.2 : ℤ) : ℝ)
        else 0)
      atTop (fun ω (p : Fin (m + 1) × Fin d) =>
        ∑ i : Fin m, if i.val < p.1.val then B (t i) ω p.2 - B (s i) ω p.2 else 0)
      (fun _ => LatticeProb.incPathLaw d) P := by
  let F : (Fin m × Fin d → ℝ) → (Fin (m + 1) × Fin d → ℝ) := fun z p =>
    ∑ i : Fin m, if i.val < p.1.val then z (i, p.2) else 0
  have hF : Continuous F := by
    apply continuous_pi
    intro p
    apply continuous_finset_sum
    intro i _
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  have h := (tendstoInDistribution_walk_brownian_vector_intervals R hR s t hst hdisj P B hB)
    |>.continuous_comp hF
  simpa only [F, Function.comp_def] using h

end Sandpile.External.Stopping
