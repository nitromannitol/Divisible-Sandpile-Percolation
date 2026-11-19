import Sandpile.External.Stopping.WalkBrownianIntervalConvergence
import Sandpile.External.Stopping.FiniteCramerWold

/-!
# Joint vector limits for walk increments on time intervals

The joint projected-increment limit implies convergence of all coordinates of
the increments on a finite family of disjoint positive intervals.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Vector-valued walk increments converge jointly to Brownian increments. -/
theorem tendstoInDistribution_walk_brownian_vector_intervals
    {d m : ℕ} [NeZero d] (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (s t : Fin m → ℝ≥0) (hst : ∀ i, s i < t i)
    (hdisj : ∀ i j, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    TendstoInDistribution
      (fun n (ξ : ℕ → LatticeProb.Site d) (p : Fin m × Fin d) =>
        (R n)⁻¹ * ∑ k ∈ Finset.range (⌊(t p.1 : ℝ) * (R n) ^ 2⌋₊ -
          ⌊(s p.1 : ℝ) * (R n) ^ 2⌋₊),
          ((ξ (⌊(s p.1 : ℝ) * (R n) ^ 2⌋₊ + k) p.2 : ℤ) : ℝ))
      atTop (fun ω (p : Fin m × Fin d) => B (t p.1) ω p.2 - B (s p.1) ω p.2)
      (fun _ => LatticeProb.incPathLaw d) P := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  let X : ℕ → (ℕ → LatticeProb.Site d) → (Fin m × Fin d → ℝ) := fun n ξ p =>
    (R n)⁻¹ * ∑ k ∈ Finset.range (⌊(t p.1 : ℝ) * (R n) ^ 2⌋₊ -
      ⌊(s p.1 : ℝ) * (R n) ^ 2⌋₊),
      ((ξ (⌊(s p.1 : ℝ) * (R n) ^ 2⌋₊ + k) p.2 : ℤ) : ℝ)
  let Y : Ω → (Fin m × Fin d → ℝ) := fun ω p => B (t p.1) ω p.2 - B (s p.1) ω p.2
  have hX (n : ℕ) : AEMeasurable (X n) (LatticeProb.incPathLaw d) := by
    apply Measurable.aemeasurable
    apply Measurable.of_eval
    intro p
    dsimp [X]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro k _
    exact (measurable_of_countable (fun z : LatticeProb.Site d => (z p.2 : ℝ))).comp
      (measurable_pi_apply _)
  have hY : AEMeasurable Y P := by
    apply AEMeasurable.of_eval
    intro p
    exact (LatticeProb.Scaling.WalkCLT.aemeasurable_isBrownianSpace_coord hd hB (t p.1) p.2).sub
      (LatticeProb.Scaling.WalkCLT.aemeasurable_isBrownianSpace_coord hd hB (s p.1) p.2)
  apply tendstoInDistribution_fintype_of_forall_dot X Y (LatticeProb.incPathLaw d) P hX hY
  intro c
  let a : Fin m → Fin d → ℝ := fun i ℓ => c (i, ℓ)
  have h := tendstoInDistribution_walk_brownian_interval_increments a R hR s t hst hdisj P B hB
  have hsum := h.continuous_comp (g := fun z : Fin m → ℝ => ∑ i, z i) (by fun_prop)
  refine hsum.congr (fun n => Filter.Eventually.of_forall fun ξ => ?_)
    (Filter.Eventually.of_forall fun ω => ?_)
  · simp only [Function.comp_def, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [X, a, LatticeProb.dotSite]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ℓ _
    ring
  · simp only [Function.comp_def, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro ℓ _
    dsimp [Y, a]
    ring

end Sandpile.External.Stopping
