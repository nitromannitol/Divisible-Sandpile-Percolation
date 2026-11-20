import Sandpile.External.Stopping.StepWalkJointMeasurable

/-!
# Right-continuity of diffusive step walks

The floor-time walk is constant on a right neighborhood of every time.
-/

open Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- A diffusive step walk is right-continuous at every time and on every path. -/
theorem continuousWithinAt_diffusiveStepWalk {d : ℕ} (R : ℝ)
    (X : ℕ → Site d) (t : ℝ≥0) :
    ContinuousWithinAt (fun s => diffusiveStepWalk R s X) (Set.Ici t) t := by
  have hupper : ∀ᶠ s : ℝ≥0 in 𝓝 t,
      R ^ 2 * (s : ℝ) < (⌊R ^ 2 * (t : ℝ)⌋₊ : ℝ) + 1 := by
    have hcont : Continuous (fun s : ℝ≥0 => R ^ 2 * (s : ℝ)) :=
      continuous_const.mul continuous_subtype_val
    exact hcont.continuousAt.eventually (eventually_lt_nhds (Nat.lt_floor_add_one _))
  have heq : (fun s => diffusiveStepWalk R s X) =ᶠ[𝓝[Set.Ici t] t]
      (fun _ => diffusiveStepWalk R t X) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hupper] with s hs hu
    have hindex : diffusiveTimeIndex R s = diffusiveTimeIndex R t := by
      apply (Nat.floor_eq_iff (mul_nonneg (sq_nonneg R) s.property)).2
      constructor
      · exact (Nat.floor_le (mul_nonneg (sq_nonneg R) t.property)).trans
          (mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ s from hs) (sq_nonneg R))
      · exact hu
    rw [diffusiveStepWalk_eq_at_index, diffusiveStepWalk_eq_at_index, hindex]
  exact continuousWithinAt_const.congr_of_eventuallyEq_of_mem heq (Set.mem_Ici.mpr le_rfl)

end Sandpile.External.Stopping
