import LatticeProb.Prob.BrownianOpenExit
import Mathlib

/-!
# Identification of a regular exit time

A time with the defining before-and-after properties of a first exit agrees
with the infimum-based open exit time. This pathwise fact applies even when the
path or the set has no topological regularity.
-/

open Filter Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- If a path stays in a set before `τ` and leaves it before every time after
`τ`, then its first exit time is `τ`. -/
theorem openExitTime_eq_of_regular {Ω E : Type*} (X : ℝ≥0 → Ω → E)
    (U : Set E) (ω : Ω) (τ : ℝ≥0)
    (hbefore : ∀ s < τ, X s ω ∈ U)
    (hafter : ∀ t > τ, ∃ s < t, X s ω ∉ U) :
    LatticeProb.openExitTime X U ω = (τ : ℝ≥0∞) := by
  have hle (t : ℝ≥0) (ht : τ < t) : LatticeProb.openExitTime X U ω ≤ t := by
    obtain ⟨s, hs, hout⟩ := hafter t ht
    exact (LatticeProb.openExitTime_le_of_not_mem hout).trans (by exact_mod_cast hs.le)
  have hfin : LatticeProb.openExitTime X U ω ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (hle (τ + 1) (lt_add_of_pos_right τ zero_lt_one))
  apply le_antisymm
  · rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe]
    apply le_of_forall_gt_imp_ge_of_dense
    intro t ht
    have h := hle t ht
    rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe] at h
    exact h
  · apply le_iInf
    rintro ⟨s, hs⟩
    apply ENNReal.coe_le_coe.2
    exact le_of_not_gt (fun h => hs (hbefore s h))

end Sandpile.External.Stopping
