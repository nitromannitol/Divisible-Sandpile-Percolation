import LatticeProb.Analysis.Sobolev.TestFnCutoff

/-!
# A compact cutoff for a bounded domain

A bounded domain has a smooth, compactly supported function equal to one on
its closure.
-/

namespace Sandpile.Support

open LatticeProb.Sobolev

/-- A bounded domain admits a compactly supported smooth cutoff equal to one
on the domain. -/
theorem exists_testFn_eq_one_on_domain {d : ℕ} {D : Set (Space d)} (hD : IsDomain D) :
    ∃ χ : Space d → ℝ, IsTestFn Set.univ χ ∧ ∀ z ∈ D, χ z = 1 := by
  obtain ⟨r, hr, hsub⟩ := hD.2.1.closure.subset_ball_lt 0 (0 : Space d)
  have hball : IsDomain (Metric.ball (0 : Space d) r) := by
    refine ⟨Metric.isOpen_ball, Metric.isBounded_ball, ⟨0, ?_⟩⟩
    simpa using hr
  obtain ⟨χ, hχ, _, hone⟩ := exists_isTestFn_eqOn_one' hball hD.2.1.isCompact_closure hsub
  refine ⟨χ, ⟨hχ.1, hχ.2.1, Set.subset_univ _⟩, ?_⟩
  intro z hz
  exact hone (subset_closure hz)

end Sandpile.Support
