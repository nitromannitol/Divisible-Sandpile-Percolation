import LatticeProb.Prob.BrownianFirstPassageStrict

/-!
# Brownian motion crosses its level at the first hit

A one-dimensional Brownian path hits a fixed level in finite time and crosses
it strictly at arbitrarily nearby later times. This is the coordinatewise
regularity needed for exits from cubes. The strict-passage theorem used here
is proved in `LatticeProb.Prob.BrownianFirstPassageStrict` using the strong
Markov property and Blumenthal's zero-one law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A real Brownian path hits `-a` in finite time, stays above it before the
hit, and goes strictly below it before any later time. -/
theorem ae_brownian_level_regular {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) (a : ℝ) :
    ∀ᵐ ω ∂P,
      let τ := LatticeProb.hitDrift (fun t ω => -B t ω) 0 a ω
      τ < ⊤ ∧
        (∀ s : ℝ≥0, s < τ.toNNReal → -a < B s ω) ∧
        (∀ t : ℝ≥0, τ.toNNReal < t → ∃ s : ℝ≥0, s < t ∧ B s ω < -a) := by
  filter_upwards [LatticeProb.LadderSet.ae_firstPassageBelow_eq_hitDrift hB hm hc a,
    hB.eval_zero_ae_eq_zero] with ω hω h0
  dsimp only
  let τ := LatticeProb.hitDrift (fun t ω => -B t ω) 0 a ω
  have hfin : τ < ⊤ := hω.1
  refine ⟨hfin, ?_, ?_⟩
  · intro s hs
    by_contra hn
    have hhit : τ ≤ (s : ℝ≥0∞) := by
      apply (LatticeProb.hitDrift_le_iff (fun ω => (hc ω).neg) 0 a ω s).2
      refine ⟨s, le_rfl, ?_⟩
      change a ≤ -B s ω + 0 * (s : ℝ)
      linarith
    rw [← ENNReal.coe_toNNReal hfin.ne, ENNReal.coe_le_coe] at hhit
    exact (not_le_of_gt hs) hhit
  · intro t ht
    have heq : LatticeProb.LadderSet.firstPassageBelow
        (LatticeProb.LadderSet.nnExtend fun t => B t ω) 0 a = (τ.toNNReal : ℝ) := by
      rw [hω.2.1]
      rfl
    have hlt : LatticeProb.LadderSet.firstPassageBelow
        (LatticeProb.LadderSet.nnExtend fun t => B t ω) 0 a < (t : ℝ) := by
      rw [heq]
      exact_mod_cast ht
    rw [LatticeProb.LadderSet.firstPassageBelow] at hlt
    obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt
      (show {s : ℝ | 0 ≤ s ∧ LatticeProb.LadderSet.nnExtend (fun t => B t ω) s <
        LatticeProb.LadderSet.nnExtend (fun t => B t ω) 0 - a}.Nonempty from hω.2.2) hlt
    refine ⟨s.toNNReal, ?_, ?_⟩
    · exact (Real.toNNReal_lt_iff_lt_coe hs.1).2 hst
    · simpa only [LatticeProb.LadderSet.nnExtend, Real.toNNReal_zero, h0, zero_sub] using hs.2

end Sandpile.External.Stopping
