import Sandpile.Support.BallCrossingDefinitions

/-!
# Measurability of the ball Green field and the star-crossing event

This file proves the measurability facts of `sandpile.tex:3551-3557` needed to make sense of
probabilities over the ball Green field. The field itself is a countable sum of measurable
coordinate functions, and the blocking `∗`-crossing event is rewritten as the countable union,
over the lists of sites that are admissible crossings of the rectangle, of the event that the
field is below the given level on every site of the list, which is a countable Boolean
combination of measurable sets.
-/

open MeasureTheory

noncomputable section
namespace Sandpile

/-- The ball Green field `ballGreenField R · z`, as a function of the underlying scenery, is
measurable: it is a series of constant multiples of coordinate projections. -/
lemma measurable_ballGreenField (R : ℕ) (z : Site 4) :
    Measurable (fun ζ : Site 4 → ℝ => ballGreenField R ζ z) := by
  unfold ballGreenField
  refine Measurable.tsum fun u => ?_
  exact (measurable_pi_apply (z + u)).const_mul _

/-- The blocking `∗`-crossing event `HasStarTopBottomCrossing ϑ r x {w | ballGreenField R η w
≤ level}` is measurable in `η`: it is rewritten as a countable union over lists of sites of
the intersection, over the sites of the list, of the measurable sets `ballGreenField R η z ≤
level`. -/
lemma measurableSet_star_crossing (ϑ : ℝ) (r R : ℕ) (x : Site 4) (level : ℝ) :
    MeasurableSet {η : Site 4 → ℝ |
      HasStarTopBottomCrossing ϑ r x {w | ballGreenField R η w ≤ level}} := by
  classical
  have hset : {η : Site 4 → ℝ |
      HasStarTopBottomCrossing ϑ r x {w | ballGreenField R η w ≤ level}}
      = ⋃ Γ : List (Site 4),
          (if Γ ≠ [] ∧ (∀ z ∈ Γ, z ∈ ballRect ϑ r x) ∧ List.IsChain starGraph.Adj Γ ∧
              (∀ z ∈ Γ.head?, z 1 = x 1 + (r : ℤ)) ∧ (∀ z ∈ Γ.getLast?, z 1 = x 1)
            then {η : Site 4 → ℝ | ∀ z ∈ Γ, ballGreenField R η z ≤ level}
            else (∅ : Set (Site 4 → ℝ))) := by
    ext η
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨Γ, hΓ, hmem, hchain, hhead, hlast⟩
      refine ⟨Γ, ?_⟩
      rw [if_pos ⟨hΓ, fun z hz => (hmem z hz).2, hchain, hhead, hlast⟩]
      exact fun z hz => (hmem z hz).1
    · rintro ⟨Γ, hΓ⟩
      by_cases hc : Γ ≠ [] ∧ (∀ z ∈ Γ, z ∈ ballRect ϑ r x) ∧ List.IsChain starGraph.Adj Γ ∧
          (∀ z ∈ Γ.head?, z 1 = x 1 + (r : ℤ)) ∧ (∀ z ∈ Γ.getLast?, z 1 = x 1)
      · rw [if_pos hc] at hΓ
        exact ⟨Γ, hc.1, fun z hz => ⟨hΓ z hz, hc.2.1 z hz⟩, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩
      · rw [if_neg hc] at hΓ
        exact absurd hΓ (Set.notMem_empty η)
  rw [hset]
  refine MeasurableSet.iUnion fun Γ => ?_
  by_cases hc : Γ ≠ [] ∧ (∀ z ∈ Γ, z ∈ ballRect ϑ r x) ∧ List.IsChain starGraph.Adj Γ ∧
      (∀ z ∈ Γ.head?, z 1 = x 1 + (r : ℤ)) ∧ (∀ z ∈ Γ.getLast?, z 1 = x 1)
  · rw [if_pos hc]
    have he : {η : Site 4 → ℝ | ∀ z ∈ Γ, ballGreenField R η z ≤ level}
        = ⋂ z ∈ {w : Site 4 | w ∈ Γ}, {η : Site 4 → ℝ | ballGreenField R η z ≤ level} := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [he]
    refine MeasurableSet.biInter (Set.to_countable _) fun z _ => ?_
    exact measurableSet_le (measurable_ballGreenField R z) measurable_const
  · rw [if_neg hc]
    exact MeasurableSet.empty

end Sandpile
