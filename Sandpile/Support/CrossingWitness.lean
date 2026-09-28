import Sandpile.Support.RectangleBottleneck

/-!
# Attainment of the rectangle crossing value by walks

Attainment of rectangle crossing values by simple paths and their exact walk characterization.
`crossingValue_spec` shows the supremum defining `crossingValue Q F` is an actual maximum,
attained by a simple path of `rectangleGraph Q` from the left side to the right side of `Q`, by
transporting the abstract definition through `crossingValue_eq_bounded_max` to the finite,
length-bounded `boundedBottleneckValue` recursion of `RectangleBottleneck.lean`.
`le_crossingValue_of_walk` and `le_crossingValue_iff_exists_walk` restate this as the
walk-theoretic characterization used throughout: a level is at most `crossingValue Q F` exactly
when some left-right walk keeps `F` at or above that level on every vertex it visits.
-/

noncomputable section
namespace Sandpile

/-- **The crossing value is attained.** Every left-right walk's bottleneck is at most
`crossingValue Q F`, and this bound is achieved with equality by some simple left-right path,
obtained by transporting the finite maximizer of `boundedBottleneckValue` (via
`crossingValue_eq_bounded_max`) back to a walk and taking its `bypass` to make it a path. -/
lemma crossingValue_spec {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    (hN : Q.Nonempty) (F : Q → ℝ) :
    (∀ (a b : Q) (p : (rectangleGraph Q).Walk a b),
      a ∈ rectangleLeft Q → b ∈ rectangleRight Q → walkBottleneck p F ≤ crossingValue Q F) ∧
    ∃ (a b : Q) (p : (rectangleGraph Q).Walk a b), p.IsPath ∧
      a ∈ rectangleLeft Q ∧ b ∈ rectangleRight Q ∧ walkBottleneck p F = crossingValue Q F := by
  classical
  obtain ⟨hleft, hright⟩ := rectangle_boundaries_nonempty hQ hN
  letI : Nonempty (rectangleLeft Q) := ⟨⟨hleft.choose, hleft.choose_spec⟩⟩
  letI : Nonempty (rectangleRight Q) := ⟨⟨hright.choose, hright.choose_spec⟩⟩
  have hn : Q.card ≤ 2 ^ Q.card := Q.card.lt_two_pow_self.le
  let f (c : rectangleLeft Q × rectangleRight Q) :=
    boundedBottleneckValue (rectangleGraph Q) Q.card c.1 c.2
      (rectangle_boundedReach hQ hn c.1 c.2) F
  have he : crossingValue Q F = finiteMaximum f := crossingValue_eq_bounded_max hQ hn F
  have hu (a b : Q) (p : (rectangleGraph Q).Walk a b)
      (ha : a ∈ rectangleLeft Q) (hb : b ∈ rectangleRight Q) :
      walkBottleneck p F ≤ crossingValue Q F := by
    have hlen : p.bypass.length ≤ 2 ^ Q.card :=
      (by simpa using p.bypass_isPath.length_lt.le : p.bypass.length ≤ Q.card).trans hn
    have hh := (boundedBottleneckValue_spec (rectangleGraph Q) Q.card a b
      (rectangle_boundedReach hQ hn a b) F).1 p.bypass hlen
    rw [he]
    exact (walkBottleneck_le_bypass p F).trans (hh.trans
      (le_finiteMaximum f (⟨a, ha⟩, ⟨b, hb⟩)))
  refine ⟨hu, ?_⟩
  obtain ⟨c, hc⟩ := finiteMaximum_mem f
  obtain ⟨p, _, hp⟩ := (boundedBottleneckValue_spec (rectangleGraph Q) Q.card c.1 c.2
    (rectangle_boundedReach hQ hn c.1 c.2) F).2
  refine ⟨c.1, c.2, p.bypass, p.bypass_isPath, c.1.property, c.2.property,
    le_antisymm (hu _ _ _ c.1.property c.2.property) ?_⟩
  rw [he, hc]
  change boundedBottleneckValue (rectangleGraph Q) Q.card c.1 c.2
    (rectangle_boundedReach hQ hn c.1 c.2) F ≤ walkBottleneck p.bypass F
  rw [← hp]
  exact walkBottleneck_le_bypass p F

/-- If a left-right walk of `rectangleGraph Q` keeps `F` at or above `level` on its whole
support, then `level ≤ crossingValue Q F`: combines the bottleneck characterization
`le_walkBottleneck_iff` with the upper bound half of `crossingValue_spec`. -/
lemma le_crossingValue_of_walk {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    {F : Q → ℝ} {a b : Q} (p : (rectangleGraph Q).Walk a b)
    (ha : a ∈ rectangleLeft Q) (hb : b ∈ rectangleRight Q) {level : ℝ}
    (hp : ∀ z ∈ p.support, level ≤ F z) : level ≤ crossingValue Q F := by
  exact ((le_walkBottleneck_iff p F level).mpr hp).trans
    ((crossingValue_spec hQ ⟨a, a.property⟩ F).1 a b p ha hb)

/-- **Walk characterization of the crossing value.** `level ≤ crossingValue Q F` exactly when
some left-right walk of `rectangleGraph Q` keeps `F` at or above `level` throughout its support:
the forward direction reads off the witnessing path of `crossingValue_spec`, the converse is
`le_crossingValue_of_walk`. -/
lemma le_crossingValue_iff_exists_walk {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    (hN : Q.Nonempty) (F : Q → ℝ) (level : ℝ) :
    level ≤ crossingValue Q F ↔ ∃ (a b : Q) (p : (rectangleGraph Q).Walk a b),
      a ∈ rectangleLeft Q ∧ b ∈ rectangleRight Q ∧ ∀ z ∈ p.support, level ≤ F z := by
  constructor
  · intro hl
    obtain ⟨a, b, p, _, ha, hb, hp⟩ := (crossingValue_spec hQ hN F).2
    refine ⟨a, b, p, ha, hb, ?_⟩
    apply (le_walkBottleneck_iff p F level).mp
    rwa [hp]
  · rintro ⟨a, b, p, ha, hb, hp⟩
    exact le_crossingValue_of_walk hQ p ha hb hp

end Sandpile
