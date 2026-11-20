import Sandpile.External.RSW.UnorientedCorridorCascade
import Sandpile.External.RSW.CorridorContact

/-!
# Unoriented corridor contact

An exceptional path in either traversal direction transfers to its own scale.
Contact with a wall then gives the corresponding bridge cover.
-/

open Set

namespace Sandpile.External.RSW

/-- An unoriented exceptional path can be represented at its own scale. -/
theorem kstUnorientedExceptionalPathEvent_subset_own_scale (n m k : ℕ) :
    kstUnorientedExceptionalPathEvent n m k ⊆ kstUnorientedExceptionalPathEvent m m k := by
  let R := centeredPlaneRectangle (m + m / 12) m
  let S := centeredPlaneRectangle (m + 3 * (m / 12)) m
  have hRS : R ⊆ S := by
    intro z hz
    have h := (mem_centeredPlaneRectangle _ _ z).mp hz
    apply (mem_centeredPlaneRectangle _ _ z).mpr
    push_cast at *
    omega
  let f := rectangleGraphInclusion hRS
  intro ω hω
  obtain ⟨a, b, p, hp, hbad, hbadrev, hopen⟩ := hω
  obtain ⟨ha, hb, q, hq, hqo, hpq⟩ := hp.exists_restrict hopen
  change ((lattice 2).induce
    (centeredPlaneRectangle (n + 3 * (n / 12)) n : Set (Site 2))).Walk a b at p
  change ((lattice 2).induce (R : Set (Site 2))).Walk ⟨a, ha⟩ ⟨b, hb⟩ at q
  change ((lattice 2).induce (R : Set (Site 2))) →g
    ((lattice 2).induce (S : Set (Site 2))) at f
  have heq0 : q.map (SimpleGraph.Embedding.induce (R : Set (Site 2))).toHom =
      (q.map f).map (SimpleGraph.Embedding.induce (S : Set (Site 2))).toHom := by
    rw [SimpleGraph.Walk.map_map]
    rfl
  let w := q.map f
  change ((lattice 2).induce (S : Set (Site 2))).Walk ⟨a, hRS ha⟩ ⟨b, hRS hb⟩ at w
  have heq : q.map (SimpleGraph.Embedding.induce (R : Set (Site 2))).toHom =
      w.map (SimpleGraph.Embedding.induce (S : Set (Site 2))).toHom := heq0
  have hqbad : ¬ HasKSTSubpath k q := by
    intro hs
    exact hbad (hasKSTSubpath_of_eq_ambient_walk p q k hpq.symm hs)
  have hqbadrev : ¬ HasKSTSubpath k q.reverse := by
    intro hs
    apply hbadrev
    apply hasKSTSubpath_of_eq_ambient_walk p.reverse q.reverse k _ hs
    rw [← SimpleGraph.Walk.reverse_map, ← SimpleGraph.Walk.reverse_map]
    exact congrArg SimpleGraph.Walk.reverse hpq.symm
  have hbad' : ¬ HasKSTSubpath k w := by
    intro hs
    exact hqbad (hasKSTSubpath_of_eq_ambient_walk q w k heq hs)
  have hbadrev' : ¬ HasKSTSubpath k w.reverse := by
    intro hs
    apply hqbadrev
    apply hasKSTSubpath_of_eq_ambient_walk q.reverse w.reverse k _ hs
    rw [← SimpleGraph.Walk.reverse_map, ← SimpleGraph.Walk.reverse_map]
    exact congrArg SimpleGraph.Walk.reverse heq
  exact ⟨f ⟨a, ha⟩, f ⟨b, hb⟩, w, hq.map_inclusion hRS, hbad', hbadrev',
    hqo.map_inclusion hRS⟩

/-- An exceptional path in either direction meets one of two attached walls. -/
def KSTUnorientedCorridorIntersects (m k : ℕ) : Prop :=
  let S := centeredPlaneRectangle (m + 3 * (m / 12)) m
  ∀ (a b c d x y e f u v : S)
    (p : (rectangleGraph S).Walk a b) (r : (rectangleGraph S).Walk c d)
    (q : (rectangleGraph S).Walk x y) (r' : (rectangleGraph S).Walk e f)
    (q' : (rectangleGraph S).Walk u v),
    IsKSTPath m p → ¬ HasKSTSubpath k p → ¬ HasKSTSubpath k p.reverse →
    IsKSTPath k r → x ∈ r.support →
    (y : Site 2) 0 = -((m + 3 * (m / 12) : ℕ) : ℤ) →
    IsKSTPath k r' → u ∈ r'.support →
    (v : Site 2) 0 = ((m + 3 * (m / 12) : ℕ) : ℤ) →
    (∃ z, z ∈ p.support ∧ (z ∈ r.support ∨ z ∈ q.support)) ∨
      ∃ z, z ∈ p.support ∧ (z ∈ r'.support ∨ z ∈ q'.support)

/-- Unoriented corridor contact gives the corresponding translated bridge cover. -/
theorem kstUnorientedCorridorBridgeCover_of_intersects (n m k : ℕ) (hm : 0 < m)
    (hgeom : KSTUnorientedCorridorIntersects m k) :
    KSTUnorientedCorridorBridgeCover n m k := by
  intro ω hω
  have hex := kstUnorientedExceptionalPathEvent_subset_own_scale n m k hω.1
  obtain ⟨a, b, p, hp, hbad, hbadrev, hpo⟩ := hex
  obtain ⟨c, d, x, y, r, q, hr, hx, hy, hro, hqo⟩ := hω.2.1
  obtain ⟨e, f, u, v, r', q', hr', hu, hv, hr'o, hq'o⟩ := hω.2.2
  have hcontact := hgeom a b c d x y e f u v p r q r' q' hp hbad hbadrev hr hx
    (by simpa only [Bool.true_eq, ↓reduceIte] using hy) hr' hu
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using hv)
  rcases hcontact with hleft | hright
  · exact Or.inl (kstWallEvent_left_subset_translated_bridge m hm
      (kstWallEvent_of_contact m true p r q hp hpo hx hro hqo hy hleft))
  · exact Or.inr (kstWallEvent_right_subset_translated_bridge m hm
      (kstWallEvent_of_contact m false p r' q' hp hpo hu hr'o hq'o hv hright))

end Sandpile.External.RSW
