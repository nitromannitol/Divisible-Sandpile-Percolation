import Sandpile.External.RSW.KSTSubpathRestriction
import Sandpile.External.RSW.WallToBridge

/-!
# Restricting exceptional paths

An exceptional path can be represented in the quasi-crossing rectangle at its own
scale, retaining its openness and the absence of a smaller KST subpath.
-/

open Set

namespace Sandpile.External.RSW

/-- The exceptional path event does not depend on enlarging its ambient rectangle. -/
theorem kstExceptionalPathEvent_subset_own_scale (n m k : ℕ) :
    kstExceptionalPathEvent n m k ⊆ kstExceptionalPathEvent m m k := by
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
  obtain ⟨a, b, p, hp, hbad, hopen⟩ := hω
  obtain ⟨ha, hb, q, hq, hqo, hqbad⟩ := hp.exists_restrict_without_subpath hopen hbad
  change ((lattice 2).induce (R : Set (Site 2))).Walk ⟨a, ha⟩ ⟨b, hb⟩ at q
  change ((lattice 2).induce (R : Set (Site 2))) →g
    ((lattice 2).induce (S : Set (Site 2))) at f
  have heq : q.map (SimpleGraph.Embedding.induce (R : Set (Site 2))).toHom =
      (q.map f).map (SimpleGraph.Embedding.induce (S : Set (Site 2))).toHom := by
    rw [SimpleGraph.Walk.map_map]
    rfl
  have hbad' : ¬ HasKSTSubpath k (q.map f) := by
    intro hs
    exact hqbad (hasKSTSubpath_of_eq_ambient_walk q (q.map f) k heq hs)
  exact ⟨f ⟨a, ha⟩, f ⟨b, hb⟩, q.map f, hq.map_inclusion hRS, hbad',
    hqo.map_inclusion hRS⟩

/-- It suffices to establish the corridor wall inclusion in the intermediate rectangle. -/
theorem kstCorridorBridgeCover_of_own_scale_wall_cover (n m k : ℕ) (hm : 0 < m)
    (h : kstExceptionalPathEvent m m k ∩ kstQuasiCrossingEvent m k ⊆
      kstWallEvent m m true ∪ kstWallEvent m m false) :
    KSTCorridorBridgeCover n m k := by
  apply kstCorridorBridgeCover_of_wall_cover n m k hm
  intro ω hω
  exact h ⟨kstExceptionalPathEvent_subset_own_scale n m k hω.1, hω.2⟩

end Sandpile.External.RSW
