import Sandpile.External.RSW.KSTPathInclusion
import Sandpile.External.RSW.BondWalk

/-!
# Restricting KST paths

A KST path in any finite ambient rectangle can be regarded as a path in its own
scale rectangle, without changing its vertices or edges.
-/

open Set

namespace Sandpile.External.RSW

/-- Restrict a KST path to its scale rectangle while preserving its ambient walk. -/
theorem IsKSTPath.exists_restrict {Q : Finset (Site 2)} {a b : Q}
    {p : (rectangleGraph Q).Walk a b} {m : ℕ} (hp : IsKSTPath m p)
    {ω : Sym2 (Site 2) → Bool} (hopen : IsBondOpenWalk ω p) :
    ∃ (ha : (a : Site 2) ∈ centeredPlaneRectangle (m + m / 12) m)
      (hb : (b : Site 2) ∈ centeredPlaneRectangle (m + m / 12) m)
      (q : (rectangleGraph (centeredPlaneRectangle (m + m / 12) m)).Walk ⟨a, ha⟩ ⟨b, hb⟩),
      IsKSTPath m q ∧ IsBondOpenWalk ω q ∧
      q.map (SimpleGraph.Embedding.induce
        (centeredPlaneRectangle (m + m / 12) m : Set (Site 2))).toHom =
      p.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom := by
  change ((lattice 2).induce (Q : Set (Site 2))).Walk a b at p
  let R := centeredPlaneRectangle (m + m / 12) m
  let P := p.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom
  have hP : ∀ z ∈ P.support, z ∈ (R : Set (Site 2)) := by
    intro z hz
    change z ∈ (p.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact hp.2.2.2.2.2.2.2 x hx
  let q := P.induce (R : Set (Site 2)) hP
  have hq : q.map (SimpleGraph.Embedding.induce (R : Set (Site 2))).toHom = P := by
    exact SimpleGraph.Walk.map_induce P hP
  refine ⟨hP _ P.start_mem_support, hP _ P.end_mem_support, q, ?_, ?_, hq⟩
  · have hpath : P.IsPath := hp.1.map Subtype.val_injective
    have hqpath : q.IsPath := by
      have hh : (q.map (SimpleGraph.Embedding.induce (R : Set (Site 2))).toHom).IsPath := by
        rw [hq]
        exact hpath
      exact hh.of_map
    refine ⟨hqpath, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
      hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, ?_⟩
    intro z _
    exact z.property
  · apply (isBondOpenWalk_iff_edges ω q).mpr
    intro e he
    rw [hq] at he
    exact (isBondOpenWalk_iff_edges ω p).mp hopen e he

end Sandpile.External.RSW
