import Sandpile.External.RSW.HorizontalStripSubpath
import Sandpile.External.RSW.BondWalk
import Sandpile.External.RSW.RefinedRectangleAvoidance

/-!
# Horizontal paths in an embedded rectangle

An open horizontal walk spanning a centered subrectangle contains a simple
open crossing of that subrectangle whose vertices belong to the original walk.
-/

namespace Sandpile.External.RSW

/-- Restrict a spanning open walk to a simple crossing of a centered subrectangle. -/
theorem exists_open_path_in_embedded_rectangle {W H M : ℕ} (hM : 0 < M)
    {ω : Sym2 (Site 2) → Bool} {a b : centeredPlaneRectangle W H}
    (p : (rectangleGraph (centeredPlaneRectangle W H)).Walk a b)
    (hp : IsBondOpenWalk ω p) (ha : (a : Site 2) 0 ≤ -(M : ℤ))
    (hb : (M : ℤ) ≤ (b : Site 2) 0) :
    ∃ (c d : centeredPlaneRectangle M H)
      (q : (rectangleGraph (centeredPlaneRectangle M H)).Walk c d),
      q.IsPath ∧ IsBondOpenWalk ω q ∧ (c : Site 2) 0 = -(M : ℤ) ∧
      (d : Site 2) 0 = M ∧
      ∀ z ∈ q.support, ∃ w ∈ p.support, (w : Site 2) = (z : Site 2) := by
  classical
  obtain ⟨c, d, r, hrsub, hrpath, hc, hd, hrbox, _⟩ :=
    exists_horizontal_strip_subpath p.bypass p.bypass_isPath
      (L := -(M : ℤ)) (R := M) (by omega) ha hb
  let Q := centeredPlaneRectangle M H
  let P := r.map (rectangleGraphToLattice (centeredPlaneRectangle W H))
  have hP : ∀ z ∈ P.support, z ∈ (Q : Set (Site 2)) := by
    intro z hz
    change z ∈ (r.map (rectangleGraphToLattice _)).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    have hx := hrbox w hw
    have hy := (mem_centeredPlaneRectangle _ _ _).mp w.property
    exact ⟨hx.1, hx.2, hy.2.2.1, hy.2.2.2⟩
  let q := P.induce (Q : Set (Site 2)) hP
  have hqmap : q.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom = P :=
    SimpleGraph.Walk.map_induce P hP
  have hqpath : q.IsPath := by
    have hPpath : P.IsPath := hrpath.map Subtype.val_injective
    have h : (q.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom).IsPath := by
      rw [hqmap]
      exact hPpath
    exact h.of_map
  have hqopen : IsBondOpenWalk ω q := by
    apply (isBondOpenWalk_iff_edges ω q).mpr
    intro e he
    rw [hqmap] at he
    exact (isBondOpenWalk_iff_edges ω r).mp (hp.bypass.subwalk hrsub) e he
  refine ⟨⟨c, hP _ P.start_mem_support⟩, ⟨d, hP _ P.end_mem_support⟩,
    q, hqpath, hqopen, hc, hd, ?_⟩
  intro z hz
  have hzP : (z : Site 2) ∈ P.support := by
    have hzmap : (z : Site 2) ∈
        (q.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom).support := by
      rw [SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨z, hz, rfl⟩
    rw [hqmap] at hzmap
    exact hzmap
  change (z : Site 2) ∈ (r.map (rectangleGraphToLattice _)).support at hzP
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hzP
  obtain ⟨w, hw, he⟩ := hzP
  exact ⟨w, p.support_bypass_subset_support (hrsub.support_subset hw), he⟩

end Sandpile.External.RSW
