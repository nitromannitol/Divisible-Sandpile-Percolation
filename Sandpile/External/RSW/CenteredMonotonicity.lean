import Sandpile.External.RSW.CenteredGeometry
import Sandpile.External.RSW.DualRotatedCrossing

/-!
# Restricting centered bond crossings

A horizontal crossing of a centered rectangle restricts to a crossing of any narrower
centered rectangle of the same height.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Restricting a centered horizontal bond crossing to a narrower centered rectangle. -/
theorem centeredBondCrossingEvent_anti_width {m M n : ℕ} (hm : m ≤ M) :
    centeredBondCrossingEvent M n ⊆ centeredBondCrossingEvent m n := by
  intro ω hω
  obtain ⟨a, b, p, ha, hb, hp⟩ := (mem_centeredBondCrossingEvent_iff M n ω).mp hω
  let Q := centeredPlaneRectangle M n
  let R := centeredPlaneRectangle m n
  let f : rectangleGraph Q →g lattice 2 := ⟨Subtype.val, fun h => h⟩
  let p₀ := p.map f
  have hpQ : ∀ z ∈ p₀.support, z ∈ (Q : Set (Site 2)) := by
    intro z hz
    change z ∈ (p.map f).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hz
    exact t.property
  have hpω : ∀ e ∈ p₀.edges, e ∈ openPlaneBonds ω := by
    intro e he
    refine ⟨SimpleGraph.Walk.edges_subset_edgeSet p₀ he, ?_⟩
    exact (isBondOpenWalk_iff_edges ω p).mp hp e he
  have hconn : openPlaneBonds ω ∈ openConnIn (↑Q : Set (Site 2)) (a : Site 2) (b : Site 2) :=
    mem_openConnIn_of_walk p₀ hpQ hpω
  obtain ⟨c, hc, hac⟩ := exists_openConnIn_column (openPlaneBonds_subset ω) (m : ℤ)
    (by rw [ha]; exact_mod_cast (show -(M : ℤ) ≤ m by omega))
    (by rw [hb]; exact_mod_cast hm) hconn
  have hca : openPlaneBonds ω ∈ openConnIn (↑Q ∩ {z : Site 2 | z 0 ≤ (m : ℤ)}) c (a : Site 2) := by
    rw [openConnIn_comm]
    exact hac
  obtain ⟨d, hd, hcd⟩ := exists_openConnIn_column_ge (openPlaneBonds_subset ω) (-(m : ℤ))
    (by rw [hc]; omega) (by rw [ha]; exact_mod_cast (show -(M : ℤ) ≤ -(m : ℤ) by omega)) hca
  have hsub : ((↑Q : Set (Site 2)) ∩ {z : Site 2 | z 0 ≤ (m : ℤ)}) ∩
      {z : Site 2 | -(m : ℤ) ≤ z 0} ⊆ (↑R : Set (Site 2)) := by
    intro z hz
    have hzQ := (mem_centeredPlaneRectangle M n z).mp hz.1.1
    apply (mem_centeredPlaneRectangle m n z).mpr
    exact ⟨hz.2, hz.1.2, hzQ.2.2⟩
  have hdc : openPlaneBonds ω ∈ openConnIn (↑R) d c := by
    rw [openConnIn_comm]
    exact openConnIn_mono hsub c d hcd
  have hωl : openPlaneBonds ω ⊆ (lattice 2).edgeSet := by
    rw [lattice_eq_zdGraph]
    exact openPlaneBonds_subset ω
  obtain ⟨q, hqR, hqω⟩ := exists_walk_of_mem_openConnIn (G := lattice 2) hωl hdc
  let r := q.induce (R : Set (Site 2)) hqR
  apply (mem_centeredBondCrossingEvent_iff m n ω).mpr
  refine ⟨⟨d, hqR d q.start_mem_support⟩, ⟨c, hqR c q.end_mem_support⟩, r, hd, hc, ?_⟩
  apply (isBondOpenWalk_iff_edges ω r).mpr
  intro e he
  rw [SimpleGraph.Walk.map_induce] at he
  exact (hqω e he).2

end Sandpile.External.RSW
