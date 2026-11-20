import Sandpile.External.RSW.RefinedWiredBoundaryCut
import Sandpile.External.RSW.RefinedWiredWallIntersection

/-!
# A dual bridge meeting all walls

An exceptional path has a wired dual boundary cut that avoids it and intersects
every central wall after embedding both paths into the refined lattice.
-/

namespace Sandpile.External.RSW

/-- A wired boundary cut intersects every refined KST wall. -/
theorem refined_wired_cut_intersects_kst_wall (k : ℕ) (hk : 0 < k)
    (ω : Sym2 (Site 2) → Bool) {Q R : Finset (Site 2)} {a b : Q} {u v : R}
    (p : (rectangleGraph Q).Walk a b) (q : (rectangleGraph R).Walk u v)
    (hp : IsKSTPath k p)
    (hq : IsBondOpenWalk (dualBondConfig (wiredKSTConfig k ω)) q)
    (hu : wiredKSTDualLeftBoundary k u) (hv : wiredKSTDualRightBoundary k v)
    (hbox : ∀ z ∈ q.support, -((k + k / 12 : ℕ) : ℤ) - 1 ≤ (z : Site 2) 0 ∧
      (z : Site 2) 0 ≤ ((k + k / 12 : ℕ) : ℤ) ∧
      -((k : ℤ) + 1) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k) :
    ∃ z ∈ (refinedLatticeWalk 0 (p.map (rectangleGraphToLattice Q))).support,
      z ∈ (refinedLatticeWalk (fun _ => 1) (q.map (rectangleGraphToLattice R))).support := by
  apply refined_wired_boundary_walk_intersects_wall k hk ω
  · intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact (mem_centeredPlaneRectangle _ _ _).mp (hp.2.2.2.2.2.2.2 z' hz')
  · exact ⟨hp.2.1, hp.2.2.2.1, hp.2.2.2.2.1⟩
  · exact ⟨hp.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1⟩
  · intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact hbox z' hz'
  · exact hu
  · exact hv
  · intro e he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    exact ((isBondOpenWalk_iff_local_edges _ q).mp hq) e' he'

end Sandpile.External.RSW
