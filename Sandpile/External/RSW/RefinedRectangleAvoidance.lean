import Sandpile.External.RSW.RefinedWiredAvoidance
import Sandpile.External.RSW.BondWalk

/-!
# Refined avoidance for rectangle walks

The refined wired-strip avoidance theorem applies to walks in finite rectangle
graphs by forgetting the rectangle membership proof.
-/

namespace Sandpile.External.RSW

/-- The inclusion of an induced rectangle graph into the square lattice. -/
def rectangleGraphToLattice (Q : Finset (Site 2)) : rectangleGraph Q →g lattice 2 :=
  ⟨Subtype.val, fun h => h⟩

/-- A wired dual rectangle walk avoids a primal rectangle walk on the refined grid. -/
theorem refined_wired_rectangle_walk_avoids (k : ℕ) (ω : Sym2 (Site 2) → Bool)
    {Q R : Finset (Site 2)} {a b : Q} {c d : R}
    (p : (rectangleGraph Q).Walk a b) (q : (rectangleGraph R).Walk c d)
    (hp : IsBondOpenWalk ω p) (hq : IsBondOpenWalk (dualBondConfig (wiredKSTConfig k ω)) q)
    (hstrip : ∀ z ∈ q.support, -(k : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k)
    (htop : ∀ x ∈ q.support, ∀ y ∈ q.support, (rectangleGraph R).Adj x y →
      ¬ ((x : Site 2) 1 = k ∧ (y : Site 2) 1 = k)) :
    ∀ z ∈ (refinedLatticeWalk 0 (p.map (rectangleGraphToLattice Q))).support,
      z ∉ (refinedLatticeWalk (fun _ => 1) (q.map (rectangleGraphToLattice R))).support := by
  apply refined_wired_dual_walk_avoids k ω
  · intro e he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    exact ((isBondOpenWalk_iff_local_edges ω p).mp hp) e' he'
  · intro e he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    exact ((isBondOpenWalk_iff_local_edges (dualBondConfig (wiredKSTConfig k ω)) q).mp hq) e' he'
  · intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact hstrip z' hz'
  · intro x hx y hy hxy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact htop x' hx' y' hy' hxy

end Sandpile.External.RSW
