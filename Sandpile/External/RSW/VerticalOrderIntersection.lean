import Sandpile.External.RSW.OrderedArcIntersection

/-!
# Order of vertical lattice crossings

Vertical walks in a rectangle meet when their endpoints occur in opposite
left-to-right orders on the top and bottom sides.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Two vertical rectangle crossings with oppositely ordered endpoints intersect. -/
theorem vertical_walks_intersect_of_opposite_order {L R B T : ℤ}
    (hBT : B < T) {a b u v : Site 2}
    (p : (LatticeModels.zdGraph 2).Walk a b)
    (q : (LatticeModels.zdGraph 2).Walk u v)
    (hp : ∀ z ∈ p.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hq : ∀ z ∈ q.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (ha : a 1 = T) (hb : b 1 = B) (hu : u 1 = T) (hv : v 1 = B)
    (htop : u 0 ≤ a 0) (hbottom : b 0 ≤ v 0) :
    ∃ z ∈ p.support, z ∈ q.support :=
  vertical_walk_intersects_ordered_boundary_walk hBT p q hp hq ha hb
    (Or.inr (Or.inl ⟨hu, htop⟩)) (Or.inr (Or.inl ⟨hv, hbottom⟩))

/-- Disjoint vertical crossings preserve the left-to-right order of their endpoints. -/
theorem vertical_walks_order_of_disjoint {L R B T : ℤ}
    (hBT : B < T) {a b u v : Site 2}
    (p : (LatticeModels.zdGraph 2).Walk a b)
    (q : (LatticeModels.zdGraph 2).Walk u v)
    (hp : ∀ z ∈ p.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hq : ∀ z ∈ q.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (ha : a 1 = T) (hb : b 1 = B) (hu : u 1 = T) (hv : v 1 = B)
    (hdis : ∀ z ∈ p.support, z ∉ q.support) (htop : u 0 ≤ a 0) :
    v 0 < b 0 := by
  by_contra hn
  obtain ⟨z, hzp, hzq⟩ := vertical_walks_intersect_of_opposite_order hBT p q hp hq
    ha hb hu hv htop (by omega)
  exact hdis z hzp hzq

end Sandpile.External.RSW
