import Sandpile.External.RSW.RefinedWalkBounds
import Sandpile.External.RSW.RefinedDualConnector
import Sandpile.External.RSW.InsetBoundaryIntersection
import Sandpile.External.RSW.WiredKSTBoundaryCut

/-!
# Refined wired dual paths and walls

A wired-open dual path joining the two exterior boundary arcs meets every
vertical path with endpoints in the central target segments on the refined grid.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- A wired dual boundary path intersects a central vertical wall after refinement. -/
theorem refined_wired_boundary_walk_intersects_wall (k : ℕ) (hk : 0 < k)
    (ω : Sym2 (Site 2) → Bool) {a b u v : Site 2}
    (p : (lattice 2).Walk a b) (q : (lattice 2).Walk u v)
    (hp : ∀ z ∈ p.support, -((k + k / 12 : ℕ) : ℤ) ≤ z 0 ∧
      z 0 ≤ ((k + k / 12 : ℕ) : ℤ) ∧ -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k)
    (ha : a 1 = k ∧ -((k / 12 : ℕ) : ℤ) ≤ a 0 ∧ a 0 ≤ k / 12)
    (hb : b 1 = -(k : ℤ) ∧ -((k / 12 : ℕ) : ℤ) ≤ b 0 ∧ b 0 ≤ k / 12)
    (hq : ∀ z ∈ q.support, -((k + k / 12 : ℕ) : ℤ) - 1 ≤ z 0 ∧
      z 0 ≤ ((k + k / 12 : ℕ) : ℤ) ∧ -((k : ℤ) + 1) ≤ z 1 ∧ z 1 ≤ k)
    (hu : wiredKSTDualLeftBoundary k u) (hv : wiredKSTDualRightBoundary k v)
    (hopen : ∀ f ∈ q.edges, dualBondConfig (wiredKSTConfig k ω) f = true) :
    ∃ z ∈ (refinedLatticeWalk 0 p).support,
      z ∈ (refinedLatticeWalk (fun _ => 1) q).support := by
  let A : ℤ := ((k + k / 12 : ℕ) : ℤ)
  let D : ℤ := ((k / 12 : ℕ) : ℤ)
  let P := refinedLatticeWalk 0 p
  let Q := refinedLatticeWalk (fun _ => 1) q
  let f : lattice 2 →g LatticeModels.zdGraph 2 :=
    ⟨id, fun h => by rw [← lattice_eq_zdGraph]; exact h⟩
  have hP0 := refinedLatticeWalk_coord_bounds 0 p 0 (-A) A (by
    intro z hz
    have h := hp z hz
    exact ⟨h.1, h.2.1⟩)
  have hP1 := refinedLatticeWalk_coord_bounds 0 p 1 (-(k : ℤ)) k (by
    intro z hz
    exact (hp z hz).2.2)
  have hQ0 := refinedLatticeWalk_coord_bounds (fun _ => 1) q 0 (-A - 1) A (by
    intro z hz
    have h := hq z hz
    exact ⟨h.1, h.2.1⟩)
  have hQ1 := refinedLatticeWalk_coord_bounds (fun _ => 1) q 1 (-((k : ℤ) + 1)) k (by
    intro z hz
    exact (hq z hz).2.2)
  have hPbox : ∀ z ∈ (P.map f).support, -2*A-1 ≤ z 0 ∧ z 0 ≤ 2*A+1 ∧
      -2*(k : ℤ) ≤ z 1 ∧ z 1 ≤ 2*(k : ℤ) := by
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have h0 := hP0 w hw
    have h1 := hP1 w hw
    simp only [Pi.zero_apply, add_zero] at h0 h1
    change -2*A-1 ≤ w 0 ∧ w 0 ≤ 2*A+1 ∧ -2*(k : ℤ) ≤ w 1 ∧ w 1 ≤ 2*(k : ℤ)
    omega
  have hQbox : ∀ z ∈ (Q.map f).support, -2*A-1 ≤ z 0 ∧ z 0 ≤ 2*A+1 ∧
      -2*(k : ℤ)-1 ≤ z 1 ∧ z 1 ≤ 2*(k : ℤ)+1 := by
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have h0 := hQ0 w hw
    have h1 := hQ1 w hw
    change -2*A-1 ≤ w 0 ∧ w 0 ≤ 2*A+1 ∧ -2*(k : ℤ)-1 ≤ w 1 ∧ w 1 ≤ 2*(k : ℤ)+1
    omega
  have hAD : D ≤ A := by dsimp [A, D]; omega
  have htop := refined_wired_dual_avoids_upper_connector k ω q hopen a ha.1 ha.2.1 ha.2.2
  have hbot := refined_wired_dual_avoids_lower_connector k ω q hopen b hb.1 hb.2.1 hb.2.2
  have hcross := inset_vertical_walk_intersects_boundary_walk
    (L := -2*A-1) (R := 2*A+1) (B := -2*(k : ℤ)-1) (T := 2*(k : ℤ)+1)
    (c := -2*D) (d := 2*D) (by omega) (by omega) (by omega)
    (P.map f) (Q.map f) (by simpa only [sub_add_cancel, add_sub_cancel_right] using hPbox) hQbox
    (by
      change 2 * a 1 + 0 = 2 * (k : ℤ) + 1 - 1 ∧
        -2 * D ≤ 2 * a 0 + 0 ∧ 2 * a 0 + 0 ≤ 2 * D
      omega)
    (by
      change 2 * b 1 + 0 = -2 * (k : ℤ) - 1 + 1 ∧
        -2 * D ≤ 2 * b 0 + 0 ∧ 2 * b 0 + 0 ≤ 2 * D
      omega)
    (by
      dsimp [wiredKSTDualLeftBoundary] at hu
      change 2 * u 0 + 1 = -2 * A - 1 ∨
        (2 * u 0 + 1 ≤ -2 * D ∧
          (2 * u 1 + 1 = -2 * (k : ℤ) - 1 ∨ 2 * u 1 + 1 = 2 * (k : ℤ) + 1))
      omega)
    (by
      dsimp [wiredKSTDualRightBoundary] at hv
      change 2 * v 0 + 1 = 2 * A + 1 ∨
        (2 * D ≤ 2 * v 0 + 1 ∧
          (2 * v 1 + 1 = -2 * (k : ℤ) - 1 ∨ 2 * v 1 + 1 = 2 * (k : ℤ) + 1))
      omega)
  rcases hcross with ⟨z, hzP, hzQ⟩ | h | h
  · rw [SimpleGraph.Walk.support_map, List.mem_map] at hzP hzQ
    obtain ⟨x, hx, hxz⟩ := hzP
    obtain ⟨y, hy, hyz⟩ := hzQ
    change x = z at hxz
    change y = z at hyz
    subst x
    subst y
    exact ⟨z, hx, hy⟩
  · apply False.elim
    apply htop
    rw [SimpleGraph.Walk.support_map, List.mem_map] at h
    obtain ⟨z, hz, he⟩ := h
    change z = refinedVertex 0 a + Pi.single 1 1 at he
    simpa only [he] using hz
  · apply False.elim
    apply hbot
    rw [SimpleGraph.Walk.support_map, List.mem_map] at h
    obtain ⟨z, hz, he⟩ := h
    change z = refinedVertex 0 b - Pi.single 1 1 at he
    simpa only [he] using hz

end Sandpile.External.RSW
