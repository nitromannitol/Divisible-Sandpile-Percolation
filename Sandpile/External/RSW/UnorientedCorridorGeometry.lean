import Sandpile.External.RSW.UnorientedCorridorContact
import Sandpile.External.RSW.WiredKSTScaleInclusion
import Sandpile.External.RSW.RefinedWiredWallBridge
import Sandpile.External.RSW.RefinedRectangleWalks
import Sandpile.External.RSW.BridgeConnectedWalls

/-!
# Unoriented corridor geometry

An exceptional path must meet one of two walls attached to opposite sides of
the corridor. The proof uses a wired dual boundary cut on the refined lattice.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- An exceptional path at a larger scale meets one of the two attached walls. -/
theorem kstUnorientedCorridorIntersects (m k : ℕ) (hk : 12 ≤ k) (hkm : k < m) :
    KSTUnorientedCorridorIntersects m k := by
  classical
  intro a b c d x y e f u v p r q r' q' hp hsub hsubrev hr hx hy hr' hu hv
  by_contra hcontact
  let S := centeredPlaneRectangle (m + 3 * (m / 12)) m
  let M := m + 3 * (m / 12)
  let F : lattice 2 →g LatticeModels.zdGraph 2 :=
    ⟨id, fun h => by rw [← lattice_eq_zdGraph]; exact h⟩
  have hmap {s t : Site 2} (w : (lattice 2).Walk s t) (z : Site 2) :
      z ∈ (w.map F).support ↔ z ∈ w.support := by
    rw [SimpleGraph.Walk.support_map]
    change z ∈ w.support.map id ↔ z ∈ w.support
    rw [List.map_id]
  have hpr : ∀ z ∈ p.support, z ∉ r.support := by
    intro z hz hz'
    exact hcontact (Or.inl ⟨z, hz, Or.inl hz'⟩)
  have hpq : ∀ z ∈ p.support, z ∉ q.support := by
    intro z hz hz'
    exact hcontact (Or.inl ⟨z, hz, Or.inr hz'⟩)
  have hpr' : ∀ z ∈ p.support, z ∉ r'.support := by
    intro z hz hz'
    exact hcontact (Or.inr ⟨z, hz, Or.inl hz'⟩)
  have hpq' : ∀ z ∈ p.support, z ∉ q'.support := by
    intro z hz hz'
    exact hcontact (Or.inr ⟨z, hz, Or.inr hz'⟩)
  have hQR : centeredPlaneRectangle (k + k / 12) (k + 1) ⊆ S :=
    wiredKST_rectangle_subset_corridor hkm
  obtain ⟨g, h, bridge, hbridge, hg, hh, hbbox, havoid⟩ :=
    exists_refined_wired_boundary_cut_avoiding_path k hk p hp.1 hsub hsubrev hQR
  let P := refinedLatticeWalk 0 (p.map (rectangleGraphToLattice S))
  let L := refinedLatticeWalk 0 (r.map (rectangleGraphToLattice S))
  let LL := refinedLatticeWalk 0 (q.map (rectangleGraphToLattice S))
  let R := refinedLatticeWalk 0 (r'.map (rectangleGraphToLattice S))
  let RL := refinedLatticeWalk 0 (q'.map (rectangleGraphToLattice S))
  let B := refinedLatticeWalk (fun _ => 1) (bridge.map (rectangleGraphToLattice _))
  have hL := refined_wired_cut_intersects_kst_wall k (by omega) (pathBondConfig p)
    r bridge hr hbridge hg hh hbbox
  have hR := refined_wired_cut_intersects_kst_wall k (by omega) (pathBondConfig p)
    r' bridge hr' hbridge hg hh hbbox
  have hPL := refined_rectangle_walks_disjoint p r hpr
  have hPLL := refined_rectangle_walks_disjoint p q hpq
  have hPR := refined_rectangle_walks_disjoint p r' hpr'
  have hPRL := refined_rectangle_walks_disjoint p q' hpq'
  have hPbox := refined_centered_rectangle_walk_bounds M m p
  have hLbox := refined_centered_rectangle_walk_bounds M m r
  have hLLbox := refined_centered_rectangle_walk_bounds M m q
  have hRbox := refined_centered_rectangle_walk_bounds M m r'
  have hRLbox := refined_centered_rectangle_walk_bounds M m q'
  have hsmall : k + k / 12 + 1 ≤ M := by
    have hd : k / 12 ≤ m / 12 := Nat.div_le_div_right (by omega)
    dsimp [M]
    omega
  have hB0 := refinedLatticeWalk_coord_bounds (fun _ => 1)
    (bridge.map (rectangleGraphToLattice _)) 0
    (-((k + k / 12 : ℕ) : ℤ) - 1) ((k + k / 12 : ℕ) : ℤ) (by
      intro z hz
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      exact ⟨(hbbox z' hz').1, (hbbox z' hz').2.1⟩)
  have hB1 := refinedLatticeWalk_coord_bounds (fun _ => 1)
    (bridge.map (rectangleGraphToLattice _)) 1 (-((k : ℤ) + 1)) k (by
      intro z hz
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨z', hz', rfl⟩ := hz
      exact (hbbox z' hz').2.2)
  have hBbox : ∀ z ∈ B.support, -2*(M : ℤ) ≤ z 0 ∧ z 0 ≤ 2*(M : ℤ) ∧
      -2*(m : ℤ) ≤ z 1 ∧ z 1 ≤ 2*(m : ℤ) := by
    intro z hz
    have h0 := hB0 z hz
    have h1 := hB1 z hz
    have hs : ((k + k / 12 + 1 : ℕ) : ℤ) ≤ M := by exact_mod_cast hsmall
    have hm : (k : ℤ) + 1 ≤ m := by exact_mod_cast hkm
    push_cast at hs
    omega
  have hxL : refinedVertex 0 (x : Site 2) ∈ L.support := by
    apply refinedVertex_mem_refinedLatticeWalk_support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨x, hx, rfl⟩
  have huR : refinedVertex 0 (u : Site 2) ∈ R.support := by
    apply refinedVertex_mem_refinedLatticeWalk_support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨u, hu, rfl⟩
  have hcross := vertical_crossing_intersects_bridged_walls
    (L := -2*(M : ℤ)) (R := 2*(M : ℤ)) (B := -2*(m : ℤ)) (T := 2*(m : ℤ))
    (P.map F) (L.map F) (LL.map F) (R.map F) (RL.map F) (B.map F)
    (by simpa only [hmap] using hPbox) (by simpa only [hmap] using hLbox)
    (by simpa only [hmap] using hLLbox) (by simpa only [hmap] using hRbox)
    (by simpa only [hmap] using hRLbox) (by simpa only [hmap] using hBbox)
    (by
      change 2 * (a : Site 2) 1 + 0 = 2 * (m : ℤ)
      have h := hp.2.1
      omega)
    (by
      change 2 * (b : Site 2) 1 + 0 = -2 * (m : ℤ)
      have h := hp.2.2.1
      omega)
    (by
      rw [hmap]
      change refinedVertex 0 (x : Site 2) ∈ L.support
      exact hxL)
    (by
      rw [hmap]
      change refinedVertex 0 (u : Site 2) ∈ R.support
      exact huR)
    (by change 2 * (y : Site 2) 0 + 0 = -2 * (M : ℤ); omega)
    (by change 2 * (v : Site 2) 0 + 0 = 2 * (M : ℤ); omega)
    (by simpa only [hmap] using hL) (by simpa only [hmap] using hR)
  obtain ⟨z, hzP, hz⟩ := hcross
  simp only [hmap] at hzP hz
  rcases hz with hz | hz | hz | hz | hz
  · exact hPL z hzP hz
  · exact hPLL z hzP hz
  · exact havoid z hzP hz
  · exact hPR z hzP hz
  · exact hPRL z hzP hz

end Sandpile.External.RSW
