import Sandpile.External.RSW.RefinedWiredWallBridge
import Sandpile.External.RSW.RefinedRectangleWalks
import Sandpile.External.RSW.HorizontalBridgeWalls

/-!
# Horizontal crossings and KST wall obstructions

A horizontal crossing avoiding top- and bottom-attached KST walls contains a
KST subpath in one of its two traversal directions.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- A horizontal crossing either meets an attached wall or contains a KST subpath. -/
theorem horizontal_crossing_meets_walls_or_kst_subpath (M N k : ℕ)
    (hk : 12 ≤ k) (hM : k + k / 12 + 1 ≤ M) (hN : k + 1 ≤ N)
    {a b c d x y e f u v : centeredPlaneRectangle M N}
    (p : (rectangleGraph (centeredPlaneRectangle M N)).Walk a b)
    (lower : (rectangleGraph (centeredPlaneRectangle M N)).Walk c d)
    (lowerLink : (rectangleGraph (centeredPlaneRectangle M N)).Walk x y)
    (upper : (rectangleGraph (centeredPlaneRectangle M N)).Walk e f)
    (upperLink : (rectangleGraph (centeredPlaneRectangle M N)).Walk u v)
    (hp : p.IsPath) (ha : (a : Site 2) 0 = M) (hb : (b : Site 2) 0 = -(M : ℤ))
    (hl : IsKSTPath k lower) (hu : IsKSTPath k upper)
    (hx : x ∈ lower.support) (hu' : u ∈ upper.support)
    (hy : (y : Site 2) 1 = -(N : ℤ)) (hv : (v : Site 2) 1 = N) :
    HasKSTSubpath k p ∨ HasKSTSubpath k p.reverse ∨
      ∃ z ∈ p.support, z ∈ lower.support ∨ z ∈ lowerLink.support ∨
        z ∈ upper.support ∨ z ∈ upperLink.support := by
  classical
  by_cases hsub : HasKSTSubpath k p
  · exact Or.inl hsub
  by_cases hsubrev : HasKSTSubpath k p.reverse
  · exact Or.inr (Or.inl hsubrev)
  apply Or.inr
  apply Or.inr
  by_contra hcontact
  let S := centeredPlaneRectangle M N
  let F : lattice 2 →g LatticeModels.zdGraph 2 :=
    ⟨id, fun h => by rw [← lattice_eq_zdGraph]; exact h⟩
  have hmap {s t : Site 2} (w : (lattice 2).Walk s t) (z : Site 2) :
      z ∈ (w.map F).support ↔ z ∈ w.support := by
    rw [SimpleGraph.Walk.support_map]
    change z ∈ w.support.map id ↔ z ∈ w.support
    rw [List.map_id]
  have hpl : ∀ z ∈ p.support, z ∉ lower.support := by
    intro z hz hz'
    exact hcontact ⟨z, hz, Or.inl hz'⟩
  have hpll : ∀ z ∈ p.support, z ∉ lowerLink.support := by
    intro z hz hz'
    exact hcontact ⟨z, hz, Or.inr (Or.inl hz')⟩
  have hpu : ∀ z ∈ p.support, z ∉ upper.support := by
    intro z hz hz'
    exact hcontact ⟨z, hz, Or.inr (Or.inr (Or.inl hz'))⟩
  have hpul : ∀ z ∈ p.support, z ∉ upperLink.support := by
    intro z hz hz'
    exact hcontact ⟨z, hz, Or.inr (Or.inr (Or.inr hz'))⟩
  have hQR : centeredPlaneRectangle (k + k / 12) (k + 1) ⊆ S := by
    intro z hz
    have hz' := (mem_centeredPlaneRectangle _ _ _).mp hz
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    push_cast at *
    omega
  obtain ⟨g, h, bridge, hbridge, hg, hh, hbbox, havoid⟩ :=
    exists_refined_wired_boundary_cut_avoiding_path k hk p hp hsub hsubrev hQR
  let P := refinedLatticeWalk 0 (p.map (rectangleGraphToLattice S))
  let L := refinedLatticeWalk 0 (lower.map (rectangleGraphToLattice S))
  let LL := refinedLatticeWalk 0 (lowerLink.map (rectangleGraphToLattice S))
  let U := refinedLatticeWalk 0 (upper.map (rectangleGraphToLattice S))
  let UL := refinedLatticeWalk 0 (upperLink.map (rectangleGraphToLattice S))
  let B := refinedLatticeWalk (fun _ => 1) (bridge.map (rectangleGraphToLattice _))
  have hL := refined_wired_cut_intersects_kst_wall k (by omega) (pathBondConfig p)
    lower bridge hl hbridge hg hh hbbox
  have hU := refined_wired_cut_intersects_kst_wall k (by omega) (pathBondConfig p)
    upper bridge hu hbridge hg hh hbbox
  have hPL := refined_rectangle_walks_disjoint p lower hpl
  have hPLL := refined_rectangle_walks_disjoint p lowerLink hpll
  have hPU := refined_rectangle_walks_disjoint p upper hpu
  have hPUL := refined_rectangle_walks_disjoint p upperLink hpul
  have hPbox := refined_centered_rectangle_walk_bounds M N p
  have hLbox := refined_centered_rectangle_walk_bounds M N lower
  have hLLbox := refined_centered_rectangle_walk_bounds M N lowerLink
  have hUbox := refined_centered_rectangle_walk_bounds M N upper
  have hULbox := refined_centered_rectangle_walk_bounds M N upperLink
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
      -2*(N : ℤ) ≤ z 1 ∧ z 1 ≤ 2*(N : ℤ) := by
    intro z hz
    have h0 := hB0 z hz
    have h1 := hB1 z hz
    have hm : ((k + k / 12 + 1 : ℕ) : ℤ) ≤ M := by exact_mod_cast hM
    have hn : ((k + 1 : ℕ) : ℤ) ≤ N := by exact_mod_cast hN
    push_cast at hm hn
    omega
  have hxL : refinedVertex 0 (x : Site 2) ∈ L.support := by
    apply refinedVertex_mem_refinedLatticeWalk_support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨x, hx, rfl⟩
  have huU : refinedVertex 0 (u : Site 2) ∈ U.support := by
    apply refinedVertex_mem_refinedLatticeWalk_support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨u, hu', rfl⟩
  have hcross := horizontal_crossing_intersects_bridged_walls
    (L := -2*(M : ℤ)) (R := 2*(M : ℤ)) (B := -2*(N : ℤ)) (T := 2*(N : ℤ))
    (P.map F) (L.map F) (LL.map F) (U.map F) (UL.map F) (B.map F)
    (by simpa only [hmap] using hPbox) (by simpa only [hmap] using hLbox)
    (by simpa only [hmap] using hLLbox) (by simpa only [hmap] using hUbox)
    (by simpa only [hmap] using hULbox) (by simpa only [hmap] using hBbox)
    (by change 2 * (a : Site 2) 0 + 0 = 2 * (M : ℤ); omega)
    (by change 2 * (b : Site 2) 0 + 0 = -2 * (M : ℤ); omega)
    (by rw [hmap]; change refinedVertex 0 (x : Site 2) ∈ L.support; exact hxL)
    (by rw [hmap]; change refinedVertex 0 (u : Site 2) ∈ U.support; exact huU)
    (by change 2 * (y : Site 2) 1 + 0 = -2 * (N : ℤ); omega)
    (by change 2 * (v : Site 2) 1 + 0 = 2 * (N : ℤ); omega)
    (by simpa only [hmap] using hL) (by simpa only [hmap] using hU)
  obtain ⟨z, hzP, hz⟩ := hcross
  simp only [hmap] at hzP hz
  rcases hz with hz | hz | hz | hz | hz
  · exact hPL z hzP hz
  · exact hPLL z hzP hz
  · exact havoid z hzP hz
  · exact hPU z hzP hz
  · exact hPUL z hzP hz

end Sandpile.External.RSW
