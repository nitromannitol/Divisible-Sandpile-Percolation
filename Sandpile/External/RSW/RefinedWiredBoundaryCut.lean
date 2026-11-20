import Sandpile.External.RSW.RefinedWiredBoundaryAvoidance
import Sandpile.External.RSW.RefinedRectangleAvoidance
import Sandpile.External.RSW.WiredKSTBoundaryCut

/-!
# Refined wired boundary cuts

An exceptional path has a wired-open dual boundary cut whose refined image
avoids the entire exceptional path.
-/

namespace Sandpile.External.RSW

/-- An exceptional path has an untrimmed dual boundary cut avoiding it after refinement. -/
theorem exists_refined_wired_boundary_cut_avoiding_path (k : ℕ) (hk : 12 ≤ k)
    {Q : Finset (Site 2)} {u v : Q} (p : (rectangleGraph Q).Walk u v)
    (hp : p.IsPath) (hsub : ¬ HasKSTSubpath k p)
    (hsubrev : ¬ HasKSTSubpath k p.reverse)
    (hQR : centeredPlaneRectangle (k + k / 12) (k + 1) ⊆ Q) :
    ∃ (a b : centeredPlaneRectangle (k + k / 12 + 1) (k + 1))
      (q : (rectangleGraph (centeredPlaneRectangle (k + k / 12 + 1) (k + 1))).Walk a b),
      IsBondOpenWalk (dualBondConfig (wiredKSTConfig k (pathBondConfig p))) q ∧
      wiredKSTDualLeftBoundary k a ∧ wiredKSTDualRightBoundary k b ∧
      (∀ z ∈ q.support, -((k + k / 12 : ℕ) : ℤ) - 1 ≤ (z : Site 2) 0 ∧
        (z : Site 2) 0 ≤ ((k + k / 12 : ℕ) : ℤ) ∧
        -((k : ℤ) + 1) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k) ∧
      ∀ z ∈ (refinedLatticeWalk 0 (p.map (rectangleGraphToLattice Q))).support,
        z ∉ (refinedLatticeWalk (fun _ => 1)
          (q.map (rectangleGraphToLattice _))).support := by
  classical
  obtain ⟨a, b, q, hpath, hopen, ha, hb, hbox, hinterior⟩ :=
    exists_wiredKST_dual_boundary_cut_of_no_subpath k (by omega) p hp hsub hsubrev hQR
  have hd : 0 < k / 12 := Nat.div_pos hk (by decide)
  have hsep : ¬ (rectangleGraph (centeredPlaneRectangle (k + k / 12 + 1) (k + 1))).Adj a b := by
    intro hab
    have hab' : (lattice 2).Adj (a : Site 2) (b : Site 2) := hab
    have hc := lattice_two_adj_cases hab'
    dsimp [wiredKSTDualLeftBoundary, wiredKSTDualRightBoundary] at ha hb
    rcases hc with hc | hc | hc | hc <;> omega
  have htop : ∀ x ∈ q.support, ∀ y ∈ q.support,
      (rectangleGraph (centeredPlaneRectangle (k + k / 12 + 1) (k + 1))).Adj x y →
        ¬ ((x : Site 2) 1 = k ∧ (y : Site 2) 1 = k) := by
    intro x hx y hy hxy hrow
    have hxe : x = a ∨ x = b := by
      by_contra hn
      push Not at hn
      have h := hinterior x hx hn.1 hn.2
      omega
    have hye : y = a ∨ y = b := by
      by_contra hn
      push Not at hn
      have h := hinterior y hy hn.1 hn.2
      omega
    rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
    · exact hxy.ne rfl
    · exact hsep hxy
    · exact hsep hxy.symm
    · exact hxy.ne rfl
  have hbot : ∀ x ∈ q.support, ∀ y ∈ q.support,
      (rectangleGraph (centeredPlaneRectangle (k + k / 12 + 1) (k + 1))).Adj x y →
        ¬ ((x : Site 2) 1 = -((k : ℤ) + 1) ∧
          (y : Site 2) 1 = -((k : ℤ) + 1)) := by
    intro x hx y hy hxy hrow
    have hxe : x = a ∨ x = b := by
      by_contra hn
      push Not at hn
      have h := hinterior x hx hn.1 hn.2
      omega
    have hye : y = a ∨ y = b := by
      by_contra hn
      push Not at hn
      have h := hinterior y hy hn.1 hn.2
      omega
    rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
    · exact hxy.ne rfl
    · exact hsep hxy
    · exact hsep hxy.symm
    · exact hxy.ne rfl
  refine ⟨a, b, q, hopen, ha, hb, hbox, ?_⟩
  apply refined_wired_dual_exterior_walk_avoids k (pathBondConfig p)
  · intro e he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    simp only [pathBondConfig, decide_eq_true_eq, List.mem_map]
    exact ⟨e', he', rfl⟩
  · intro e he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    exact ((isBondOpenWalk_iff_local_edges _ q).mp hopen) e' he'
  · intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact (hbox z' hz').2.2
  · intro x hx y hy hxy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact htop x' hx' y' hy' hxy
  · intro x hx y hy hxy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hbot x' hx' y' hy' hxy

end Sandpile.External.RSW
