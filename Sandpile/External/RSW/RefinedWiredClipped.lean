import Sandpile.External.RSW.RefinedRectangleAvoidance
import Sandpile.External.RSW.WiredKSTClipped

/-!
# A refined dual bridge avoiding a path

An exceptional scale path yields a clipped dual walk across the bridge arcs
whose refined image avoids the refined image of the original path.
-/

namespace Sandpile.External.RSW

/-- A clipped dual bridge obtained from an exceptional path avoids that path. -/
theorem exists_refined_wired_bridge_avoiding_path (k : ℕ) (hk : 12 ≤ k)
    {Q : Finset (Site 2)} {u v : Q} (p : (rectangleGraph Q).Walk u v)
    (hp : p.IsPath) (hsub : ¬ HasKSTSubpath k p)
    (hsubrev : ¬ HasKSTSubpath k p.reverse)
    (hQR : centeredPlaneRectangle (k + k / 12) (k + 1) ⊆ Q) :
    ∃ (a b : centeredPlaneRectangle (k + k / 12 + 1) (k + 1))
      (q : (rectangleGraph (centeredPlaneRectangle (k + k / 12 + 1) (k + 1))).Walk a b),
      ((a : Site 2) 0 = -((k + k / 12 : ℕ) : ℤ) ∨
        ((a : Site 2) 0 ≤ -((k / 12 : ℕ) : ℤ) ∧
          ((a : Site 2) 1 = -(k : ℤ) ∨ (a : Site 2) 1 = k))) ∧
      ((b : Site 2) 0 = ((k + k / 12 : ℕ) : ℤ) ∨
        (((k / 12 : ℕ) : ℤ) ≤ (b : Site 2) 0 ∧
          ((b : Site 2) 1 = -(k : ℤ) ∨ (b : Site 2) 1 = k))) ∧
      (∀ z ∈ q.support, (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k) ∧
      ∀ z ∈ (refinedLatticeWalk 0 (p.map (rectangleGraphToLattice Q))).support,
        z ∉ (refinedLatticeWalk (fun _ => 1)
          (q.map (rectangleGraphToLattice _))).support := by
  classical
  obtain ⟨a, b, q, hq, ha, hb, htop, hbox⟩ :=
    exists_wiredKST_dual_clipped_path_of_no_subpath k hk p hp hsub hsubrev hQR
  have hpo : IsBondOpenWalk (pathBondConfig p) p := by
    apply (isBondOpenWalk_iff_local_edges _ _).mpr
    intro e he
    simp only [pathBondConfig, decide_eq_true_eq, List.mem_map]
    exact ⟨e, he, rfl⟩
  refine ⟨a, b, q, ha, hb, hbox, ?_⟩
  apply refined_wired_rectangle_walk_avoids k (pathBondConfig p) p q hpo hq
  · intro z hz
    have h := (mem_centeredPlaneRectangle _ _ _).mp (hbox z hz)
    exact ⟨h.2.2.1, h.2.2.2⟩
  · exact htop

end Sandpile.External.RSW
