import Sandpile.External.RSW.KSTPathEdges

/-!
# Bond configurations supported on a path

When a bond configuration opens exactly the edges of a simple path, an open
positive-scale KST path is a subpath in one of the two directions.
-/

namespace Sandpile.External.RSW

/-- The bond configuration opening precisely the edges traversed by a walk. -/
noncomputable def pathBondConfig {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b) (edge : Sym2 (Site 2)) : Bool := by
  classical
  exact decide (edge ∈ p.edges.map (Sym2.map Subtype.val))

/-- An open walk in the path-supported configuration uses only its edges. -/
theorem edges_subset_of_open_pathBondConfig {Q : Finset (Site 2)} {a b c d : Q}
    (p : (rectangleGraph Q).Walk a b) (q : (rectangleGraph Q).Walk c d)
    (hq : IsBondOpenWalk (pathBondConfig p) q) : q.edges ⊆ p.edges := by
  classical
  rw [isBondOpenWalk_iff_local_edges] at hq
  intro edge hedge
  have h := hq edge hedge
  simp only [pathBondConfig, decide_eq_true_eq, List.mem_map] at h
  obtain ⟨edge', hedge', heq⟩ := h
  have heq' : edge' = edge := Sym2.map.injective Subtype.val_injective heq
  simpa only [heq'] using hedge'

/-- A scale path open in the configuration of a simple path is a scale subpath
of that path in one of the two orientations. -/
theorem hasKSTSubpath_or_reverse_of_open_pathBondConfig (k : ℕ) (hk : 0 < k)
    {Q : Finset (Site 2)} {a b c d : Q} (p : (rectangleGraph Q).Walk a b)
    (q : (rectangleGraph Q).Walk c d) (hp : p.IsPath) (hq : IsKSTPath k q)
    (hopen : IsBondOpenWalk (pathBondConfig p) q) :
    HasKSTSubpath k p ∨ HasKSTSubpath k p.reverse :=
  hasKSTSubpath_or_reverse_of_edges_subset k hk p q hp hq
    (edges_subset_of_open_pathBondConfig p q hopen)

end Sandpile.External.RSW
