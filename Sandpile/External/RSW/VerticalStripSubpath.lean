import Sandpile.External.RSW.FirstRectangleExit
import Sandpile.External.RSW.LastEntryFirstExit
import Sandpile.External.RSW.QuasiCrossing

/-!
# Vertical strip subpaths

A lattice path crossing two horizontal lines contains a contiguous crossing of the
strip between them. Its vertices remain in the support of the original path.
-/

open Percolation.Literature

namespace Sandpile.External.RSW

/-- A rectangle walk crossing a horizontal line visits a vertex on that line. -/
theorem rectangle_walk_exists_height {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b) (t : ℤ)
    (ha : (a : Site 2) 1 ≤ t) (hb : t ≤ (b : Site 2) 1) :
    ∃ z ∈ p.support, (z : Site 2) 1 = t := by
  let f : rectangleGraph Q →g LatticeModels.zdGraph 2 :=
    ⟨Subtype.val, fun h => by rw [← lattice_eq_zdGraph]; exact h⟩
  obtain ⟨z, hz, hzt⟩ := exists_mem_support_apply_eq (p.map f) 1 t ha hb
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
  obtain ⟨v, hv, rfl⟩ := hz
  exact ⟨v, hv, hzt⟩

/-- A path crossing a vertical strip has a contiguous path confined to the strip. -/
theorem exists_vertical_strip_subpath {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b) (hp : p.IsPath) {B T : ℤ} (hBT : B < T)
    (ha : T ≤ (a : Site 2) 1) (hb : (b : Site 2) 1 ≤ B) :
    ∃ (c d : Q) (q : (rectangleGraph Q).Walk c d),
      q.IsSubwalk p ∧ q.IsPath ∧ (c : Site 2) 1 = T ∧ (d : Site 2) 1 = B ∧
      ∀ z ∈ q.support, B ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ T := by
  classical
  let A : Q → Prop := fun z => T ≤ (z : Site 2) 1
  let D : Q → Prop := fun z => (z : Site 2) 1 ≤ B
  obtain ⟨c, d, q, hsub, hc, hd, hends⟩ :=
    exists_subwalk_between_disjoint_sets A D (by intro z hz hz'; dsimp [A, D] at *; omega)
      p ha hb
  have hcrest : T ≤ (c : Site 2) 1 := hc
  have hdrest : (d : Site 2) 1 ≤ B := hd
  obtain ⟨u, hu, huT⟩ := rectangle_walk_exists_height q.reverse T (by omega) hcrest
  have huq : u ∈ q.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hu
  have huC : u = c := (hends u huq).1 (by dsimp [A]; omega)
  have hcT : (c : Site 2) 1 = T := by simpa only [huC] using huT
  obtain ⟨v, hv, hvB⟩ := rectangle_walk_exists_height q.reverse B hdrest (by omega)
  have hvq : v ∈ q.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hv
  have hvD : v = d := (hends v hvq).2 (by dsimp [D]; omega)
  have hdB : (d : Site 2) 1 = B := by simpa only [hvD] using hvB
  refine ⟨c, d, q, hsub, SimpleGraph.Walk.isPath_of_isSubwalk hsub hp, hcT, hdB, ?_⟩
  intro z hz
  constructor
  · by_contra hn
    have heq : z = d := (hends z hz).2 (by dsimp [D]; omega)
    have := congrArg (fun x : Q => (x : Site 2) 1) heq
    omega
  · by_contra hn
    have heq : z = c := (hends z hz).1 (by dsimp [A]; omega)
    have := congrArg (fun x : Q => (x : Site 2) 1) heq
    omega

end Sandpile.External.RSW
