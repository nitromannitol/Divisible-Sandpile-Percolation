import Sandpile.Support.CrossFixBlocking

/-!
# Grid points on a continuum crossing

The last planar step of the percolation proof at `sandpile.tex:2645-2660`: a continuum
left-right crossing at level `l` is a compact connected set on which the field is at least `l`,
and `exists_lattice_walk_of_connected_superlevel` already turns it into a nearest-neighbour walk
of a mesh-`t` grid whose vertices all carry the field at least `l - η`. This file records that
walk in the form the block-crossing argument consumes it, starting on the left side of the
square and ending on the right side.
-/

open MeasureTheory Set
namespace Sandpile.Support
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A continuum left-right crossing of the plane square at level `l` carries a
nearest-neighbour lattice walk of the mesh-`t` grid from the left side to the
right side, whose grid points all have field value at least `l - η`. -/
theorem perc_lattice_walk_of_crosses {s η l : ℝ} (_hs : 0 < s) (hη : 0 < η)
    {X : Sandpile.Continuum.Space 2 → ℝ} (hX : Continuous X)
    (hcross : Crosses ![0, 0] ![s, s] 0 {u | l ≤ X u}) :
    ∃ (t : ℝ) (x y : Sandpile.Continuum.Space 2)
      (p : (lattice 2).Walk (roundSite t x) (roundSite t y)),
      0 < t ∧ x 0 = 0 ∧ y 0 = s ∧
      ∀ j ≤ p.length, l - η ≤ X (gridPt t (p.getVert j)) := by
  obtain ⟨Γ, hsub, hcomp, hconn, ⟨x, hxΓ, hx0⟩, ⟨y, hyΓ, hy0⟩⟩ := hcross
  obtain ⟨t, p, ht, hp⟩ :=
    exists_lattice_walk_of_connected_superlevel hX hcomp hconn hη
      (fun u hu => (hsub hu).1) hxΓ hyΓ
  exact ⟨t, x, y, p, ht, hx0, hy0, hp⟩

end Sandpile.Support
