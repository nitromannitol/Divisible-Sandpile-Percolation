/-
The grid-corner construction of `sandpile.tex:2645-2660`, the last planar step of
the dimension-two and dimension-three percolation proof:

  "It is then at least `3c/2` at every point of the grid in the plane that lies
   inside the corresponding rectangle and within distance `2/R_n` of its
   crossing.  These grid points contain the required nearest-neighbor crossings:
   take the corners of the grid squares met by the continuum crossing and, at
   the boundary, use the first grid row or column inside the rectangle."

The continuum crossing is a compact connected set on which the field is at least
`l`; `exists_lattice_walk_of_connected_superlevel` of
`Sandpile/Support/CrossFixBlocking.lean` already turns it into a nearest-neighbour
walk of a mesh-`t` grid whose grid points all carry the field at least `l - η`.
This module records that step in the form the block-crossing argument consumes
it: the walk starts on the left side of the square and ends on the right side.
-/
import Sandpile.Support.CrossFixBlocking

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
