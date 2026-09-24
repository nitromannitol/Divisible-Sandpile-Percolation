/-
External input from Timár, Boundary-connectivity via graph theory,
Theorem 3 (arXiv 0711.1713v2, page 5), cited at `sandpile.tex:6600` in
`lem:dgt4-blocking-to-crossing`.

This is the lattice specialization for finite star-connected sets in dimension
at least two. The exterior boundary uses nearest-neighbor adjacency and simple
nearest-neighbor paths to infinity in the complement, as in the source's
boundary definition on page 2. Both induced-graph connectivity predicates
include nonemptiness. The diameter and annular crossing consequences are
proved separately and are not part of this input.
-/
import Sandpile.Support.ExteriorBoundary

-- FROZEN-STATEMENT-BEGIN
/-- Timár's exterior-boundary connectivity theorem on the lattice.
Assumed, not proved. -/
def Sandpile.External.ExteriorBoundaryConnected : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ D : Set (Sandpile.Site d), D.Finite →
    ((Sandpile.starLatticeGraph d).induce D).Connected →
    ((Sandpile.starLatticeGraph d).induce (Sandpile.exteriorVertexBoundary D)).Connected
-- FROZEN-STATEMENT-END
