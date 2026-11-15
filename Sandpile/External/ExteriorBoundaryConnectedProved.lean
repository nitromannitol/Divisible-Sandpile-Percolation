import Sandpile.External.ExteriorBoundaryConnected
import LatticeProb.Lattice.Planar.ExteriorBoundaryConnected

/-! # Exterior-boundary connectivity -/

/-- Timár's exterior-boundary connectivity theorem for the lattice. -/
theorem Sandpile.External.exteriorBoundaryConnected_holds :
    Sandpile.External.ExteriorBoundaryConnected :=
  fun d hd D hD hc =>
    LatticeProb.Lattice.Planar.exteriorVertexBoundary_connected (d := d) (D := D) hd hD hc
