import Sandpile.External.Stopping.LatticeCubeGeometry
import LatticeProb.Graph.Boundary

/-!
# Scaled lattice cube boundaries

A boundary vertex of a lattice cube is within one rescaled lattice step of
the complement of the open unit cube. This supplies the boundary error in
regular-exit convergence of interpolated lattice paths.
-/

open Metric Set

namespace Sandpile.External.Stopping

/-- Adjacent lattice sites are at distance at most one lattice spacing after
centering and rescaling. -/
theorem dist_centeredScaledSite_le_of_adj {d : ℕ} {R : ℝ} (hR : 0 < R)
    (q : Site d) {v w : Site d} (hvw : (LatticeProb.lattice d).Adj v w) :
    dist (centeredScaledSite R q v) (centeredScaledSite R q w) ≤ 1 / R := by
  obtain ⟨i, hi⟩ := LatticeProb.Graph.Zd.adj_iff.mp hvw
  have hu : LatticeProb.graphNorm (unit i : Site d) = 1 := by
    rw [← LatticeProb.dirVec_eq_unit i, LatticeProb.graphNorm_dirVec]
  have hnorm : LatticeProb.graphNorm (v - w) = 1 := by
    rcases hi with hi | hi
    · have heq : v - w = -(unit i : Site d) := by rw [hi]; abel
      simpa [heq, LatticeProb.graphNorm_neg] using hu
    · have heq : v - w = unit i := by rw [hi]; abel
      simpa [heq] using hu
  have heq : (v - q) - (w - q) = v - w := by abel
  have h := norm_scaledSite_sub_le_graphNorm R hR (v - q) (w - q)
  simpa only [centeredScaledSite, dist_eq_norm, heq, hnorm, Nat.cast_one] using h

/-- A rescaled inner-boundary vertex is within `1 / R` of the complement of
the centered open unit cube. -/
theorem infDist_centeredScaledSite_innerBoundary_le {d : ℕ} {R : ℝ} (hR : 0 < R)
    {q v : Site d} (hv : v ∈ LatticeProb.Graph.innerBoundary (LatticeProb.lattice d) (supBox q R)) :
    infDist (centeredScaledSite R q v) (openUnitCube (0 : Continuum.Space d))ᶜ ≤ 1 / R := by
  obtain ⟨_, w, hw, hvw⟩ := hv
  have hw' : centeredScaledSite R q w ∈ (openUnitCube (0 : Continuum.Space d))ᶜ :=
    centeredScaledSite_not_mem_openUnitCube hR hw
  exact (infDist_le_dist_of_mem hw').trans (dist_centeredScaledSite_le_of_adj hR q hvw)

end Sandpile.External.Stopping
