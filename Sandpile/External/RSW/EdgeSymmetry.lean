import Sandpile.External.RSW.EdgeCarrier
import Sandpile.External.RSW.BondSymmetry
import Sandpile.Support.GridRectangle
import Sandpile.Support.WalkRay

/-!
# Lattice symmetries of the induced edge law

Translations, coordinate interchange, and reflection preserve nearest-neighbor adjacency and
hence act on the nearest-neighbor bond law induced by a symmetric field.
-/

open LatticeProb MeasureTheory

namespace Sandpile.External.RSW

/-- Coordinate interchange preserves square-lattice adjacency. -/
theorem lattice_adj_swap_plane {x y : Site 2} (h : (lattice 2).Adj x y) :
    (lattice 2).Adj ![x 1, x 0] ![y 1, y 0] := by
  simpa only [permuteSite_swap_plane] using
    (lattice_adj_permute (Equiv.swap (0 : Fin 2) 1) h)

/-- Reflection in the vertical axis preserves square-lattice adjacency. -/
theorem lattice_adj_reflect_plane {x y : Site 2} (h : (lattice 2).Adj x y) :
    (lattice 2).Adj ![-x 0, x 1] ![-y 0, y 1] := by
  obtain h | h | h | h := lattice_two_adj_cases h
  · refine ⟨0, Or.inr ?_⟩
    ext i
    fin_cases i <;> simp [unit] <;> omega
  · refine ⟨0, Or.inl ?_⟩
    ext i
    fin_cases i <;> simp [unit] <;> omega
  · refine ⟨1, Or.inl ?_⟩
    ext i
    fin_cases i <;> simp [unit] <;> omega
  · refine ⟨1, Or.inr ?_⟩
    ext i
    fin_cases i <;> simp [unit] <;> omega

/-- The edge law induced by a symmetric field is invariant under the three generating
symmetries of the square lattice. -/
theorem fieldPlaneEdgeLaw_symmetric (μ : Measure (Site 2 → ℝ))
    (hμ : IsSymmetricPlanarLaw μ) (level : ℝ) :
    (∀ v : Site 2, MeasurePreserving
      (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap (fun z => z + v)
        (fun {_ _} h => lattice_adj_translate v h))
      ((fieldBondLaw μ level).map restrictToPlaneEdges)
      ((fieldBondLaw μ level).map restrictToPlaneEdges)) ∧
    MeasurePreserving
      (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap (fun z => ![z 1, z 0])
        (fun {_ _} h => lattice_adj_swap_plane h))
      ((fieldBondLaw μ level).map restrictToPlaneEdges)
      ((fieldBondLaw μ level).map restrictToPlaneEdges) ∧
    MeasurePreserving
      (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap (fun z => ![-z 0, z 1])
        (fun {_ _} h => lattice_adj_reflect_plane h))
      ((fieldBondLaw μ level).map restrictToPlaneEdges)
      ((fieldBondLaw μ level).map restrictToPlaneEdges) := by
  obtain ⟨ht, hs, hr⟩ := fieldBondLaw_symmetric μ hμ level
  exact ⟨fun v => measurePreserving_restrictToPlaneEdges _ _ _ (ht v),
    measurePreserving_restrictToPlaneEdges _ _ _ hs,
    measurePreserving_restrictToPlaneEdges _ _ _ hr⟩

end Sandpile.External.RSW
