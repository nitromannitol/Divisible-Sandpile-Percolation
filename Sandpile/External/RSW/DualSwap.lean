import Sandpile.External.RSW.DualLaw
import Sandpile.External.RSW.EdgeSymmetry

/-!
# Coordinate interchange for the dual law

Interchanging the coordinates commutes with the planar bond duality correspondence.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Interchanging the two coordinates of a planar site. -/
def swapPlaneSite (z : Site 2) : Site 2 := ![z 1, z 0]

/-- Coordinate interchange is an involution. -/
theorem swapPlaneSite_involutive : Function.Involutive swapPlaneSite := by
  intro z
  ext i
  fin_cases i <;> rfl

/-- Coordinate interchange commutes with the planar dual-edge correspondence. -/
theorem dualEdge_swap (e : Sym2 (Site 2)) :
    Percolation.Literature.dualEdge (Sym2.map swapPlaneSite e) =
      Sym2.map swapPlaneSite (Percolation.Literature.dualEdge e) := by
  by_cases he : e ∈ (LatticeModels.zdGraph 2).edgeSet
  · obtain ⟨x, i, rfl⟩ := mem_edgeSet_zdGraph_iff.mp he
    fin_cases i <;> dsimp only
    · change Percolation.Literature.dualEdge (Sym2.map swapPlaneSite s(x, x + Pi.single (0 : Fin 2) 1)) =
        Sym2.map swapPlaneSite (Percolation.Literature.dualEdge s(x, x + Pi.single (0 : Fin 2) 1))
      have h₁ : swapPlaneSite (x + Pi.single (0 : Fin 2) 1) =
          swapPlaneSite x + Pi.single (1 : Fin 2) 1 := by
        ext j
        fin_cases j <;> simp [swapPlaneSite]
      have h₂ : swapPlaneSite (x - Pi.single (1 : Fin 2) 1) =
          swapPlaneSite x - Pi.single (0 : Fin 2) 1 := by
        ext j
        fin_cases j <;> simp [swapPlaneSite]
      rw [Sym2.map_mk, h₁, dualEdge_vertical, dualEdge_horizontal, Sym2.map_mk, h₂]
    · change Percolation.Literature.dualEdge (Sym2.map swapPlaneSite s(x, x + Pi.single (1 : Fin 2) 1)) =
        Sym2.map swapPlaneSite (Percolation.Literature.dualEdge s(x, x + Pi.single (1 : Fin 2) 1))
      have h₁ : swapPlaneSite (x + Pi.single (1 : Fin 2) 1) =
          swapPlaneSite x + Pi.single (0 : Fin 2) 1 := by
        ext j
        fin_cases j <;> simp [swapPlaneSite]
      have h₂ : swapPlaneSite (x - Pi.single (0 : Fin 2) 1) =
          swapPlaneSite x - Pi.single (1 : Fin 2) 1 := by
        ext j
        fin_cases j <;> simp [swapPlaneSite]
      rw [Sym2.map_mk, h₁, dualEdge_horizontal, dualEdge_vertical, Sym2.map_mk, h₂]
  · have hm : Sym2.map swapPlaneSite e ∉ (LatticeModels.zdGraph 2).edgeSet := by
      induction e using Sym2.ind with
      | _ x y =>
        simp only [Sym2.map_mk, ← lattice_eq_zdGraph, SimpleGraph.mem_edgeSet] at he ⊢
        intro h
        have hh := lattice_adj_swap_plane h
        change (lattice 2).Adj (swapPlaneSite (swapPlaneSite x))
          (swapPlaneSite (swapPlaneSite y)) at hh
        rw [swapPlaneSite_involutive, swapPlaneSite_involutive] at hh
        exact he hh
    rw [dualEdge_of_not_mem hm, dualEdge_of_not_mem he]

/-- The inverse dual-edge correspondence commutes with coordinate interchange. -/
theorem dualEdgeEquiv_symm_swap (e : Sym2 (Site 2)) :
    dualEdgeEquiv.symm (Sym2.map swapPlaneSite e) =
      Sym2.map swapPlaneSite (dualEdgeEquiv.symm e) := by
  apply dualEdgeEquiv.injective
  rw [dualEdgeEquiv.apply_symm_apply, dualEdgeEquiv_apply, dualEdge_swap,
    ← dualEdgeEquiv_apply, dualEdgeEquiv.apply_symm_apply]

/-- The dual configuration commutes with coordinate interchange. -/
theorem dualBondConfig_swap (ω : Sym2 (Site 2) → Bool) :
    dualBondConfig (ω ∘ Sym2.map swapPlaneSite) = dualBondConfig ω ∘ Sym2.map swapPlaneSite := by
  funext e
  simp only [dualBondConfig, Function.comp_apply, dualEdgeEquiv_symm_swap]

/-- A coordinate-interchange-invariant bond law has an invariant dual law. -/
theorem measurePreserving_dualBondConfig_swap (μ : Measure (Sym2 (Site 2) → Bool))
    (hμ : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map swapPlaneSite) μ μ) :
    MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map swapPlaneSite)
      (μ.map dualBondConfig) (μ.map dualBondConfig) := by
  have hm : Measurable (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map swapPlaneSite) :=
    Measurable.of_eval (fun e => measurable_pi_apply _)
  refine ⟨hm, ?_⟩
  rw [Measure.map_map hm measurable_dualBondConfig]
  have he : (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map swapPlaneSite) ∘ dualBondConfig =
      dualBondConfig ∘ (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map swapPlaneSite) := by
    funext ω
    exact (dualBondConfig_swap ω).symm
  rw [he, ← Measure.map_map measurable_dualBondConfig hμ.measurable, hμ.map_eq]

end Sandpile.External.RSW
