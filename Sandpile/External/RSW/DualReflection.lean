import Sandpile.External.RSW.DualSwap
import Sandpile.External.RSW.DualTranslation

/-!
# Reflections and the dual lattice

Reflecting the primal lattice acts on dual lattice coordinates by reflection followed by
translation by one unit. This offset reflects the half-integer location of the dual lattice.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Reflection in the vertical axis of the primal lattice. -/
def reflectPlaneSite (z : Site 2) : Site 2 := ![-z 0, z 1]

/-- The action of primal reflection on dual face coordinates. -/
def reflectDualPlaneSite (z : Site 2) : Site 2 := ![-z 0 - 1, z 1]

/-- The dual of a reflected primal edge is the reflected dual edge with its coordinate offset. -/
theorem dualEdge_reflect {e : Sym2 (Site 2)}
    (he : e ∈ (LatticeModels.zdGraph 2).edgeSet) :
    Percolation.Literature.dualEdge (Sym2.map reflectPlaneSite e) =
      Sym2.map reflectDualPlaneSite (Percolation.Literature.dualEdge e) := by
  obtain ⟨x, i, rfl⟩ := mem_edgeSet_zdGraph_iff.mp he
  fin_cases i <;> dsimp only
  · change Percolation.Literature.dualEdge
      (Sym2.map reflectPlaneSite s(x, x + Pi.single (0 : Fin 2) 1)) =
      Sym2.map reflectDualPlaneSite
        (Percolation.Literature.dualEdge s(x, x + Pi.single (0 : Fin 2) 1))
    have h₁ : reflectPlaneSite (x + Pi.single (0 : Fin 2) 1) =
        reflectPlaneSite x - Pi.single (0 : Fin 2) 1 := by
      ext j
      fin_cases j
      · simp [reflectPlaneSite]
        omega
      · simp [reflectPlaneSite]
    have h₂ : reflectDualPlaneSite (x - Pi.single (1 : Fin 2) 1) =
        reflectPlaneSite x - Pi.single (0 : Fin 2) 1 - Pi.single (1 : Fin 2) 1 := by
      ext j
      fin_cases j <;> simp [reflectPlaneSite, reflectDualPlaneSite, Matrix.vecHead, Matrix.vecTail]
    have h₃ : reflectDualPlaneSite x = reflectPlaneSite x - Pi.single (0 : Fin 2) 1 := by
      ext j
      fin_cases j <;> simp [reflectPlaneSite, reflectDualPlaneSite]
    have hd : Percolation.Literature.dualEdge
        s(reflectPlaneSite x, reflectPlaneSite x - Pi.single (0 : Fin 2) 1) =
        s(reflectPlaneSite x - Pi.single (0 : Fin 2) 1 - Pi.single (1 : Fin 2) 1,
          reflectPlaneSite x - Pi.single (0 : Fin 2) 1) := by
      rw [Sym2.eq_swap]
      have hh := dualEdge_horizontal (reflectPlaneSite x - Pi.single (0 : Fin 2) 1)
      have hc : reflectPlaneSite x - Pi.single (0 : Fin 2) 1 + Pi.single (0 : Fin 2) 1 =
          reflectPlaneSite x := by abel
      rw [hc] at hh
      exact hh
    rw [Sym2.map_mk, h₁, hd, dualEdge_horizontal, Sym2.map_mk, h₂, h₃]
  · change Percolation.Literature.dualEdge
      (Sym2.map reflectPlaneSite s(x, x + Pi.single (1 : Fin 2) 1)) =
      Sym2.map reflectDualPlaneSite
        (Percolation.Literature.dualEdge s(x, x + Pi.single (1 : Fin 2) 1))
    have h₁ : reflectPlaneSite (x + Pi.single (1 : Fin 2) 1) =
        reflectPlaneSite x + Pi.single (1 : Fin 2) 1 := by
      ext j
      fin_cases j <;> simp [reflectPlaneSite]
    have h₂ : reflectDualPlaneSite (x - Pi.single (0 : Fin 2) 1) = reflectPlaneSite x := by
      ext j
      fin_cases j <;> simp [reflectPlaneSite, reflectDualPlaneSite]
    have h₃ : reflectDualPlaneSite x = reflectPlaneSite x - Pi.single (0 : Fin 2) 1 := by
      ext j
      fin_cases j <;> simp [reflectPlaneSite, reflectDualPlaneSite]
    rw [Sym2.map_mk, h₁, dualEdge_vertical, dualEdge_vertical, Sym2.map_mk, h₂, h₃,
      Sym2.eq_swap]

end Sandpile.External.RSW
