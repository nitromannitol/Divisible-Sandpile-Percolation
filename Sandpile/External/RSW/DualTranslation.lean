import Sandpile.External.RSW.DualLaw
import Sandpile.Support.GridRectangle

/-!
# Translation invariance of the dual law

The primal-dual correspondence commutes with lattice translations, so the dual of a
translation-invariant bond law is translation invariant.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Translating an unordered pair commutes with taking its dual edge. -/
theorem dualEdge_translate (v : Site 2) (e : Sym2 (Site 2)) :
    dualEdge (Sym2.map (fun z => z + v) e) =
      Sym2.map (fun z => z + v) (dualEdge e) := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Sym2.map_mk]
    by_cases hxy : (lattice 2).Adj x y
    · obtain ⟨i, hi | hi⟩ := hxy
      · subst y
        simp only [LatticeProb.unit]
        fin_cases i <;> dsimp only
        · change dualEdge s(x + v, x + Pi.single (0 : Fin 2) 1 + v) =
            Sym2.map (fun z => z + v) (dualEdge s(x, x + Pi.single (0 : Fin 2) 1))
          have he : x + Pi.single (0 : Fin 2) 1 + v = (x + v) + Pi.single 0 1 := by
            abel
          rw [he, dualEdge_horizontal, dualEdge_horizontal, Sym2.map_mk]
          congr 1; abel
        · change dualEdge s(x + v, x + Pi.single (1 : Fin 2) 1 + v) =
            Sym2.map (fun z => z + v) (dualEdge s(x, x + Pi.single (1 : Fin 2) 1))
          have he : x + Pi.single (1 : Fin 2) 1 + v = (x + v) + Pi.single 1 1 := by
            abel
          rw [he, dualEdge_vertical, dualEdge_vertical, Sym2.map_mk]
          congr 1; abel
      · subst x
        simp only [LatticeProb.unit]
        rw [Sym2.eq_swap (a := y + Pi.single i 1 + v),
          Sym2.eq_swap (a := y + Pi.single i 1)]
        fin_cases i <;> dsimp only
        · change dualEdge s(y + v, y + Pi.single (0 : Fin 2) 1 + v) =
            Sym2.map (fun z => z + v) (dualEdge s(y, y + Pi.single (0 : Fin 2) 1))
          have he : y + Pi.single (0 : Fin 2) 1 + v = (y + v) + Pi.single 0 1 := by
            abel
          rw [he, dualEdge_horizontal, dualEdge_horizontal, Sym2.map_mk]
          congr 1; abel
        · change dualEdge s(y + v, y + Pi.single (1 : Fin 2) 1 + v) =
            Sym2.map (fun z => z + v) (dualEdge s(y, y + Pi.single (1 : Fin 2) 1))
          have he : y + Pi.single (1 : Fin 2) 1 + v = (y + v) + Pi.single 1 1 := by
            abel
          rw [he, dualEdge_vertical, dualEdge_vertical, Sym2.map_mk]
          congr 1; abel
    · have hne : s(x, y) ∉ (LatticeModels.zdGraph 2).edgeSet := by
        rw [← lattice_eq_zdGraph, SimpleGraph.mem_edgeSet]
        exact hxy
      have hne' : s(x + v, y + v) ∉ (LatticeModels.zdGraph 2).edgeSet := by
        rw [← lattice_eq_zdGraph, SimpleGraph.mem_edgeSet]
        intro h
        have hh := lattice_adj_translate (-v) h
        simp only [add_neg_cancel_right] at hh
        exact hxy hh
      rw [dualEdge_of_not_mem hne', dualEdge_of_not_mem hne, Sym2.map_mk]

/-- The inverse primal-dual edge correspondence commutes with translations. -/
theorem dualEdgeEquiv_symm_translate (v : Site 2) (e : Sym2 (Site 2)) :
    dualEdgeEquiv.symm (Sym2.map (fun z => z + v) e) =
      Sym2.map (fun z => z + v) (dualEdgeEquiv.symm e) := by
  apply dualEdgeEquiv.injective
  rw [dualEdgeEquiv.apply_symm_apply, dualEdgeEquiv_apply, dualEdge_translate,
    ← dualEdgeEquiv_apply, dualEdgeEquiv.apply_symm_apply]

/-- The dual configuration commutes with translations. -/
theorem dualBondConfig_translate (v : Site 2) (ω : Sym2 (Site 2) → Bool) :
    dualBondConfig (ω ∘ Sym2.map (fun z => z + v)) =
      dualBondConfig ω ∘ Sym2.map (fun z => z + v) := by
  funext e
  simp only [dualBondConfig, Function.comp_apply, dualEdgeEquiv_symm_translate]

/-- A translation-invariant bond law has a translation-invariant dual law. -/
theorem measurePreserving_dualBondConfig_translate
    (μ : Measure (Sym2 (Site 2) → Bool)) (v : Site 2)
    (hμ : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ) :
    MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + v))
      (μ.map dualBondConfig) (μ.map dualBondConfig) := by
  have hm : Measurable (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + v)) :=
    Measurable.of_eval (fun e => measurable_pi_apply _)
  refine ⟨hm, ?_⟩
  rw [Measure.map_map hm measurable_dualBondConfig]
  have he : (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + v)) ∘
      dualBondConfig = dualBondConfig ∘
        (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + v)) := by
    funext ω
    exact (dualBondConfig_translate v ω).symm
  rw [he, ← Measure.map_map measurable_dualBondConfig hμ.measurable, hμ.map_eq]

end Sandpile.External.RSW
