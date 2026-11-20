import Sandpile.External.RSW.EdgeCarrierBridge
import Sandpile.External.RSW.DualTranslation

/-!
# Double duality of bond laws

With lower-left face coordinates, taking the dual twice translates lattice edges by
one unit in each coordinate. Translation invariance restores bridge probabilities.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Applying the inverse dual-edge correspondence twice translates a lattice edge by
one unit in both coordinates. -/
theorem dualEdgeEquiv_symm_symm {e : Sym2 (Site 2)}
    (he : e ∈ (LatticeModels.zdGraph 2).edgeSet) :
    dualEdgeEquiv.symm (dualEdgeEquiv.symm e) = Sym2.map (fun z => z + 1) e := by
  have hplus : Sym2.map (fun z : Site 2 => z + 1) e ∈ (LatticeModels.zdGraph 2).edgeSet := by
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Sym2.map_mk, SimpleGraph.mem_edgeSet] at he ⊢
      rw [← lattice_eq_zdGraph] at he ⊢
      exact lattice_adj_translate 1 he
  have hh : dualEdgeEquiv (dualEdgeEquiv (Sym2.map (fun z : Site 2 => z + 1) e)) = e := by
    change Percolation.Literature.dualEdge (Percolation.Literature.dualEdge (Sym2.map (fun z : Site 2 => z + 1) e)) = e
    rw [dualEdge_dualEdge_holds hplus, Sym2.map_map]
    have hf : (fun z : Site 2 => (z + 1) - 1) = id := by
      funext z
      simp only [add_sub_cancel_right, id_eq]
    change Sym2.map (fun z : Site 2 => (z + 1) - 1) e = e
    rw [hf, Sym2.map_id, id_eq]
  apply dualEdgeEquiv.injective
  apply dualEdgeEquiv.injective
  rw [dualEdgeEquiv.apply_symm_apply, dualEdgeEquiv.apply_symm_apply, hh]

/-- Double duality agrees with translation on every nearest-neighbor bond. -/
theorem dualBondConfig_double_apply (ω : Sym2 (Site 2) → Bool) {e : Sym2 (Site 2)}
    (he : e ∈ (LatticeModels.zdGraph 2).edgeSet) :
    dualBondConfig (dualBondConfig ω) e = ω (Sym2.map (fun z => z + 1) e) := by
  simp only [dualBondConfig, Bool.not_not, dualEdgeEquiv_symm_symm he]

/-- Restricting a double dual configuration to lattice edges gives its translated
restriction. -/
theorem restrictToPlaneEdges_double_dual (ω : Sym2 (Site 2) → Bool) :
    restrictToPlaneEdges (dualBondConfig (dualBondConfig ω)) =
      restrictToPlaneEdges (ω ∘ Sym2.map (fun z => z + 1)) := by
  funext e
  change dualBondConfig (dualBondConfig ω) e = ω (Sym2.map (fun z => z + 1) e)
  apply dualBondConfig_double_apply
  rw [← lattice_eq_zdGraph]
  exact e.property

/-- Double duality preserves all lattice-edge event probabilities for a translation-invariant
bond law. -/
theorem map_doubleDual_restrictToPlaneEdges (μ : Measure (Sym2 (Site 2) → Bool))
    (ht : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + 1)) μ μ) :
    ((μ.map dualBondConfig).map dualBondConfig).map restrictToPlaneEdges =
      μ.map restrictToPlaneEdges := by
  have he : restrictToPlaneEdges ∘ (dualBondConfig ∘ dualBondConfig) =
      restrictToPlaneEdges ∘ (fun ω : Sym2 (Site 2) → Bool =>
        ω ∘ Sym2.map (fun z => z + 1)) := by
    funext ω
    exact restrictToPlaneEdges_double_dual ω
  calc
    _ = μ.map (restrictToPlaneEdges ∘ (dualBondConfig ∘ dualBondConfig)) := by
      rw [Measure.map_map measurable_restrictToPlaneEdges measurable_dualBondConfig,
        Measure.map_map (measurable_restrictToPlaneEdges.comp measurable_dualBondConfig)
          measurable_dualBondConfig]
      rfl
    _ = μ.map (restrictToPlaneEdges ∘ (fun ω : Sym2 (Site 2) → Bool =>
          ω ∘ Sym2.map (fun z => z + 1))) := by rw [he]
    _ = (μ.map (fun ω : Sym2 (Site 2) → Bool =>
          ω ∘ Sym2.map (fun z => z + 1))).map restrictToPlaneEdges := by
      rw [Measure.map_map measurable_restrictToPlaneEdges ht.measurable]
    _ = μ.map restrictToPlaneEdges := by rw [ht.map_eq]

/-- A translation-invariant bond law and its double dual have the same bridge probability. -/
theorem measureReal_doubleDual_kstBridge (μ : Measure (Sym2 (Site 2) → Bool))
    (ht : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + 1)) μ μ) (m : ℕ) :
    ((μ.map dualBondConfig).map dualBondConfig).real (kstBridgeEvent m) =
      μ.real (kstBridgeEvent m) := by
  rw [← restrictToPlaneEdges_kstBridge ((μ.map dualBondConfig).map dualBondConfig) m,
    ← restrictToPlaneEdges_kstBridge μ m, map_doubleDual_restrictToPlaneEdges μ ht]

end Sandpile.External.RSW
