import Sandpile.External.RSW.DualReflection

/-!
# Reflection invariance of dual bonds

Reflection of the dual lattice includes an integer coordinate offset. After restriction to
nearest-neighbor edges, translation invariance removes this offset.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- The dual reflection is primal reflection followed by a unit translation. -/
theorem reflectDualPlaneSite_eq (z : Site 2) :
    reflectDualPlaneSite z = reflectPlaneSite z + (-Pi.single (0 : Fin 2) 1) := by
  ext i
  fin_cases i <;> simp [reflectDualPlaneSite, reflectPlaneSite, sub_eq_add_neg]

/-- Dual reflection preserves lattice adjacency. -/
theorem lattice_adj_reflectDual_plane {x y : Site 2} (h : (lattice 2).Adj x y) :
    (lattice 2).Adj (reflectDualPlaneSite x) (reflectDualPlaneSite y) := by
  rw [reflectDualPlaneSite_eq, reflectDualPlaneSite_eq]
  exact lattice_adj_translate _ (lattice_adj_reflect_plane h)

/-- On lattice edges, the inverse dual correspondence intertwines the two reflections. -/
theorem dualEdgeEquiv_symm_reflect {e : Sym2 (Site 2)}
    (he : e ∈ (LatticeModels.zdGraph 2).edgeSet) :
    dualEdgeEquiv.symm (Sym2.map reflectDualPlaneSite e) =
      Sym2.map reflectPlaneSite (dualEdgeEquiv.symm e) := by
  have he' : dualEdgeEquiv.symm e ∈ (LatticeModels.zdGraph 2).edgeSet := by
    apply (dualEdge_mem_edgeSet_iff _).mp
    rw [← dualEdgeEquiv_apply, dualEdgeEquiv.apply_symm_apply]
    exact he
  apply dualEdgeEquiv.injective
  rw [dualEdgeEquiv.apply_symm_apply, dualEdgeEquiv_apply, dualEdge_reflect he',
    ← dualEdgeEquiv_apply, dualEdgeEquiv.apply_symm_apply]

/-- Restricting the dual configuration to lattice edges. -/
noncomputable def dualPlaneEdges (ω : Sym2 (Site 2) → Bool) : PlaneEdge → Bool :=
  restrictToPlaneEdges (dualBondConfig ω)

/-- Restriction of the dual configuration is measurable. -/
theorem measurable_dualPlaneEdges : Measurable dualPlaneEdges :=
  measurable_restrictToPlaneEdges.comp measurable_dualBondConfig

/-- Primal reflection induces the shifted reflection on the dual edge configuration. -/
theorem dualPlaneEdges_reflect (ω : Sym2 (Site 2) → Bool) :
    dualPlaneEdges (ω ∘ Sym2.map reflectPlaneSite) =
      dualPlaneEdges ω ∘ planeEdgeMap reflectDualPlaneSite
        (fun {_ _} h => lattice_adj_reflectDual_plane h) := by
  funext e
  have he : (e : Sym2 (Site 2)) ∈ (LatticeModels.zdGraph 2).edgeSet := by
    rw [← lattice_eq_zdGraph]
    exact e.property
  simp only [dualPlaneEdges, restrictToPlaneEdges, dualBondConfig, Function.comp_apply,
    planeEdgeMap, dualEdgeEquiv_symm_reflect he]

/-- Reflection invariance transfers to the dual edge law with its shifted reflection. -/
theorem measurePreserving_dualPlaneEdges_shiftedReflect
    (μ : Measure (Sym2 (Site 2) → Bool))
    (hμ : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map reflectPlaneSite) μ μ) :
    MeasurePreserving (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap reflectDualPlaneSite
      (fun {_ _} h => lattice_adj_reflectDual_plane h)) (μ.map dualPlaneEdges)
      (μ.map dualPlaneEdges) := by
  have hm : Measurable (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap reflectDualPlaneSite
      (fun {_ _} h => lattice_adj_reflectDual_plane h)) :=
    Measurable.of_eval (fun e => measurable_pi_apply _)
  refine ⟨hm, ?_⟩
  rw [Measure.map_map hm measurable_dualPlaneEdges]
  have he : (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap reflectDualPlaneSite
      (fun {_ _} h => lattice_adj_reflectDual_plane h)) ∘ dualPlaneEdges =
      dualPlaneEdges ∘ (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map reflectPlaneSite) := by
    funext ω
    exact (dualPlaneEdges_reflect ω).symm
  rw [he, ← Measure.map_map measurable_dualPlaneEdges hμ.measurable, hμ.map_eq]

/-- A translation- and reflection-invariant bond law has a reflection-invariant dual edge law. -/
theorem measurePreserving_dualPlaneEdges_reflect
    (μ : Measure (Sym2 (Site 2) → Bool))
    (hμr : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map reflectPlaneSite) μ μ)
    (hμt : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + Pi.single (0 : Fin 2) 1)) μ μ) :
    MeasurePreserving (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap reflectPlaneSite
      (fun {_ _} h => lattice_adj_reflect_plane h)) (μ.map dualPlaneEdges)
      (μ.map dualPlaneEdges) := by
  let v : Site 2 := Pi.single (0 : Fin 2) 1
  have ht := measurePreserving_dualBondConfig_translate μ v hμt
  have ht' := measurePreserving_restrictToPlaneEdges (μ.map dualBondConfig) (fun z => z + v)
    (fun {_ _} h => lattice_adj_translate v h) ht
  have hmap : (μ.map dualBondConfig).map restrictToPlaneEdges = μ.map dualPlaneEdges := by
    rw [Measure.map_map measurable_restrictToPlaneEdges measurable_dualBondConfig]
    rfl
  rw [hmap] at ht'
  have hr := measurePreserving_dualPlaneEdges_shiftedReflect μ hμr
  have hc := hr.comp ht'
  have hs (z : Site 2) : reflectDualPlaneSite z + v = reflectPlaneSite z := by
    rw [reflectDualPlaneSite_eq]
    change reflectPlaneSite z + (-v) + v = reflectPlaneSite z
    abel
  have he : (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap reflectDualPlaneSite
      (fun {_ _} h => lattice_adj_reflectDual_plane h)) ∘
      (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap (fun z => z + v)
        (fun {_ _} h => lattice_adj_translate v h)) =
      (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap reflectPlaneSite
        (fun {_ _} h => lattice_adj_reflect_plane h)) := by
    funext η e
    change η (planeEdgeMap (fun z => z + v) _ (planeEdgeMap reflectDualPlaneSite _ e)) =
      η (planeEdgeMap reflectPlaneSite _ e)
    congr 1
    apply Subtype.ext
    change Sym2.map (fun z => z + v) (Sym2.map reflectDualPlaneSite e.val) =
      Sym2.map reflectPlaneSite e.val
    rw [Sym2.map_map]
    congr 1
    funext z
    exact hs z
  rwa [he] at hc

end Sandpile.External.RSW
