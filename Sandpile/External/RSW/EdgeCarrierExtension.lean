import Sandpile.External.RSW.EdgeCarrierBridge

/-!
# Extending lattice-edge laws

Closing nonedges extends a nearest-neighbor bond law to all unordered site pairs. The
extension preserves association and adjacency-preserving lattice symmetries.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- Closing nonedges preserves the coordinatewise order. -/
theorem monotone_extendPlaneEdges : Monotone extendPlaneEdges := by
  classical
  intro η ξ h e
  by_cases he : e ∈ (lattice 2).edgeSet
  · simp only [extendPlaneEdges, dite_eq_left he]
    exact h ⟨e, he⟩
  · simp only [extendPlaneEdges, dite_eq_right he, le_refl]

/-- Extension of an associated nearest-neighbor law remains associated. -/
theorem extendPlaneEdges_associated (μ : Measure (PlaneEdge → Bool))
    (hμ : ∀ A B : Set (PlaneEdge → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    {A B : Set (Sym2 (Site 2) → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (μ.map extendPlaneEdges).real A * (μ.map extendPlaneEdges).real B ≤
      (μ.map extendPlaneEdges).real (A ∩ B) := by
  have ha : IsUpperSet (extendPlaneEdges ⁻¹' A) :=
    fun _ _ hω h => hA (monotone_extendPlaneEdges hω) h
  have hb : IsUpperSet (extendPlaneEdges ⁻¹' B) :=
    fun _ _ hω h => hB (monotone_extendPlaneEdges hω) h
  have hh := hμ _ _ ha hb (hAm.preimage measurable_extendPlaneEdges)
    (hBm.preimage measurable_extendPlaneEdges)
  simpa only [Measure.real, Measure.map_apply measurable_extendPlaneEdges hAm,
    Measure.map_apply measurable_extendPlaneEdges hBm,
    Measure.map_apply measurable_extendPlaneEdges (hAm.inter hBm), preimage_inter] using hh

/-- Extension commutes with any site map that preserves and reflects adjacency. -/
theorem extendPlaneEdges_reindex (g : Site 2 → Site 2)
    (hg : ∀ x y, (lattice 2).Adj (g x) (g y) ↔ (lattice 2).Adj x y)
    (η : PlaneEdge → Bool) :
    extendPlaneEdges (η ∘ planeEdgeMap g (fun {_ _} h => (hg _ _).2 h)) =
      extendPlaneEdges η ∘ Sym2.map g := by
  classical
  funext e
  have hmap : Sym2.map g e ∈ (lattice 2).edgeSet ↔ e ∈ (lattice 2).edgeSet := by
    induction e using Sym2.ind with
    | _ x y => simpa only [Sym2.map_mk, SimpleGraph.mem_edgeSet] using hg x y
  by_cases he : e ∈ (lattice 2).edgeSet
  · have he' : Sym2.map g e ∈ (lattice 2).edgeSet := hmap.mpr he
    simp only [extendPlaneEdges, dite_eq_left he, dite_eq_left he', Function.comp_apply,
      planeEdgeMap]
  · have he' : Sym2.map g e ∉ (lattice 2).edgeSet := fun h => he (hmap.mp h)
    simp only [extendPlaneEdges, dite_eq_right he, dite_eq_right he', Function.comp_apply]

/-- An invariant edge law has an invariant extension to all unordered pairs. -/
theorem measurePreserving_extendPlaneEdges (μ : Measure (PlaneEdge → Bool))
    (g : Site 2 → Site 2)
    (hg : ∀ x y, (lattice 2).Adj (g x) (g y) ↔ (lattice 2).Adj x y)
    (hμ : MeasurePreserving (fun η : PlaneEdge → Bool =>
      η ∘ planeEdgeMap g (fun {_ _} h => (hg _ _).2 h)) μ μ) :
    MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map g)
      (μ.map extendPlaneEdges) (μ.map extendPlaneEdges) := by
  have hm : Measurable (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map g) :=
    Measurable.of_eval (fun e => measurable_pi_apply _)
  refine ⟨hm, ?_⟩
  rw [Measure.map_map hm measurable_extendPlaneEdges]
  have he : (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map g) ∘ extendPlaneEdges =
      extendPlaneEdges ∘ (fun η : PlaneEdge → Bool =>
        η ∘ planeEdgeMap g (fun {_ _} h => (hg _ _).2 h)) := by
    funext η
    exact (extendPlaneEdges_reindex g hg η).symm
  rw [he, ← Measure.map_map measurable_extendPlaneEdges hμ.measurable, hμ.map_eq]

end Sandpile.External.RSW
