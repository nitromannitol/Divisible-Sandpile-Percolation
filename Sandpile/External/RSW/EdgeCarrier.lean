import Sandpile.External.RSW.FieldBondLaw

/-!
# Nearest-neighbor bond configurations

Rectangle crossings use only edges of the square lattice. Restricting an all-pairs bond law to
these edges preserves association and crossing probabilities.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- The unoriented nearest-neighbor edges of the square lattice. -/
abbrev PlaneEdge := (lattice 2).edgeSet

/-- Restriction of an all-pairs configuration to nearest-neighbor edges. -/
def restrictToPlaneEdges (ω : Sym2 (Site 2) → Bool) : PlaneEdge → Bool :=
  fun e => ω e

/-- Extend a nearest-neighbor edge configuration by closing all other pairs. -/
noncomputable def extendPlaneEdges (η : PlaneEdge → Bool) (e : Sym2 (Site 2)) : Bool := by
  classical
  exact if h : e ∈ (lattice 2).edgeSet then η ⟨e, h⟩ else false

/-- Restricting a configuration to lattice edges is measurable. -/
theorem measurable_restrictToPlaneEdges : Measurable restrictToPlaneEdges :=
  Measurable.of_eval (fun e => measurable_pi_apply e.val)

/-- Extending a lattice-edge configuration is measurable. -/
theorem measurable_extendPlaneEdges : Measurable extendPlaneEdges := by
  classical
  apply Measurable.of_eval
  intro e
  by_cases h : e ∈ (lattice 2).edgeSet
  · simpa only [extendPlaneEdges, dite_eq_left h] using
      (measurable_pi_apply (⟨e, h⟩ : PlaneEdge))
  · simpa only [extendPlaneEdges, dite_eq_right h] using
      (measurable_const : Measurable (fun _ : PlaneEdge → Bool => false))

/-- Restriction is monotone with respect to edge states. -/
theorem monotone_restrictToPlaneEdges : Monotone restrictToPlaneEdges :=
  fun _ _ h e => h e.val

/-- The extension agrees with the original configuration on lattice edges. -/
theorem extend_restrict_planeEdge (ω : Sym2 (Site 2) → Bool) (e : PlaneEdge) :
    extendPlaneEdges (restrictToPlaneEdges ω) e = ω e := by
  classical
  simp only [extendPlaneEdges, dite_eq_left e.property, restrictToPlaneEdges]

/-- A rectangle walk has the same open status after restriction to lattice edges. -/
theorem isBondOpenWalk_extend_restrict {Q : Finset (Site 2)}
    (ω : Sym2 (Site 2) → Bool) {a b : Q} (p : (rectangleGraph Q).Walk a b) :
    IsBondOpenWalk (extendPlaneEdges (restrictToPlaneEdges ω)) p ↔ IsBondOpenWalk ω p := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
    have he : s((a : Site 2), (b : Site 2)) ∈ (lattice 2).edgeSet :=
      ((lattice 2).mem_edgeSet).mpr hab
    change (extendPlaneEdges (restrictToPlaneEdges ω) s((a : Site 2), (b : Site 2)) = true ∧
      IsBondOpenWalk (extendPlaneEdges (restrictToPlaneEdges ω)) p) ↔
      (ω s((a : Site 2), (b : Site 2)) = true ∧ IsBondOpenWalk ω p)
    rw [extend_restrict_planeEdge ω ⟨_, he⟩, ih]

/-- The crossing event on nearest-neighbor edge configurations. -/
def planeEdgeCrossingEvent (w h : ℕ) : Set (PlaneEdge → Bool) :=
  extendPlaneEdges ⁻¹' bondCrossingEvent w h

/-- The edge crossing event is measurable. -/
theorem measurableSet_planeEdgeCrossingEvent (w h : ℕ) :
    MeasurableSet (planeEdgeCrossingEvent w h) :=
  (measurableSet_bondCrossingEvent w h).preimage measurable_extendPlaneEdges

/-- A rectangle crossing depends only on nearest-neighbor edge states. -/
theorem preimage_planeEdgeCrossingEvent (w h : ℕ) :
    restrictToPlaneEdges ⁻¹' planeEdgeCrossingEvent w h = bondCrossingEvent w h := by
  ext ω
  change (∃ (a b : planeRectangle w h) (p : (rectangleGraph (planeRectangle w h)).Walk a b),
    a ∈ rectangleLeft (planeRectangle w h) ∧ b ∈ rectangleRight (planeRectangle w h) ∧
      IsBondOpenWalk (extendPlaneEdges (restrictToPlaneEdges ω)) p) ↔ _
  simp only [bondCrossingEvent, mem_ofPred_eq, isBondOpenWalk_extend_restrict]

/-- Restriction of an associated all-pairs law is associated on nearest-neighbor edges. -/
theorem restrictToPlaneEdges_associated (μ : Measure (Sym2 (Site 2) → Bool))
    (hμ : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    {A B : Set (PlaneEdge → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (μ.map restrictToPlaneEdges).real A * (μ.map restrictToPlaneEdges).real B ≤
      (μ.map restrictToPlaneEdges).real (A ∩ B) := by
  have ha : IsUpperSet (restrictToPlaneEdges ⁻¹' A) :=
    fun _ _ hω h => hA (monotone_restrictToPlaneEdges hω) h
  have hb : IsUpperSet (restrictToPlaneEdges ⁻¹' B) :=
    fun _ _ hω h => hB (monotone_restrictToPlaneEdges hω) h
  have hh := hμ _ _ ha hb (hAm.preimage measurable_restrictToPlaneEdges)
    (hBm.preimage measurable_restrictToPlaneEdges)
  simpa only [Measure.real, Measure.map_apply measurable_restrictToPlaneEdges hAm,
    Measure.map_apply measurable_restrictToPlaneEdges hBm,
    Measure.map_apply measurable_restrictToPlaneEdges (hAm.inter hBm), preimage_inter] using hh

/-- Projecting an all-pairs law to lattice edges preserves rectangle crossing probabilities. -/
theorem restrictToPlaneEdges_crossing (μ : Measure (Sym2 (Site 2) → Bool)) (w h : ℕ) :
    (μ.map restrictToPlaneEdges).real (planeEdgeCrossingEvent w h) =
      μ.real (bondCrossingEvent w h) := by
  rw [Measure.real, Measure.map_apply measurable_restrictToPlaneEdges
    (measurableSet_planeEdgeCrossingEvent w h), preimage_planeEdgeCrossingEvent]
  rfl

/-- A site map preserving lattice adjacency induces a map on unoriented lattice edges. -/
def planeEdgeMap (g : Site 2 → Site 2)
    (hg : ∀ ⦃x y⦄, (lattice 2).Adj x y → (lattice 2).Adj (g x) (g y))
    (e : PlaneEdge) : PlaneEdge := by
  refine ⟨Sym2.map g e.val, ?_⟩
  have hmap (e : Sym2 (Site 2)) : e ∈ (lattice 2).edgeSet →
      Sym2.map g e ∈ (lattice 2).edgeSet := by
    induction e using Sym2.ind with
    | _ x y =>
      intro h
      exact ((lattice 2).mem_edgeSet).mpr (hg (((lattice 2).mem_edgeSet).mp h))
  exact hmap e.val e.property

/-- A symmetry of an all-pairs law descends to the corresponding lattice-edge law. -/
theorem measurePreserving_restrictToPlaneEdges (μ : Measure (Sym2 (Site 2) → Bool))
    (g : Site 2 → Site 2)
    (hg : ∀ ⦃x y⦄, (lattice 2).Adj x y → (lattice 2).Adj (g x) (g y))
    (hμ : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map g) μ μ) :
    MeasurePreserving (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap g hg)
      (μ.map restrictToPlaneEdges) (μ.map restrictToPlaneEdges) := by
  have hmap : Measurable (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap g hg) :=
    Measurable.of_eval (fun e => measurable_pi_apply (planeEdgeMap g hg e))
  refine ⟨hmap, ?_⟩
  rw [Measure.map_map hmap measurable_restrictToPlaneEdges]
  have he : (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap g hg) ∘ restrictToPlaneEdges =
      restrictToPlaneEdges ∘ (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map g) := by
    funext ω e
    rfl
  rw [he, ← Measure.map_map measurable_restrictToPlaneEdges hμ.measurable, hμ.map_eq]

/-- The nearest-neighbor law induced by a probability field law is a probability measure. -/
theorem isProbabilityMeasure_fieldPlaneEdgeLaw (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (level : ℝ) :
    IsProbabilityMeasure ((fieldBondLaw μ level).map restrictToPlaneEdges) := by
  let := isProbabilityMeasure_fieldBondLaw μ level
  exact (Measure.isProbabilityMeasure_map_iff measurable_restrictToPlaneEdges.aemeasurable).2
    inferInstance

/-- The nearest-neighbor law induced by an associated field is associated. -/
theorem fieldPlaneEdgeLaw_associated (μ : Measure (Site 2 → ℝ))
    (hμ : IsAssociatedPlanarLaw μ) (level : ℝ)
    {A B : Set (PlaneEdge → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    ((fieldBondLaw μ level).map restrictToPlaneEdges).real A *
      ((fieldBondLaw μ level).map restrictToPlaneEdges).real B ≤
      ((fieldBondLaw μ level).map restrictToPlaneEdges).real (A ∩ B) :=
  restrictToPlaneEdges_associated (fieldBondLaw μ level)
    (fun _ _ ha hb ham hbm => fieldBondLaw_associated μ hμ level ha hb ham hbm) hA hB hAm hBm

/-- Positive-width edge crossings have the same probability as field crossings. -/
theorem fieldPlaneEdgeLaw_crossing (μ : Measure (Site 2 → ℝ)) (level : ℝ)
    (w h : ℕ) (hw : 0 < w) :
    ((fieldBondLaw μ level).map restrictToPlaneEdges).real (planeEdgeCrossingEvent w h) =
      μ.real (planarCrossingEvent w h level) :=
  (restrictToPlaneEdges_crossing (fieldBondLaw μ level) w h).trans
    (fieldBondLaw_crossing μ level w h hw)

end Sandpile.External.RSW
