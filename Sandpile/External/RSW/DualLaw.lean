import Sandpile.External.RSW.DualCrossing
import Sandpile.External.RSW.Association

/-!
# The dual bond configuration

The dual configuration closes each bond whose primal crossing bond is open. Positive
association is preserved by simultaneous complementation and reindexing.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- A dual bond is open exactly when the primal bond it crosses is closed. -/
noncomputable def dualBondConfig (ω : Sym2 (Site 2) → Bool) (e : Sym2 (Site 2)) : Bool :=
  !(ω (dualEdgeEquiv.symm e))

/-- The dual bond map is measurable. -/
theorem measurable_dualBondConfig : Measurable dualBondConfig := by
  apply Measurable.of_eval
  intro e
  exact (measurable_of_finite (fun b : Bool => !b)).comp (measurable_pi_apply _)

/-- The dual bond map reverses the coordinatewise order. -/
theorem antitone_dualBondConfig : Antitone dualBondConfig := by
  intro ω η h e
  have he := h (dualEdgeEquiv.symm e)
  change (!(η (dualEdgeEquiv.symm e))) ≤ (!(ω (dualEdgeEquiv.symm e)))
  cases hω : ω (dualEdgeEquiv.symm e) <;> cases hη : η (dualEdgeEquiv.symm e) <;> simp_all

/-- The dual configuration agrees with lattice duality on all nearest-neighbor edges. -/
theorem openPlaneBonds_dualBondConfig (ω : Sym2 (Site 2) → Bool) :
    openPlaneBonds (dualBondConfig ω) = dualConfig (openPlaneBonds ω) := by
  ext e
  rw [dualConfig_eq]
  have he : dualEdgeEquiv.symm e ∈ (lattice 2).edgeSet ↔ e ∈ (lattice 2).edgeSet := by
    rw [lattice_eq_zdGraph, ← dualEdge_mem_edgeSet_iff, ← dualEdgeEquiv_apply,
      dualEdgeEquiv.apply_symm_apply]
  simp only [openPlaneBonds, mem_ofPred_eq, dualBondConfig, lattice_eq_zdGraph] at *
  cases hw : ω (dualEdgeEquiv.symm e) <;> simp_all

/-- Decreasing events of an associated bond law are positively correlated. -/
theorem bond_measureReal_mul_le_inter_of_lower (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (hμ : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    {A B : Set (Sym2 (Site 2) → Bool)} (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    μ.real A * μ.real B ≤ μ.real (A ∩ B) := by
  have hass := hμ Aᶜ Bᶜ hA.compl hB.compl hAm.compl hBm.compl
  rw [← compl_union, probReal_compl_eq_one_sub hAm, probReal_compl_eq_one_sub hBm,
    probReal_compl_eq_one_sub (hAm.union hBm)] at hass
  have hu := measureReal_union_add_inter (μ := μ) hBm (measure_ne_top μ A) (measure_ne_top μ B)
  nlinarith

/-- The dual of an associated bond law is associated. -/
theorem dualBondConfig_associated (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (hμ : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    {A B : Set (Sym2 (Site 2) → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (μ.map dualBondConfig).real A * (μ.map dualBondConfig).real B ≤
      (μ.map dualBondConfig).real (A ∩ B) := by
  have ha : IsLowerSet (dualBondConfig ⁻¹' A) :=
    fun _ _ hω h => hA (antitone_dualBondConfig hω) h
  have hb : IsLowerSet (dualBondConfig ⁻¹' B) :=
    fun _ _ hω h => hB (antitone_dualBondConfig hω) h
  have hh := bond_measureReal_mul_le_inter_of_lower μ hμ ha hb
    (hAm.preimage measurable_dualBondConfig) (hBm.preimage measurable_dualBondConfig)
  simpa only [Measure.real, Measure.map_apply measurable_dualBondConfig hAm,
    Measure.map_apply measurable_dualBondConfig hBm,
    Measure.map_apply measurable_dualBondConfig (hAm.inter hBm), preimage_inter] using hh

end Sandpile.External.RSW
