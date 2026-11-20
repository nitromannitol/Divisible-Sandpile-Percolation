import Sandpile.External.ContinuumRSW.FullAssociation
import Sandpile.Support.PlanarLaw

/-!
# Association of sampled threshold fields

Thresholding a field with associated finite-dimensional distributions produces
an associated law on a countable binary configuration space.
-/

open MeasureTheory Set

namespace Sandpile.External.ContinuumRSW

open Sandpile.Continuum

/-- Threshold a real value into a binary state. -/
noncomputable def threshold (level x : ℝ) : Fin 2 :=
  if level ≤ x then 1 else 0

/-- Thresholding is nondecreasing. -/
theorem monotone_threshold (level : ℝ) : Monotone (threshold level) := by
  intro x y hxy
  by_cases hx : level ≤ x
  · have hy : level ≤ y := hx.trans hxy
    simp only [threshold, ite_eq_left hx, ite_eq_left hy, le_refl]
  · simp only [threshold, ite_eq_right hx]
    exact Fin.zero_le _

/-- Thresholding is measurable. -/
theorem measurable_threshold (level : ℝ) : Measurable (threshold level) := by
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    measurable_const measurable_const

/-- The sampled binary configuration of a field. -/
noncomputable def sampledThreshold {Ω : Type} (X : Space 2 → Ω → ℝ)
    (q : Sandpile.Site 2 → Space 2) (level : ℝ) (ω : Ω) : Sandpile.Site 2 → Fin 2 :=
  fun z => threshold level (X (q z) ω)

/-- The sampled binary configuration is measurable. -/
theorem measurable_sampledThreshold {Ω : Type} [MeasurableSpace Ω]
    {X : Space 2 → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    (q : Sandpile.Site 2 → Space 2) (level : ℝ) :
    Measurable (sampledThreshold X q level) :=
  Measurable.of_eval fun z => (measurable_threshold level).comp (hX (q z))

/-- Finite-dimensional association of a field passes to its sampled threshold law. -/
theorem finiteCoordinateAssociation_sampledThreshold {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Space 2 → Ω → ℝ)
    (hX : ∀ u, Measurable (X u)) (hassoc : IsAssociatedField P X)
    (q : Sandpile.Site 2 → Space 2) (level : ℝ) :
    FiniteCoordinateAssociation (P.map (sampledThreshold X q level)) := by
  classical
  intro s A B hAu hBu hAm hBm hAs hBs
  let e : Fin (Fintype.card ↥s) ≃ ↥s := (Fintype.equivFin ↥s).symm
  let Z : (Fin (Fintype.card ↥s) → ℝ) → (Sandpile.Site 2 → Fin 2) := fun v z =>
    if hz : z ∈ s then threshold level (v (e.symm ⟨z, hz⟩)) else 0
  have hZmono : Monotone Z := by
    intro v w hvw z
    dsimp [Z]
    split
    · exact monotone_threshold level (hvw _)
    · exact le_rfl
  have hZm : Measurable Z := by
    apply Measurable.of_eval
    intro z
    dsimp [Z]
    split
    · exact (measurable_threshold level).comp (measurable_pi_apply _)
    · exact measurable_const
  let U : Set (Fin (Fintype.card ↥s) → ℝ) := Z ⁻¹' A
  let V : Set (Fin (Fintype.card ↥s) → ℝ) := Z ⁻¹' B
  have hUu : IsUpperSet U := fun _ _ h hv => hAu (hZmono h) hv
  have hVu : IsUpperSet V := fun _ _ h hv => hBu (hZmono h) hv
  have hUm : MeasurableSet U := hAm.preimage hZm
  have hVm : MeasurableSet V := hBm.preimage hZm
  let v : Ω → (Fin (Fintype.card ↥s) → ℝ) := fun ω i => X (q (e i)) ω
  have hsame (ω : Ω) : ∀ z ∈ s, sampledThreshold X q level ω z = Z (v ω) z := by
    intro z hz
    simp only [sampledThreshold, Z, dite_eq_left hz, v, Equiv.apply_symm_apply]
  have hAeq : (sampledThreshold X q level) ⁻¹' A = v ⁻¹' U := by
    ext ω
    exact hAs _ _ (hsame ω)
  have hBeq : (sampledThreshold X q level) ⁻¹' B = v ⁻¹' V := by
    ext ω
    exact hBs _ _ (hsame ω)
  have hF := Sandpile.Support.fkg_cylinder_same hX hassoc (Fintype.card ↥s)
    (fun i => q (e i)) U V hUm hUu hVm hVu
  have hmap := measurable_sampledThreshold hX q level
  simp only [Measure.real, Measure.map_apply hmap hAm, Measure.map_apply hmap hBm,
    Measure.map_apply hmap (hAm.inter hBm), preimage_inter, hAeq, hBeq]
  exact hF

/-- The sampled threshold law is positively associated for all measurable upper events. -/
theorem sampledThreshold_associated {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Space 2 → Ω → ℝ)
    (hX : ∀ u, Measurable (X u)) (hassoc : IsAssociatedField P X)
    (q : Sandpile.Site 2 → Space 2) (level : ℝ)
    (A B : Set (Sandpile.Site 2 → Fin 2))
    (hAu : IsUpperSet A) (hBu : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (P.map (sampledThreshold X q level)).real A *
        (P.map (sampledThreshold X q level)).real B ≤
      (P.map (sampledThreshold X q level)).real (A ∩ B) := by
  let μ := P.map (sampledThreshold X q level)
  have hmap := measurable_sampledThreshold hX q level
  let : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hmap.aemeasurable).2
    inferInstance
  have hfin : FiniteCoordinateAssociation μ :=
    finiteCoordinateAssociation_sampledThreshold P X hX hassoc q level
  exact measureReal_mul_le_inter_of_finiteCoordinateAssociation hfin hAu hBu hAm hBm

/-- Regard a binary configuration as a real-valued field taking values zero and one. -/
def binaryToReal (x : Sandpile.Site 2 → Fin 2) : Sandpile.Site 2 → ℝ :=
  fun z => ((x z : ℕ) : ℝ)

/-- The real-valued encoding of a binary configuration is measurable. -/
theorem measurable_binaryToReal : Measurable binaryToReal := by
  apply Measurable.of_eval
  intro z
  exact (measurable_of_countable (fun x : Fin 2 => ((x : ℕ) : ℝ))).comp
    (measurable_pi_apply z)

/-- The real-valued encoding of a binary configuration is increasing. -/
theorem monotone_binaryToReal : Monotone binaryToReal := by
  intro x y h z
  change ((x z : ℕ) : ℝ) ≤ ((y z : ℕ) : ℝ)
  have hxy : (x z : ℕ) ≤ (y z : ℕ) := h z
  exact_mod_cast hxy

/-- The real-valued law of the sampled threshold configuration. -/
noncomputable def sampledPlanarLaw {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Space 2 → Ω → ℝ) (q : Sandpile.Site 2 → Space 2) (level : ℝ) :
    Measure (Sandpile.Site 2 → ℝ) :=
  (P.map (sampledThreshold X q level)).map binaryToReal

/-- The sampled threshold law satisfies the lattice association hypothesis. -/
theorem sampledPlanarLaw_associated {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Space 2 → Ω → ℝ)
    (hX : ∀ u, Measurable (X u)) (hassoc : IsAssociatedField P X)
    (q : Sandpile.Site 2 → Space 2) (level : ℝ) :
    Sandpile.IsAssociatedPlanarLaw (sampledPlanarLaw P X q level) := by
  apply Sandpile.isAssociatedPlanarLaw_map _ binaryToReal measurable_binaryToReal
    monotone_binaryToReal
  exact sampledThreshold_associated P X hX hassoc q level

end Sandpile.External.ContinuumRSW
