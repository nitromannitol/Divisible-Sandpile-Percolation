/-
Carrying a crossing statement about all the prescribed rectangles at once from
one space carrying white noise to another.

The frozen statements of `lem:finite-scale-extraction` and
`thm:limiting-odometer-crossing` bind the level, the scales and the horizon
BEFORE the space carrying the white noise, exactly as the paper does: the fields
`𝒳_s` have a fixed law, so nothing they are asked about can depend on the space
they are realized on.  The proof, on the other hand, produces the level and the
scales by continuity from below on one space.  This module is what closes that
gap.

The crossing event is not known to be measurable, so equality in law says
nothing about it directly.  What the chain events of
`Sandpile/Support/CrossUnion.lean` give is a bracket: they are measurable,
their probability is determined by the law of the field, and they surround the
crossing event at two levels a distance `ε` apart.  Running the bracket twice,
once up and once down, transfers a crossing bound from one space to another at
the cost of lowering the level by `ε`, which the extraction absorbs into `c`.
-/
import Sandpile.Support.CrossLaw

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- On the continuity event, a chain event for every rectangle forces a crossing
of every rectangle. -/
theorem iInter_crossApprox_inter_subset_crossing {Ω : Type*} [MeasurableSpace Ω]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {N : ℕ} {a b : Fin N → Fin 2 → ℝ}
    {dir : Fin N → Fin 2} {l : ℝ} :
    (⋂ j : Fin N, crossApprox X (a j) (b j) (dir j) l) ∩ {ω | Continuous fun u => X u ω}
      ⊆ {ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | l ≤ X u ω}} := by
  rintro ω ⟨h1, h2⟩ j
  exact crossApprox_inter_subset_crossing ⟨Set.mem_iInter.mp h1 j, h2⟩

/-- On the continuity event, crossings of every rectangle are carried by chain
events at a level lower by `ε`. -/
theorem crossing_all_inter_subset_iInter_crossApprox {Ω : Type*} [MeasurableSpace Ω]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {N : ℕ} {a b : Fin N → Fin 2 → ℝ}
    {dir : Fin N → Fin 2} {l ε : ℝ}
    (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i) (hε : 0 < ε) :
    {ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | l ≤ X u ω}}
        ∩ {ω | Continuous fun u => X u ω}
      ⊆ ⋂ j : Fin N, crossApprox X (a j) (b j) (dir j) (l - ε) := by
  rintro ω ⟨h1, h2⟩
  refine Set.mem_iInter.mpr fun j => ?_
  exact crossing_inter_subset_crossApprox (hab j 0) (hab j 1) hε ⟨h1 j, h2⟩

/-- The outer bracket for all the rectangles at once, at a level lower by `ε`. -/
theorem measure_crossing_all_le_iInter_crossApprox {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {N : ℕ}
    {a b : Fin N → Fin 2 → ℝ} {dir : Fin N → Fin 2} {l ε : ℝ}
    (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i) (hε : 0 < ε)
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω) :
    P {ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | l ≤ X u ω}}
      ≤ P (⋂ j : Fin N, crossApprox X (a j) (b j) (dir j) (l - ε)) := by
  have hnull : P {ω | Continuous fun u => X u ω}ᶜ = 0 := by
    rw [← MeasureTheory.ae_iff.mp hcont]
    rfl
  calc P {ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | l ≤ X u ω}}
      ≤ P ({ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | l ≤ X u ω}}
            ∩ {ω | Continuous fun u => X u ω})
          + P {ω | Continuous fun u => X u ω}ᶜ := measure_le_inter_add_compl P _ _
    _ = P ({ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | l ≤ X u ω}}
            ∩ {ω | Continuous fun u => X u ω}) := by rw [hnull, add_zero]
    _ ≤ P (⋂ j : Fin N, crossApprox X (a j) (b j) (dir j) (l - ε)) :=
        measure_mono (crossing_all_inter_subset_iInter_crossApprox hab hε)

/-- The inner bracket for all the rectangles at once. -/
theorem measure_iInter_crossApprox_le_crossing_all {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {N : ℕ}
    {a b : Fin N → Fin 2 → ℝ} {dir : Fin N → Fin 2} {l : ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω) :
    P (⋂ j : Fin N, crossApprox X (a j) (b j) (dir j) l)
      ≤ P {ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | l ≤ X u ω}} := by
  have hnull : P {ω | Continuous fun u => X u ω}ᶜ = 0 := by
    rw [← MeasureTheory.ae_iff.mp hcont]
    rfl
  calc P (⋂ j : Fin N, crossApprox X (a j) (b j) (dir j) l)
      ≤ P ((⋂ j : Fin N, crossApprox X (a j) (b j) (dir j) l)
            ∩ {ω | Continuous fun u => X u ω})
          + P {ω | Continuous fun u => X u ω}ᶜ := measure_le_inter_add_compl P _ _
    _ = P ((⋂ j : Fin N, crossApprox X (a j) (b j) (dir j) l)
            ∩ {ω | Continuous fun u => X u ω}) := by rw [hnull, add_zero]
    _ ≤ P {ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | l ≤ X u ω}} :=
        measure_mono iInter_crossApprox_inter_subset_crossing

/-- The intersection over the rectangles of the chain events is determined by
the law of the field, and so has the same probability on any two spaces carrying
fields of the same law. -/
theorem measure_iInter_crossApprox_eq_of_fieldLaw {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (Y : Sandpile.Continuum.Space 2 → Ω' → ℝ)
    (hX : ∀ u, Measurable (X u)) (hY : ∀ u, Measurable (Y u))
    (hlaw : Sandpile.Continuum.fieldLaw P X = Sandpile.Continuum.fieldLaw P' Y)
    {N : ℕ} (a b : Fin N → Fin 2 → ℝ) (dir : Fin N → Fin 2) (l : ℝ) :
    P (⋂ j : Fin N, crossApprox X (a j) (b j) (dir j) l)
      = P' (⋂ j : Fin N, crossApprox Y (a j) (b j) (dir j) l) := by
  have hev : ∀ u : Sandpile.Continuum.Space 2,
      Measurable (fun g : Sandpile.Continuum.Space 2 → ℝ => g u) := fun u => measurable_pi_apply u
  have hmeasSet : MeasurableSet (⋂ j : Fin N, crossApprox
      (fun (u : Sandpile.Continuum.Space 2) (g : Sandpile.Continuum.Space 2 → ℝ) => g u)
      (a j) (b j) (dir j) l) :=
    MeasurableSet.iInter fun j => measurableSet_crossApprox hev (a j) (b j) (dir j) l
  have hXpre : (⋂ j : Fin N, crossApprox X (a j) (b j) (dir j) l)
      = (fun ω => (fun u => X u ω) : Ω → (Sandpile.Continuum.Space 2 → ℝ)) ⁻¹'
        (⋂ j : Fin N, crossApprox
          (fun (u : Sandpile.Continuum.Space 2) (g : Sandpile.Continuum.Space 2 → ℝ) => g u)
          (a j) (b j) (dir j) l) := by
    rw [Set.preimage_iInter]
    exact Set.iInter_congr fun j => crossApprox_eq_preimage X (a j) (b j) (dir j) l
  have hYpre : (⋂ j : Fin N, crossApprox Y (a j) (b j) (dir j) l)
      = (fun ω => (fun u => Y u ω) : Ω' → (Sandpile.Continuum.Space 2 → ℝ)) ⁻¹'
        (⋂ j : Fin N, crossApprox
          (fun (u : Sandpile.Continuum.Space 2) (g : Sandpile.Continuum.Space 2 → ℝ) => g u)
          (a j) (b j) (dir j) l) := by
    rw [Set.preimage_iInter]
    exact Set.iInter_congr fun j => crossApprox_eq_preimage Y (a j) (b j) (dir j) l
  rw [hXpre, hYpre, Sandpile.Continuum.measure_preimage_fieldLaw P X hX hmeasSet,
    Sandpile.Continuum.measure_preimage_fieldLaw P' Y hY hmeasSet, hlaw]

/-- The transfer: a crossing bound for all the rectangles on one space gives the
same bound on any other space carrying a field of the same law, at a level lower
by `ε`. -/
theorem measure_crossing_all_transfer {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (Y : Sandpile.Continuum.Space 2 → Ω' → ℝ)
    (hX : ∀ u, Measurable (X u)) (hY : ∀ u, Measurable (Y u))
    (hcX : ∀ᵐ ω ∂P, Continuous fun u => X u ω)
    (hcY : ∀ᵐ ω ∂P', Continuous fun u => Y u ω)
    (hlaw : Sandpile.Continuum.fieldLaw P X = Sandpile.Continuum.fieldLaw P' Y)
    {N : ℕ} (a b : Fin N → Fin 2 → ℝ) (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i)
    (dir : Fin N → Fin 2) (l ε : ℝ) (hε : 0 < ε) :
    P {ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | l ≤ X u ω}}
      ≤ P' {ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | l - ε ≤ Y u ω}} :=
  calc P {ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | l ≤ X u ω}}
      ≤ P (⋂ j : Fin N, crossApprox X (a j) (b j) (dir j) (l - ε)) :=
        measure_crossing_all_le_iInter_crossApprox P hab hε hcX
    _ = P' (⋂ j : Fin N, crossApprox Y (a j) (b j) (dir j) (l - ε)) :=
        measure_iInter_crossApprox_eq_of_fieldLaw P P' X Y hX hY hlaw a b dir (l - ε)
    _ ≤ P' {ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | l - ε ≤ Y u ω}} :=
        measure_iInter_crossApprox_le_crossing_all P' hcY

end Sandpile.Support
