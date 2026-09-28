import Sandpile.Support.LinThreshold
import Sandpile.Support.Odometer
import Sandpile.Support.LinGaussFactor

/-! # Null-measurable threshold replacement

The threshold events of the Gaussian branch are not measurable, only null measurable, and
`eq:dgt4-path-contact-replacement` does not need them to be either.

`Support/LinGaussBridge.lean` proves that the Gaussian Green field is only ALMOST everywhere
measurable, since it is defined by a case split on the existence of the box limit.  So the
threshold event `{σ : b < J(x)}` of the Gaussian branch of `lem:dgt4-path-survival` is only
null measurable, and the threshold replacement of `sandpile.tex:5532-5550` cannot be read
through a lemma that asks its events to be measurable.

Two observations remove the difficulty.  First, the replacement inequality is true for
ARBITRARY sets: a measure is an outer measure, `S ⊆ T ∪ (S Δ T)` and `T ⊆ S ∪ (S Δ T)` are set
inclusions, and the union bound over a finite family is monotonicity plus subadditivity, so
no measurability enters at any step.  Second, the threshold events ARE null measurable, which
is what every later step (Fubini, conditioning) will want.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- The threshold replacement of `eq:dgt4-path-contact-replacement` with NO measurability
hypothesis: both sides are outer measures, and every step is monotonicity or
subadditivity. -/
theorem abs_measureReal_iInter_sub_le_all {alpha iota : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsFiniteMeasure mu] (s : Finset iota) (A B : iota → Set alpha) :
    |mu.real (⋂ i ∈ s, A i) - mu.real (⋂ i ∈ s, B i)|
      ≤ ∑ i ∈ s, mu.real (symmDiff (A i) (B i)) := by
  classical
  set S : Set alpha := ⋂ i ∈ s, A i with hS
  set T : Set alpha := ⋂ i ∈ s, B i with hT
  have h1 : S ⊆ T ∪ symmDiff S T := by
    intro x hx
    by_cases h : x ∈ T
    · exact Or.inl h
    · exact Or.inr (Set.mem_symmDiff.mpr (Or.inl ⟨hx, h⟩))
  have h2 : T ⊆ S ∪ symmDiff S T := by
    intro x hx
    by_cases h : x ∈ S
    · exact Or.inl h
    · exact Or.inr (Set.mem_symmDiff.mpr (Or.inr ⟨hx, h⟩))
  have h3 : mu.real S ≤ mu.real T + mu.real (symmDiff S T) :=
    le_trans (measureReal_mono h1) (measureReal_union_le T (symmDiff S T))
  have h4 : mu.real T ≤ mu.real S + mu.real (symmDiff S T) :=
    le_trans (measureReal_mono h2) (measureReal_union_le S (symmDiff S T))
  have h5 : mu.real (symmDiff S T) ≤ mu.real (⋃ i ∈ s, symmDiff (A i) (B i)) :=
    measureReal_mono (symmDiff_iInter_subset s A B) (measure_ne_top mu _)
  have h6 : mu.real (⋃ i ∈ s, symmDiff (A i) (B i)) ≤ ∑ i ∈ s, mu.real (symmDiff (A i) (B i)) :=
    measureReal_biUnion_finset_le s (fun i => symmDiff (A i) (B i))
  rw [abs_le]
  constructor <;> linarith

/-- The Gaussian Green field at a site is almost everywhere measurable in the mass
normalization. -/
theorem aemeasurable_infiniteGreenField_mass (hd : 5 ≤ d) (v : ℝ≥0) (x : Site d) :
    AEMeasurable (fun σ : Site d → ℝ => infiniteGreenField (scenery d σ) x)
      (centeredMassLaw d (gaussianReal 0 v)) := by
  have h := aemeasurable_infiniteGreenField_iid hd v x
  rw [← map_scenery_centeredMassLaw d (gaussianReal 0 v) (by omega)] at h
  exact h.comp_aemeasurable (measurable_scenery d).aemeasurable

/-- The threshold event of the Gaussian branch is null measurable. -/
theorem nullMeasurableSet_threshold_gauss (hd : 5 ≤ d) (v : ℝ≥0) (x : Site d) (b : ℝ) :
    NullMeasurableSet {σ : Site d → ℝ | b < -infiniteGreenField (scenery d σ) x}
      (centeredMassLaw d (gaussianReal 0 v)) :=
  nullMeasurableSet_lt aemeasurable_const (aemeasurable_infiniteGreenField_mass hd v x).neg

/-- The threshold event of the Gaussian branch, written through the field `J` of
`sandpile.tex:5449-5450`, is null measurable. -/
theorem nullMeasurableSet_threshold_of (hd : 5 ≤ d) (v : ℝ≥0)
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : ∀ σ x, J σ x = -infiniteGreenField (scenery d σ) x) (x : Site d) (b : ℝ) :
    NullMeasurableSet {σ : Site d → ℝ | b < J σ x}
      (centeredMassLaw d (gaussianReal 0 v)) := by
  have hset : {σ : Site d → ℝ | b < J σ x}
      = {σ : Site d → ℝ | b < -infiniteGreenField (scenery d σ) x} := by
    ext σ
    simp only [Set.mem_setOf_eq, hJ]
  rw [hset]
  exact nullMeasurableSet_threshold_gauss hd v x b

/-- The survival event and the threshold event of `sandpile.tex:5527-5545` have the same
symmetric difference as the contact event and its threshold: both pairs are complements. -/
theorem symmDiff_survival_threshold (t : ℕ) (x : Site d) (b : ℝ)
    (J : (Site d → ℝ) → Site d → ℝ) :
    symmDiff {σ : Site d → ℝ | 0 < odometer σ t x} {σ : Site d → ℝ | J σ x ≤ b}
      = symmDiff {σ : Site d → ℝ | odometer σ t x = 0} {σ : Site d → ℝ | b < J σ x} := by
  have h1 : {σ : Site d → ℝ | 0 < odometer σ t x} = {σ : Site d → ℝ | odometer σ t x = 0}ᶜ := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · intro h hc
      rw [hc] at h
      exact lt_irrefl 0 h
    · intro h
      exact lt_of_le_of_ne (odometer_nonneg σ t x) (Ne.symm h)
  have h2 : {σ : Site d → ℝ | J σ x ≤ b} = {σ : Site d → ℝ | b < J σ x}ᶜ := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  rw [h1, h2, compl_symmDiff_compl]

end Sandpile
