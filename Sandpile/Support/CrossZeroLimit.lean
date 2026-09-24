/-
Closed superlevel crossings at an increasing limit of levels, and the square
crossing estimate at level zero.
-/
import Sandpile.Support.CrossCompact
import Sandpile.Support.CrossDuality

open MeasureTheory Set Filter Topology
open scoped ENNReal
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

namespace Sandpile.Support

/-- A crossing at every level in an increasing convergent sequence gives a
crossing at the limiting level. -/
theorem crosses_of_monotone_levels {a b : Fin 2 → ℝ} {i : Fin 2}
    {f : Space 2 → ℝ} (hf : Continuous f) {l : ℕ → ℝ} {c : ℝ}
    (hmono : Monotone l) (hlim : Tendsto l atTop (𝓝 c))
    (hcross : ∀ n, Crosses a b i {x | l n ≤ f x}) :
    Crosses a b i {x | c ≤ f x} := by
  have hA : IsClosed {x : Space 2 | x i = a i} :=
    isClosed_eq (by fun_prop) continuous_const
  have hB : IsClosed {x : Space 2 | x i = b i} :=
    isClosed_eq (by fun_prop) continuous_const
  obtain ⟨C, hsub, hcomp, hconn, hCA, hCB⟩ := CrossCompact.exists_connected_compact_iInter
    (isCompact_rectSet a b) hA hB (fun n => {x | l n ≤ f x})
    (fun _ => isClosed_le continuous_const hf)
    (fun n m hnm x hx => (hmono hnm).trans hx) (fun n => by
      obtain ⟨C, hsub, hcomp, hconn, hp, hq⟩ := hcross n
      exact ⟨C, fun x hx => (hsub hx).symm, hcomp, hconn, hp, hq⟩)
  refine ⟨C, ?_, hcomp, hconn, hCA, hCB⟩
  intro x hx
  obtain ⟨hxrect, hxlevels⟩ := hsub hx
  exact ⟨le_of_tendsto hlim (Eventually.of_forall fun n => Set.mem_iInter.mp hxlevels n), hxrect⟩

/-- A closed superlevel crossing has a countable measurable representative,
obtained from chain events at strictly lower levels. -/
theorem crossing_ae_eq_iInter_crossApprox {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Space 2 → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2)
    (hab : ∀ j, a j < b j) (c : ℝ)
    (hc : ∀ᵐ ω ∂P, Continuous fun x => X x ω) :
    {ω | Crosses a b i {x | c ≤ X x ω}} =ᵐ[P]
      ⋂ n : ℕ, crossApprox X a b i (c - 1 / ((n : ℝ) + 1)) := by
  filter_upwards [hc] with ω hω
  apply propext
  constructor
  · intro hcross
    exact Set.mem_iInter.mpr fun n =>
      crossing_inter_subset_crossApprox (hab 0) (hab 1) (by positivity) ⟨hcross, hω⟩
  · intro hchain
    apply crosses_of_monotone_levels hω (l := fun n : ℕ => c - 1 / ((n : ℝ) + 1))
    · intro n m hnm
      exact sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hnm 1)) c
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub c
    · intro n
      exact crossApprox_inter_subset_crossing ⟨Set.mem_iInter.mp hchain n, hω⟩

/-- The superlevel crossing event of an almost surely continuous field is
measurable in the completed probability space. -/
theorem nullMeasurableSet_crossing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Space 2 → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2)
    (hab : ∀ j, a j < b j) (c : ℝ) (hm : ∀ x, Measurable (X x))
    (hc : ∀ᵐ ω ∂P, Continuous fun x => X x ω) :
    NullMeasurableSet {ω | Crosses a b i {x | c ≤ X x ω}} P := by
  exact ((MeasurableSet.iInter fun n : ℕ =>
    measurableSet_crossApprox hm a b i (c - 1 / ((n : ℝ) + 1))).nullMeasurableSet).congr
      (crossing_ae_eq_iInter_crossApprox P X a b i hab c hc).symm

/-- Equal field laws give equal closed-superlevel crossing probabilities for
almost surely continuous fields, without a change of level. -/
theorem measure_crossing_eq_of_fieldLaw {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω')
    (X : Space 2 → Ω → ℝ) (Y : Space 2 → Ω' → ℝ)
    (hmX : ∀ x, Measurable (X x)) (hmY : ∀ x, Measurable (Y x))
    (hcX : ∀ᵐ ω ∂P, Continuous fun x => X x ω)
    (hcY : ∀ᵐ ω ∂Q, Continuous fun x => Y x ω)
    (hlaw : fieldLaw P X = fieldLaw Q Y)
    (a b : Fin 2 → ℝ) (i : Fin 2) (hab : ∀ j, a j < b j) (c : ℝ) :
    P {ω | Crosses a b i {x | c ≤ X x ω}} =
      Q {ω | Crosses a b i {x | c ≤ Y x ω}} := by
  rw [measure_congr (crossing_ae_eq_iInter_crossApprox P X a b i hab c hcX),
    measure_congr (crossing_ae_eq_iInter_crossApprox Q Y a b i hab c hcY)]
  let E : Set (Space 2 → ℝ) := ⋂ n : ℕ,
    crossApprox (fun x (f : Space 2 → ℝ) => f x) a b i (c - 1 / ((n : ℝ) + 1))
  have hE : MeasurableSet E := MeasurableSet.iInter fun n =>
    measurableSet_crossApprox (fun x => measurable_pi_apply x) a b i _
  have hx : (⋂ n : ℕ, crossApprox X a b i (c - 1 / ((n : ℝ) + 1))) =
      (fun ω x => X x ω) ⁻¹' E := by
    simp only [E, Set.preimage_iInter]
    exact Set.iInter_congr fun n => crossApprox_eq_preimage X a b i _
  have hy : (⋂ n : ℕ, crossApprox Y a b i (c - 1 / ((n : ℝ) + 1))) =
      (fun ω x => Y x ω) ⁻¹' E := by
    simp only [E, Set.preimage_iInter]
    exact Set.iInter_congr fun n => crossApprox_eq_preimage Y a b i _
  rw [hx, hy, measure_preimage_fieldLaw P X hmX hE,
    measure_preimage_fieldLaw Q Y hmY hE, hlaw]

/-- The countable chain events at levels tending up to zero force a zero-level
crossing on every continuous sample path. -/
theorem iInter_crossApprox_subset_zero {Ω : Type*} [MeasurableSpace Ω]
    (X : Space 2 → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2) :
    (⋂ n : ℕ, crossApprox X a b i (-(1 / ((n : ℝ) + 1)))) ∩
      {ω | Continuous fun x => X x ω} ⊆
        {ω | Crosses a b i {x | 0 ≤ X x ω}} := by
  rintro ω ⟨hω, hc⟩
  apply crosses_of_monotone_levels hc
    (l := fun n : ℕ => -(1 / ((n : ℝ) + 1)))
  · intro n m hnm
    exact neg_le_neg (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnm 1))
  · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  · intro n
    exact crossApprox_inter_subset_crossing ⟨Set.mem_iInter.mp hω n, hc⟩

/-- Sign and coordinate symmetry give the square estimate at level zero. -/
theorem square_half_crossing_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Space 2 → Ω → ℝ)
    (hmeas : ∀ x, Measurable (X x))
    (hcont : ∀ᵐ ω ∂P, Continuous fun x => X x ω)
    (hsym : IsSymmetricField P X) (s : ℝ) (hs : 0 < s) :
    (1 : ℝ) / 2 ≤ P.real {ω | Crosses ![0, 0] ![s, s] 0 {x | 0 ≤ X x ω}} := by
  let E : ℕ → Set Ω := fun n => crossApprox X ![0, 0] ![s, s] 0 (-(1 / ((n : ℝ) + 1)))
  have hmono : Antitone E := by
    intro n m hnm
    exact crossApprox_mono_level _ _ _ _ (neg_le_neg
      (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hnm 1)))
  have hhalf : ENNReal.ofReal ((1 : ℝ) / 2) ≤ P (⋂ n, E n) := by
    rw [hmono.measure_iInter (fun n => (measurableSet_crossApprox hmeas _ _ _ _).nullMeasurableSet)
      ⟨0, measure_ne_top P _⟩]
    apply le_iInf
    intro n
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top P _)).2
      (square_half_crossApprox P X hmeas hcont hsym s (1 / ((n : ℝ) + 1)) hs (by positivity))
  have hsub : P (⋂ n, E n) ≤ P {ω | Crosses ![0, 0] ![s, s] 0 {x | 0 ≤ X x ω}} := by
    apply measure_mono_ae
    filter_upwards [hcont] with ω hc hω
    exact iInter_crossApprox_subset_zero X _ _ _ ⟨hω, hc⟩
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top P _)).1 (hhalf.trans hsub)

/-- The zero-level square bound holds for every translated field. -/
theorem square_half_translate_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Space 2 → Ω → ℝ)
    (hmeas : ∀ x, Measurable (X x))
    (hcont : ∀ᵐ ω ∂P, Continuous fun x => X x ω)
    (hsym : IsSymmetricField P X) (v : Space 2) (s : ℝ) (hs : 1 ≤ s) :
    (1 : ℝ) / 2 ≤ P.real {ω |
      Crosses ![0, 0] ![2 * s, 2 * s] 0 {x | 0 ≤ X (x + v) ω}} := by
  apply square_half_crossing_zero P (fun x ω => X (x + v) ω) (fun x => hmeas _)
    _ (isSymmetricField_translate hsym v) (2 * s) (by linarith)
  filter_upwards [hcont] with ω hω
  exact hω.comp (continuous_id.add continuous_const)

end Sandpile.Support
