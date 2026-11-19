import Sandpile.External.RSW.RectangleGluing
import Sandpile.External.RSW.DualRotatedProbability

/-!
# Rectangle gluing for associated bond laws

Positive association and lattice symmetry turn deterministic crossing gluing into a product
lower bound for horizontal crossing probabilities.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- The vertical-overlap reindexing preserves a translation- and interchange-invariant law. -/
theorem measurePreserving_glueVerticalIso (μ : Measure (Sym2 (Site 2) → Bool))
    (m n : ℕ)
    (ht : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + glueShift m n)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) :
    MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (glueVerticalIso m n)) μ μ := by
  have hh := hs.comp ht
  have he : (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (glueVerticalIso m n)) =
      (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map swapPlaneSite) ∘
        (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + glueShift m n)) := by
    funext ω e
    induction e using Sym2.ind with
    | _ x y => simp only [Function.comp_apply, Sym2.map_mk, glueVerticalIso_apply]
  rw [he]
  exact hh

/-- Associated, symmetric bond laws satisfy the product bound obtained by gluing two
horizontal rectangles across a square. -/
theorem bondCrossing_prob_glue (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (hμ : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    {m₁ m₂ n : ℕ} (hn₁ : n ≤ m₁) (hn₂ : n ≤ m₂)
    (ht : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + glueShift m₁ n)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) :
    μ.real (bondCrossingEvent m₁ n) * μ.real (bondCrossingEvent n n) *
      μ.real (bondCrossingEvent m₂ n) ≤ μ.real (bondCrossingEvent (m₁ + m₂ - n) n) := by
  let A := bondCrossingEvent m₁ n
  let f : (Sym2 (Site 2) → Bool) → (Sym2 (Site 2) → Bool) :=
    fun ω => ω ∘ Sym2.map (glueVerticalIso m₁ n)
  let g : (Sym2 (Site 2) → Bool) → (Sym2 (Site 2) → Bool) :=
    fun ω => ω ∘ Sym2.map (zdShiftIso (glueShift m₁ n))
  let B := f ⁻¹' bondCrossingEvent n n
  let C := g ⁻¹' bondCrossingEvent m₂ n
  have hf := measurePreserving_glueVerticalIso μ m₁ n ht hs
  have hg : MeasurePreserving g μ μ := ht
  have hA : IsUpperSet A := isUpperSet_bondCrossingEvent m₁ n
  have hB : IsUpperSet B := fun _ _ hω h =>
    isUpperSet_bondCrossingEvent n n (fun e => hω _) h
  have hC : IsUpperSet C := fun _ _ hω h =>
    isUpperSet_bondCrossingEvent m₂ n (fun e => hω _) h
  have hAm : MeasurableSet A := measurableSet_bondCrossingEvent m₁ n
  have hBm : MeasurableSet B := (measurableSet_bondCrossingEvent n n).preimage hf.measurable
  have hCm : MeasurableSet C := (measurableSet_bondCrossingEvent m₂ n).preimage hg.measurable
  have hBprob : μ.real B = μ.real (bondCrossingEvent n n) :=
    hf.measureReal_preimage (measurableSet_bondCrossingEvent n n).nullMeasurableSet
  have hCprob : μ.real C = μ.real (bondCrossingEvent m₂ n) :=
    hg.measureReal_preimage (measurableSet_bondCrossingEvent m₂ n).nullMeasurableSet
  have hsub : A ∩ (B ∩ C) ⊆ bondCrossingEvent (m₁ + m₂ - n) n := by
    rintro ω ⟨ha, hb, hc⟩
    exact bondCrossingEvent_of_glue hn₁ hn₂ ha hb hc
  calc
    μ.real (bondCrossingEvent m₁ n) * μ.real (bondCrossingEvent n n) *
        μ.real (bondCrossingEvent m₂ n) = μ.real A * (μ.real B * μ.real C) := by
          rw [hBprob, hCprob, mul_assoc]
    _ ≤ μ.real A * μ.real (B ∩ C) :=
      mul_le_mul_of_nonneg_left (hμ B C hB hC hBm hCm) measureReal_nonneg
    _ ≤ μ.real (A ∩ (B ∩ C)) := hμ A (B ∩ C) hA (hB.inter hC) hAm (hBm.inter hCm)
    _ ≤ μ.real (bondCrossingEvent (m₁ + m₂ - n) n) :=
      measureReal_mono hsub (measure_ne_top μ _)

/-- Field crossings satisfy the same rectangle gluing inequality at every positive scale. -/
theorem fieldCrossing_prob_glue (μ : Measure (Site 2 → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSymmetricPlanarLaw μ) (ha : IsAssociatedPlanarLaw μ) (level : ℝ)
    {m₁ m₂ n : ℕ} (hn : 0 < n) (hn₁ : n ≤ m₁) (hn₂ : n ≤ m₂) :
    μ.real (planarCrossingEvent m₁ n level) * μ.real (planarCrossingEvent n n level) *
      μ.real (planarCrossingEvent m₂ n level) ≤
        μ.real (planarCrossingEvent (m₁ + m₂ - n) n level) := by
  let ν := fieldBondLaw μ level
  let : IsProbabilityMeasure ν := isProbabilityMeasure_fieldBondLaw μ level
  have hs := fieldBondLaw_symmetric μ hμ level
  have hh := bondCrossing_prob_glue ν
    (fun _ _ hA hB hAm hBm => fieldBondLaw_associated μ ha level hA hB hAm hBm)
    hn₁ hn₂ (hs.1 (glueShift m₁ n)) hs.2.1
  rw [fieldBondLaw_crossing μ level m₁ n (by omega),
    fieldBondLaw_crossing μ level n n hn,
    fieldBondLaw_crossing μ level m₂ n (by omega),
    fieldBondLaw_crossing μ level (m₁ + m₂ - n) n (by omega)] at hh
  exact hh

end Sandpile.External.RSW
