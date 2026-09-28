import Sandpile.Support.Dgt4AStep3Point

/-!
**Step 3 of case (a), from the pointwise comparison to the conditional mean**
(`eq:dgt4-gaussian-reflected-limit`, `sandpile.tex:5233-5251`).

The paper says that the scaled positive part of the reflected increment converges in
conditional probability and that its positive parts are uniformly integrable, so the
conditional means converge too.  Uniform integrability is not needed in this form: the
terminal domination of `Support/Dgt4AStep3Point.lean` bounds the positive part by `|y|`
plus a quantity whose conditional mean tends to zero, and a quantity bounded by a constant
plus an `L^1`-null quantity converges in mean as soon as it converges in probability.  The
three lemmas below are that argument, stated for one measure at a time and with every
error explicit, so that the limit is taken once in `Support/Dgt4AStep3Limit.lean`.

`abs_integral_sub_le_of_split` is the elementary inequality behind it: away from the
exceptional set the integrand is within `δ` of its limit, and on the exceptional set it is
bounded by `c+L+Y`, so the mean deviates by at most `δ+(c+L)\rho(A)+\E Y`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {α : Type*} [MeasurableSpace α]

/-- The mean of a nonnegative integrand that is within `δ` of `L` off an exceptional set and
bounded by `c+Y` everywhere deviates from `L` by at most `δ+(c+L)\rho(A)+\E Y`. -/
theorem abs_integral_sub_le_of_split (μ : Measure α) [IsProbabilityMeasure μ]
    (X Y : α → ℝ) (L c δ : ℝ) (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hX0 : ∀ a, 0 ≤ X a) (hY0 : ∀ a, 0 ≤ Y a) (hXY : ∀ᵐ a ∂μ, X a ≤ c + Y a)
    (hXint : Integrable X μ) (hYint : Integrable Y μ)
    (hA : MeasurableSet {a | δ < |X a - L|}) :
    |(∫ a, X a ∂μ) - L| ≤ δ + (c + L) * (μ {a | δ < |X a - L|}).toReal + ∫ a, Y a ∂μ := by
  set A : Set α := {a | δ < |X a - L|} with hAdef
  have hind : Integrable (fun a => (c + L) * A.indicator (fun _ => (1:ℝ)) a) μ :=
    ((integrable_const (1:ℝ)).indicator hA).const_mul (c + L)
  have hptw : ∀ᵐ a ∂μ, |X a - L| ≤ δ + (c + L) * A.indicator (fun _ => (1:ℝ)) a + Y a := by
    filter_upwards [hXY] with a hXYa
    by_cases ha : a ∈ A
    · rw [Set.indicator_of_mem ha]
      have h1 : |X a - L| ≤ X a + L := by
        rw [abs_le]
        exact ⟨by linarith [hX0 a], by linarith [hL]⟩
      have h2 := hXYa
      have h3 := hY0 a
      simp only [mul_one]
      linarith
    · rw [Set.indicator_of_notMem ha]
      have hna : |X a - L| ≤ δ := not_lt.mp ha
      have h3 := hY0 a
      have h4 : (0:ℝ) ≤ c + L := by linarith
      simp only [mul_zero]
      linarith
  have h5 : |(∫ a, X a ∂μ) - L| ≤ ∫ a, |X a - L| ∂μ := by
    have hL' : ∫ _a : α, L ∂μ = L := by simp
    calc |(∫ a, X a ∂μ) - L| = |∫ a, (X a - L) ∂μ| := by
          rw [integral_sub hXint (integrable_const L), hL']
      _ ≤ ∫ a, |X a - L| ∂μ := abs_integral_le_integral_abs
  have h6 : ∫ a, |X a - L| ∂μ
      ≤ ∫ a, (δ + (c + L) * A.indicator (fun _ => (1:ℝ)) a + Y a) ∂μ :=
    integral_mono_ae (hXint.sub (integrable_const L)).abs
      (((integrable_const δ).add hind).add hYint) hptw
  have e1 : ∫ a, (δ + (c + L) * A.indicator (fun _ => (1:ℝ)) a + Y a) ∂μ
      = (∫ a, (δ + (c + L) * A.indicator (fun _ => (1:ℝ)) a) ∂μ) + ∫ a, Y a ∂μ :=
    integral_add ((integrable_const δ).add hind) hYint
  have e2 : ∫ a, (δ + (c + L) * A.indicator (fun _ => (1:ℝ)) a) ∂μ
      = δ + (c + L) * (μ A).toReal := by
    have e3 : ∫ a, (δ + (c + L) * A.indicator (fun _ => (1:ℝ)) a) ∂μ
        = (∫ _a : α, δ ∂μ) + ∫ a, (c + L) * A.indicator (fun _ => (1:ℝ)) a ∂μ :=
      integral_add (integrable_const δ) hind
    rw [e3, integral_const_mul, integral_indicator_const (1:ℝ) hA]
    simp [measureReal_def]
  have h7 : ∫ a, (δ + (c + L) * A.indicator (fun _ => (1:ℝ)) a + Y a) ∂μ
      = δ + (c + L) * (μ A).toReal + ∫ a, Y a ∂μ := by rw [e1, e2]
  linarith

/-- Markov's inequality in the form the error terms use. -/
theorem measure_ge_le_integral_div (μ : Measure α) (T : α → ℝ)
    (hT0 : ∀ a, 0 ≤ T a) (hTint : Integrable T μ) {δ : ℝ} (hδ : 0 < δ) :
    (μ {a | δ ≤ T a}).toReal ≤ (∫ a, T a ∂μ) / δ := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hT0) hTint δ
  rw [measureReal_def] at h
  rw [le_div_iff₀ hδ]
  linarith [h]

/-- **The conditional mean comparison of Step 3** (`sandpile.tex:5228-5246`): if `X` is
within `T` of `L` off an exceptional set `B^c` and its positive part is bounded by `c_y+T`
everywhere, then the mean of the positive part is within an explicit error of
`\max(L,0)`.  Applied with `X` the scaled reflected increment, `T` the scaled terminal
quantity and `B` the event that the conditioned field is positive off the origin, the
three error terms are the ones Step 3 sends to zero. -/
theorem abs_integral_posPart_sub_le (μ : Measure α) [IsProbabilityMeasure μ]
    (X T : α → ℝ) (B : Set α) (L cy δ : ℝ)
    (hδ : 0 < δ) (hcy : 0 ≤ cy)
    (hXm : Measurable X) (hT0 : ∀ a, 0 ≤ T a)
    (hTint : Integrable T μ) (hXint : Integrable (fun a => max (X a) 0) μ)
    (hcomp : ∀ a ∈ B, |X a - L| ≤ T a)
    (hdom : ∀ᵐ a ∂μ, max (X a) 0 ≤ cy + T a) :
    |(∫ a, max (X a) 0 ∂μ) - max L 0|
      ≤ δ + (cy + max L 0) * ((μ Bᶜ).toReal + (∫ a, T a ∂μ) / δ) + ∫ a, T a ∂μ := by
  have hA : MeasurableSet {a | δ < |max (X a) 0 - max L 0|} :=
    measurableSet_lt measurable_const ((hXm.max measurable_const).sub measurable_const).abs
  have hsplit := abs_integral_sub_le_of_split μ (fun a => max (X a) 0) T (max L 0) cy δ
    hδ.le (le_max_right L 0) hcy (fun a => le_max_right _ _) hT0 hdom hXint hTint hA
  have hsub : {a | δ < |max (X a) 0 - max L 0|} ⊆ Bᶜ ∪ {a | δ ≤ T a} := by
    intro a ha
    by_cases hb : a ∈ B
    · refine Or.inr ?_
      have h1 : |max (X a) 0 - max L 0| ≤ |X a - L| := abs_max_sub_max_le_abs (X a) L 0
      exact le_of_lt (lt_of_lt_of_le ha (le_trans h1 (hcomp a hb)))
    · exact Or.inl hb
  have hne : μ Bᶜ + μ {a | δ ≤ T a} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  have hreal : (μ {a | δ < |max (X a) 0 - max L 0|}).toReal
      ≤ (μ Bᶜ).toReal + (μ {a | δ ≤ T a}).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono hne (le_trans (measure_mono hsub) (measure_union_le _ _))
  have hmark := measure_ge_le_integral_div μ T hT0 hTint hδ
  have hcoef : (0:ℝ) ≤ cy + max L 0 := by
    have := le_max_right L (0:ℝ)
    linarith
  have hmono : (cy + max L 0) * (μ {a | δ < |max (X a) 0 - max L 0|}).toReal
      ≤ (cy + max L 0) * ((μ Bᶜ).toReal + (∫ a, T a ∂μ) / δ) :=
    mul_le_mul_of_nonneg_left (le_trans hreal (by linarith)) hcoef
  linarith

/-- **The conditional probability comparison of Step 3**
(`eq:dgt4-gaussian-conditional-contact`, `sandpile.tex:5136-5142`): when the limit `L` is
away from zero, the event `\{X>0\}` differs from its limiting value by at most the
exceptional set plus Markov's bound at level `|L|`. -/
theorem abs_measure_pos_sub_le (μ : Measure α) [IsProbabilityMeasure μ]
    (X T : α → ℝ) (B : Set α) (L : ℝ) (hL : L ≠ 0)
    (hXm : Measurable X) (hT0 : ∀ a, 0 ≤ T a) (hTint : Integrable T μ)
    (hcomp : ∀ a ∈ B, |X a - L| ≤ T a) :
    |(μ {a | 0 < X a}).toReal - (if 0 < L then 1 else 0)|
      ≤ (μ Bᶜ).toReal + (∫ a, T a ∂μ) / |L| := by
  have hLpos : 0 < |L| := abs_pos.mpr hL
  have hXmeas : MeasurableSet {a | 0 < X a} := measurableSet_lt measurable_const hXm
  have hsub : symmDiff {a | 0 < X a} {a : α | 0 < L} ⊆ Bᶜ ∪ {a | |L| ≤ T a} := by
    intro a ha
    by_cases hb : a ∈ B
    · refine Or.inr ?_
      have hbig : |L| ≤ |X a - L| := by
        rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hXa : 0 < X a := h1
          have hLle : L ≤ 0 := not_lt.mp h2
          rw [abs_of_nonpos hLle]
          have hstep : -L ≤ X a - L := by linarith
          exact le_trans hstep (le_abs_self _)
        · have hLpos' : 0 < L := h1
          have hXle : X a ≤ 0 := not_lt.mp h2
          rw [abs_of_pos hLpos', ← abs_neg]
          have hstep : L ≤ -(X a - L) := by linarith
          exact le_trans hstep (le_abs_self _)
      exact le_trans hbig (hcomp a hb)
    · exact Or.inl hb
  have hconst : {a : α | 0 < L} = if 0 < L then (Set.univ : Set α) else ∅ := by
    by_cases h : 0 < L <;> simp [h]
  have hmeasval : (μ {a : α | 0 < L}).toReal = (if 0 < L then 1 else 0) := by
    rw [hconst]
    by_cases h : 0 < L <;> simp [h]
  have hne : μ Bᶜ + μ {a | |L| ≤ T a} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  have hsymm : (μ (symmDiff {a | 0 < X a} {a : α | 0 < L})).toReal
      ≤ (μ Bᶜ).toReal + (μ {a | |L| ≤ T a}).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono hne (le_trans (measure_mono hsub) (measure_union_le _ _))
  have hdiff : |(μ {a | 0 < X a}).toReal - (μ {a : α | 0 < L}).toReal|
      ≤ (μ (symmDiff {a | 0 < X a} {a : α | 0 < L})).toReal := by
    have h1 : MeasurableSet {a : α | 0 < L} := by
      rw [hconst]; by_cases h : 0 < L <;> simp [h]
    simpa [measureReal_def] using
      MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
        (s := {a | 0 < X a}) (t := {a : α | 0 < L})
        hXmeas.nullMeasurableSet h1.nullMeasurableSet
  have hmark := measure_ge_le_integral_div μ T hT0 hTint hLpos
  rw [← hmeasval]
  linarith

end Sandpile
