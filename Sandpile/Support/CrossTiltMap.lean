import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pushforward and product facts for exponential tilts

Two facts about exponential tilts that Mathlib 4.32 does not have, needed for the
Cameron--Martin shift of Step 3 of `prop:fixed-scale-crossings`
(`sandpile.tex:2334-2350`).

* `tilted_map`: a tilt whose exponent factors through a map pushes forward to the tilt of
  the pushforward.  This is what lets the shift be computed in the law of the coordinates
  the exploration reads instead of on the underlying space.
* `tilted_prod_left`: tilting a product measure by a function of the first coordinate tilts
  the first factor and leaves the second alone.  This is the independence step: the shift
  acts only on the one Gaussian direction it is built from.

Both are stated for arbitrary measurable spaces and import only Mathlib.
-/

open MeasureTheory

namespace Sandpile.Support

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Pushing an exponential tilt forward along a map through which its exponent factors:
`(μ.tilted (g ∘ Φ)).map Φ = (μ.map Φ).tilted g`. -/
theorem tilted_map (μ : Measure α) [SFinite μ] {Φ : α → β} (hΦ : Measurable Φ)
    {g : β → ℝ} (hg : Measurable g) :
    (μ.tilted (fun x => g (Φ x))).map Φ = (μ.map Φ).tilted g := by
  have hexp : Measurable fun y => Real.exp (g y) := Real.measurable_exp.comp hg
  have hZ : ∫ x, Real.exp (g (Φ x)) ∂μ = ∫ y, Real.exp (g y) ∂(μ.map Φ) :=
    (integral_map hΦ.aemeasurable hexp.aestronglyMeasurable).symm
  ext s hs
  rw [Measure.map_apply hΦ hs, tilted_apply' _ _ (hΦ hs), tilted_apply' _ _ hs, hZ]
  have hFmeas : Measurable fun y : β =>
      ENNReal.ofReal (Real.exp (g y) / ∫ y, Real.exp (g y) ∂(μ.map Φ)) := by
    exact (hexp.div_const _).ennreal_ofReal
  rw [← lintegral_indicator hs, ← lintegral_indicator (hΦ hs),
    lintegral_map (hFmeas.indicator hs) hΦ]
  exact lintegral_congr fun x => by
    by_cases hx : Φ x ∈ s <;>
      simp [hx, Set.indicator_of_mem, Set.indicator_of_notMem]

/-- Tilting a product measure by a function of the first coordinate tilts the first factor
and leaves the second unchanged. -/
theorem tilted_prod_left (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {g : α → ℝ} (hg : Measurable g) :
    (μ.prod ν).tilted (fun p : α × β => g p.1) = (μ.tilted g).prod ν := by
  have hexp : Measurable fun x => Real.exp (g x) := Real.measurable_exp.comp hg
  have hfst : (μ.prod ν).map Prod.fst = μ := by rw [← Measure.fst, Measure.fst_prod]
  have hZ : ∫ x, Real.exp (g x) ∂μ = ∫ p : α × β, Real.exp (g p.1) ∂(μ.prod ν) := by
    conv_lhs => rw [← hfst]
    exact integral_map measurable_fst.aemeasurable hexp.aestronglyMeasurable
  have hFmeas : Measurable fun x : α =>
      ENNReal.ofReal (Real.exp (g x) / ∫ x, Real.exp (g x) ∂μ) := (hexp.div_const _).ennreal_ofReal
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  have hrect : MeasurableSet (s ×ˢ t) := hs.prod ht
  rw [tilted_apply' _ _ hrect, ← hZ, tilted_apply' _ _ hs]
  rw [← lintegral_indicator hrect, ← lintegral_indicator hs]
  have hmeas2 : Measurable fun p : α × β => (s ×ˢ t).indicator
      (fun q : α × β => ENNReal.ofReal (Real.exp (g q.1) / ∫ x, Real.exp (g x) ∂μ)) p :=
    (hFmeas.comp measurable_fst).indicator hrect
  rw [lintegral_prod _ hmeas2.aemeasurable]
  have hstep : ∀ x : α, ∫⁻ y, (s ×ˢ t).indicator
      (fun p : α × β => ENNReal.ofReal (Real.exp (g p.1) / ∫ x, Real.exp (g x) ∂μ)) (x, y) ∂ν
      = s.indicator (fun x : α => ENNReal.ofReal (Real.exp (g x) / ∫ x, Real.exp (g x) ∂μ)) x
          * ν t := by
    intro x
    have hind : ∀ y : β, (s ×ˢ t).indicator
        (fun p : α × β => ENNReal.ofReal (Real.exp (g p.1) / ∫ x, Real.exp (g x) ∂μ)) (x, y)
        = s.indicator (fun x : α => ENNReal.ofReal (Real.exp (g x) / ∫ x, Real.exp (g x) ∂μ)) x
            * t.indicator (fun _ => (1 : ENNReal)) y := by
      intro y
      by_cases hx : x ∈ s <;> by_cases hy : y ∈ t <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, hy, Set.mem_prod]
    simp_rw [hind]
    have hone : Measurable fun y : β => t.indicator (fun _ : β => (1 : ENNReal)) y :=
      measurable_const.indicator ht
    rw [lintegral_const_mul _ hone, lintegral_indicator ht]
    simp
  simp_rw [hstep]
  rw [lintegral_mul_const _ (hFmeas.indicator hs)]

end Sandpile.Support
