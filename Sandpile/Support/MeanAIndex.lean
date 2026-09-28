import Mathlib

/-!
# Restricting the scale index to `[1,∞)` and back

`thm:main-explosion`(i)(b) states the parabolic scaling limit over all real scales with the
filter `atTop`, while the estimates of `ssec:scaling-dlt4` hold only for `R ≥ 1`: the rescaled
odometer `𝒰_R(T,x) = R^{-(2-d/2)}u_{⌊R²T⌋}(⌊Rx⌋)` is a nonnegative variable with a uniform
exponential moment only there, and at `R = 0` the prefactor `R^{-(2-d/2)}` is not even the
intended one. The moment theorems of `MeanAMoment` ask their hypotheses at every index, so this
file first restricts the family to `[1,∞)` and then carries the limit back to `atTop` on `ℝ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

/-- **Reindexing a family that converges in distribution.**  Composing with any map
of index sets along which the filters converge. -/
theorem tendstoInDistribution_comp {ι ι' E Ω' : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)]
    [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {X : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι} {l' : Filter ι'}
    (u : ι' → ι) (hu : Tendsto u l' l) (h : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution (fun j => X (u j)) l' Z (fun j => μ (u j)) μ' where
  forall_aemeasurable := fun j => h.forall_aemeasurable (u j)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hu

/-- The inclusion of `[c,∞)` into `ℝ` carries `atTop` to `atTop`. -/
theorem tendsto_val_Ici_atTop (c : ℝ) :
    Tendsto (fun r : Set.Ici c => (r : ℝ)) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ?_
  refine ⟨⟨max b c, Set.mem_Ici.2 (le_max_right _ _)⟩, fun a ha => ?_⟩
  exact le_trans (le_max_left b c) (Subtype.coe_le_coe.2 ha)

/-- A limit along `[c,∞)` is a limit along `atTop` on `ℝ`. -/
theorem tendsto_of_tendsto_val_Ici {α : Type*} [TopologicalSpace α] (c : ℝ)
    (f : ℝ → α) (a : α) (h : Tendsto (fun r : Set.Ici c => f (r : ℝ)) atTop (𝓝 a)) :
    Tendsto f atTop (𝓝 a) :=
  tendsto_comp_val_Ici_atTop.1 h

end Sandpile.Support
