import Sandpile.External.Stopping.QuantileEventVersions

/-!
# Stopping versions of kernel quantiles

Countably many adapted distribution-function versions determine an adapted
stopping-clock version of a kernel quantile. The version is equal almost surely
to the original quantile and therefore preserves its joint distribution.
-/

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The filtration obtained by adjoining an independently measured parameter. -/
def parameterFiltration {Ω A : Type*} {m : MeasurableSpace Ω} [mA : MeasurableSpace A]
    (F : Filtration ℝ≥0 m) : Filtration ℝ≥0 (m.prod mA) where
  seq t := (F t).prod mA
  mono' := by
    intro a b hab
    exact sup_le_sup (MeasurableSpace.comap_mono (F.mono hab)) le_rfl
  le' t := sup_le_sup (MeasurableSpace.comap_mono (F.le t)) le_rfl

/-- A nonnegative time clipped to the unit interval. -/
noncomputable def unitTime (t : ℝ≥0) : I :=
  ⟨min (t : ℝ) 1, le_min t.2 zero_le_one, min_le_right _ _⟩

/-- A unit-interval clock, regarded as a nonnegative time. -/
def unitClock {Ω : Type*} (τ : Ω → I) (ω : Ω) : ℝ≥0 :=
  ⟨τ ω, (τ ω).2.1⟩

/-- Clipping a test time at one does not change a unit-clock sublevel event. -/
theorem unitClock_le_iff {Ω : Type*} (τ : Ω → I) (ω : Ω) (t : ℝ≥0) :
    unitClock τ ω ≤ t ↔ τ ω ≤ unitTime t := by
  change (τ ω : ℝ) ≤ (t : ℝ) ↔ (τ ω : ℝ) ≤ min (t : ℝ) 1
  simp only [le_min_iff, (τ ω).2.2, and_true]

/-- If the distribution function has adapted versions on a dense countable
set of times, its kernel quantile has a bounded stopping-clock version in the
right-continuation of the product filtration. -/
theorem exists_stopping_version_of_ae_kernel_cdf
    {Ω ι : Type*} [m : MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [SFinite P] (F : Filtration ℝ≥0 m)
    (κ : Kernel Ω I) [IsMarkovKernel κ] (time : ι → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (hversions : ∀ i, ∃ f : Ω → ℝ, @Measurable Ω ℝ (F (time i)) inferInstance f ∧
      f =ᵐ[P] fun ω => (κ ω).real (Icc 0 (unitTime (time i)))) :
    ∃ τ : Ω × I → ℝ≥0,
      IsStoppingTime (parameterFiltration F).rightCont (fun p => (τ p : ℝ≥0∞)) ∧
      (∀ p, τ p ≤ 1) ∧
      τ =ᵐ[P.prod volume] unitClock (fun p => clockQuantile (κ p.1) p.2) := by
  have hevents : ∀ i, ∃ s : Set (Ω × I),
      MeasurableSet[(parameterFiltration F) (time i)] s ∧
      ∀ᵐ p ∂(P.prod volume), p ∈ s ↔
        unitClock (fun p => clockQuantile (κ p.1) p.2) p ≤ time i := by
    intro i
    obtain ⟨f, hf, hfeq⟩ := hversions i
    obtain ⟨s, hs, hseq⟩ :=
      @exists_quantile_sublevel_event_of_ae_cdf Ω m P inferInstance (F (time i)) κ
        inferInstance (unitTime (time i)) f hf hfeq
    refine ⟨s, hs, ?_⟩
    filter_upwards [hseq] with p hp
    exact hp.trans (unitClock_le_iff _ _ _).symm
  choose events hmeas heq using hevents
  apply exists_rightCont_stopping_of_ae_threshold_events (P.prod volume)
    (parameterFiltration F) time events 1 hdense
    (unitClock (fun p => clockQuantile (κ p.1) p.2))
  · exact Filter.Eventually.of_forall fun p => (clockQuantile (κ p.1) p.2).2.2
  · exact hmeas
  · exact heq

end Sandpile.External.Stopping
