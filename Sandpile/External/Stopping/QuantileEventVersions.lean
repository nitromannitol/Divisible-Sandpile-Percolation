import Sandpile.External.Stopping.AdaptedKernelQuantile
import Sandpile.External.Stopping.ThresholdClockRepresentation

/-!
# Adapted versions of quantile events

An almost everywhere adapted version of a conditional distribution function
provides an adapted version of the corresponding quantile sublevel event.
This connects disintegration with the countable threshold construction in the
randomized stopping argument of Coquet and Toldo, Section 2.3.1.
-/

open MeasureTheory ProbabilityTheory Set Filter unitInterval

namespace Sandpile.External.Stopping

/-- An adapted version of a kernel distribution function yields an adapted
version of the quantile sublevel event on the independent product space. -/
theorem exists_quantile_sublevel_event_of_ae_cdf
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (m₀ : MeasurableSpace Ω) (κ : @Kernel Ω I m inferInstance) [IsMarkovKernel κ]
    (t : I) (f : Ω → ℝ) (hf : @Measurable Ω ℝ m₀ inferInstance f)
    (hversion : f =ᵐ[P] fun ω => (κ ω).real (Icc 0 t)) :
    ∃ s : Set (Ω × I), @MeasurableSet (Ω × I) (m₀.prod inferInstance) s ∧
      ∀ᵐ p ∂(@Measure.prod Ω I m inferInstance P volume), p ∈ s ↔ clockQuantile (κ p.1) p.2 ≤ t := by
  refine ⟨{p | (p.2 : ℝ) ≤ f p.1}, ?_, ?_⟩
  · exact measurableSet_le measurable_snd.subtype_val (hf.comp measurable_fst)
  · filter_upwards [(@Measure.quasiMeasurePreserving_fst Ω I m inferInstance P volume inferInstance).ae_eq_comp hversion]
      with p hp
    change f p.1 = (κ p.1).real (Icc 0 t) at hp
    rw [clockQuantile_le_iff, hp]

end Sandpile.External.Stopping
