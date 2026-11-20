import Sandpile.External.Stopping.AdaptedKernelQuantile
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Representation of causal joint laws

A joint path-clock law whose conditional clock distribution is adapted can be
realized using an independent uniform parameter and an adapted quantile. The
construction is the randomization argument in Coquet and Toldo, Section 2.3.1.
-/

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped ProbabilityTheory

namespace Sandpile.External.Stopping

/-- An adapted conditional clock kernel represents its joint law by an
independent uniform parameter. -/
theorem exists_adapted_quantile_of_joint_law
    {Ω : Type*} [m : MeasurableSpace Ω] (F : Filtration I m)
    (ρ : Measure (Ω × I)) [IsFiniteMeasure ρ]
    (hρ : ∀ t, @Measurable Ω ℝ (F t) inferInstance
      (fun ω => (ρ.condKernel ω).real (Icc 0 t))) :
    ∃ τ : Ω × I → I, Measurable τ ∧
      (∀ t, MeasurableSet[(F t).prod inferInstance] {p | τ p ≤ t}) ∧
      (ρ.fst.prod volume).map (fun p => (p.1, τ p)) = ρ := by
  refine ⟨fun p => clockQuantile (ρ.condKernel p.1) p.2,
    (clockQuantile_kernel ρ.condKernel).1,
    clockQuantile_adapted F ρ.condKernel hρ, ?_⟩
  rw [map_clockQuantile_prod, ρ.disintegrate]

end Sandpile.External.Stopping
