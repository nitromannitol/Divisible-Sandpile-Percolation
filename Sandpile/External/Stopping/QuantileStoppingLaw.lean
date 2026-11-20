import Sandpile.External.Stopping.QuantileStoppingVersion
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Joint laws of adapted stopping versions

A stopping version of a kernel quantile has the same joint law as the
original disintegration. This preserves both stopped rewards and any
almost-sure clock constraint when replacing the quantile by an adapted rule.
-/

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped NNReal ENNReal ProbabilityTheory

namespace Sandpile.External.Stopping

/-- Replacing a quantile by an almost surely equal clock preserves the joint
law obtained from the kernel. -/
theorem map_stopping_version_of_ae_kernel_quantile
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (κ : Kernel Ω I) [IsMarkovKernel κ] (τ : Ω × I → ℝ≥0)
    (hτ : τ =ᵐ[P.prod volume] unitClock (fun p => clockQuantile (κ p.1) p.2)) :
    (P.prod volume).map (fun p => (p.1, τ p)) =
      (P ⊗ₘ κ).map (fun p => (p.1, unitClock id p.2)) := by
  have hbase : Measurable (fun p : Ω × I => (p.1, clockQuantile (κ p.1) p.2)) :=
    measurable_fst.prodMk (clockQuantile_kernel κ).1
  have hunit : Measurable (unitClock (id : I → I)) := by
    change Measurable (fun u : I => (⟨(u : ℝ), u.2.1⟩ : ℝ≥0))
    exact (measurable_subtype_coe : Measurable (fun u : I => (u : ℝ))).subtype_mk
  have hconvert : Measurable (fun p : Ω × I => (p.1, unitClock id p.2)) :=
    measurable_fst.prodMk (hunit.comp measurable_snd)
  calc
    (P.prod volume).map (fun p => (p.1, τ p)) =
        (P.prod volume).map (fun p => (p.1, unitClock (fun p =>
          clockQuantile (κ p.1) p.2) p)) := by
            apply Measure.map_congr
            filter_upwards [hτ] with p hp
            rw [hp]
    _ = (P ⊗ₘ κ).map (fun p => (p.1, unitClock id p.2)) := by
      rw [← map_clockQuantile_prod P κ, Measure.map_map hconvert hbase]
      rfl

/-- A joint law whose conditional CDF has adapted versions on a countable dense
set is realized by an adapted randomized stopping clock with the same law. -/
theorem exists_stopping_version_of_joint_law
    {Ω ι : Type*} [m : MeasurableSpace Ω] [Countable ι]
    (F : Filtration ℝ≥0 m) (ρ : Measure (Ω × I)) [IsFiniteMeasure ρ]
    (time : ι → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (hversions : ∀ i, ∃ f : Ω → ℝ, @Measurable Ω ℝ (F (time i)) inferInstance f ∧
      f =ᵐ[ρ.fst] fun ω => (ρ.condKernel ω).real (Icc 0 (unitTime (time i)))) :
    ∃ τ : Ω × I → ℝ≥0,
      IsStoppingTime (parameterFiltration F).rightCont (fun p => (τ p : ℝ≥0∞)) ∧
      (∀ p, τ p ≤ 1) ∧
      (ρ.fst.prod volume).map (fun p => (p.1, τ p)) =
        ρ.map (fun p => (p.1, unitClock id p.2)) := by
  obtain ⟨τ, hτ, hτ1, hτeq⟩ :=
    exists_stopping_version_of_ae_kernel_cdf ρ.fst F ρ.condKernel time hdense hversions
  refine ⟨τ, hτ, hτ1, ?_⟩
  rw [map_stopping_version_of_ae_kernel_quantile ρ.fst ρ.condKernel τ hτeq,
    ρ.disintegrate]

end Sandpile.External.Stopping
