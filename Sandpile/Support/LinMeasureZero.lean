import Sandpile.Support.ContDGT4Membrane

/-!
# From vanishing second moment to convergence in measure

This file passes from the vanishing second moment of a family of `L²` random variables to their
convergence in measure, and then restates convergence in measure as the more concrete statement
that `P {ω | ε < |Z R ω|}` tends to zero for every `ε > 0`. Together these give the passage used
to upgrade convergence of a countable dense family of test-function pairings to convergence in
probability of the underlying distributions.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- A family of `L²` random variables whose second moments tend to zero converges
to zero in measure. -/
theorem tendstoInMeasure_zero_of_tendsto_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : ℝ → Ω → ℝ)
    (hmem : ∀ R : ℝ, MemLp (Z R) 2 P)
    (hZlim : Tendsto (fun R : ℝ => ∫ ω, (Z R ω) ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P Z atTop 0 := by
  have hZint : ∀ R : ℝ, Integrable (fun ω => (Z R ω) ^ 2) P := fun R =>
    (MeasureTheory.memLp_two_iff_integrable_sq (hmem R).aestronglyMeasurable).mp (hmem R)
  have heL : Tendsto (fun R : ℝ => eLpNorm (Z R) 2 P) atTop (𝓝 0) :=
    Sandpile.Support.tendsto_eLpNorm_of_tendsto_integral_sq P Z
      (fun R => (hmem R).aestronglyMeasurable) hZint hZlim
  refine MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    (fun R => (hmem R).aestronglyMeasurable) aestronglyMeasurable_zero ?_
  simp only [sub_zero]
  exact heL

/-- The measure form of convergence in measure: a family converging to zero in
measure has, for every `ε > 0`, the probability of the event `{|Z_R| > ε}`
tending to zero.  This is the form in which the second conjunct of
`lem:dgt4-linearization-from-survival` reads its conclusion. -/
theorem tendsto_toReal_measure_lt_of_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (Z : ℝ → Ω → ℝ)
    (h : TendstoInMeasure P Z atTop 0) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun R : ℝ => (P {ω | ENNReal.ofReal ε < ENNReal.ofReal |Z R ω|}).toReal)
      atTop (𝓝 0) := by
  have hnorm : Tendsto (fun R : ℝ => P {ω | ε ≤ ‖Z R ω - (0 : Ω → ℝ) ω‖}) atTop (𝓝 0) :=
    (MeasureTheory.tendstoInMeasure_iff_norm.mp h) ε hε
  have hnormR : Tendsto (fun R : ℝ => (P {ω | ε ≤ ‖Z R ω - (0 : Ω → ℝ) ω‖}).toReal)
      atTop (𝓝 0) := by
    have h' := ENNReal.tendsto_toReal_iff (fun R => measure_ne_top _ _) (by simp) |>.mpr hnorm
    simpa using h'
  have hsub : ∀ R : ℝ, {ω | ENNReal.ofReal ε < ENNReal.ofReal |Z R ω|} ⊆
      {ω | ε ≤ ‖Z R ω - (0 : Ω → ℝ) ω‖} := by
    intro R ω hω
    have hne : Z R ω ≠ 0 := by
      intro h0
      simp [h0] at hω
    simp only [Set.mem_setOf_eq] at hω
    have h1 : ε < |Z R ω| := (ENNReal.ofReal_lt_ofReal_iff (abs_pos.mpr hne)).mp hω
    simpa using h1.le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnormR
    (fun R => ENNReal.toReal_nonneg) (fun R => ?_)
  exact ENNReal.toReal_mono (measure_ne_top _ _) (MeasureTheory.measure_mono (hsub R))

end Sandpile.Support
