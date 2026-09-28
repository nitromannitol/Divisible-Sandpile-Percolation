import Sandpile.Support.MeanAInterp
import Sandpile.Support.MeanAIndex
import Sandpile.Support.LinStationary

/-!
# From the interpolated parabolic limit to the lattice value

The rescaled odometer `rescaledOdometer d R T x` at a mesh point agrees with the multilinear
interpolation `multilinearInterp` of the rescaled odometer field, so any compact modulus of
continuity for the interpolation forces the two to differ by an amount tending to `0` in
measure (`rescaledOdometer_sub_interp_tendstoInMeasure`), because the mesh point of `x`
converges to `x`. Combined with convergence in distribution of the one-point interpolation
value, this transports the limit to the rescaled odometer itself
(`tendstoInDistribution_rescaled_of_interp`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support
open Sandpile.Continuum

/-- Compact equicontinuity makes the rounding error negligible in probability. -/
theorem rescaledOdometer_sub_interp_tendstoInMeasure
    (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ) (x : Space d)
    (hmod : ∀ K : Set (Space d), IsCompact K →
      ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
        Sandpile.centeredMassLaw d ν
          {σ | ∃ z ∈ K, ∃ z' ∈ K, dist z z' < δ ∧
            η < |multilinearInterp R
              (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z -
              multilinearInterp R
              (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z'|} ≤
          ENNReal.ofReal ε) :
    TendstoInMeasure (Sandpile.centeredMassLaw d ν)
      (fun R σ => rescaledOdometer d R T x σ - multilinearInterp R
        (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) x)
      atTop 0 := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro η hη
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  · intro ε hε
    obtain ⟨δ, hδ, hb⟩ := hmod (Metric.closedBall x 1) (isCompact_closedBall x 1)
      (ε / 2) (η / 2) (by linarith) (by linarith)
    have hmem := (tendsto_meshPoint x).eventually
      (Metric.closedBall_mem_nhds x zero_lt_one)
    have hdist : ∀ᶠ R : ℝ in atTop, dist (meshPoint R x) x < δ :=
      (tendsto_meshPoint x).eventually (Metric.ball_mem_nhds x hδ)
    filter_upwards [eventually_ge_atTop (1 : ℝ), hmem, hdist] with R hR hm hd
    have hsub : {σ | η ≤ ‖rescaledOdometer d R T x σ - multilinearInterp R
        (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) x - 0‖} ⊆
        {σ | ∃ z ∈ Metric.closedBall x 1, ∃ z' ∈ Metric.closedBall x 1,
          dist z z' < δ ∧ η / 2 < |multilinearInterp R
            (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z -
            multilinearInterp R
            (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z'|} := by
      intro σ hσ
      simp only [Set.mem_setOf_eq] at hσ
      refine ⟨meshPoint R x, hm, x, Metric.mem_closedBall_self (by norm_num), hd, ?_⟩
      rw [rescaledOdometer_eq_multilinearInterp d R T (by linarith) x σ,
        sub_zero, Real.norm_eq_abs] at hσ
      linarith
    have hbound := (measure_mono hsub).trans (hb R hR)
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hbound |>.trans_eq
      (ENNReal.toReal_ofReal (by linarith : 0 ≤ ε / 2)) |>.trans_lt (by linarith)

/-- The one-point interpolation limit and its compact modulus imply the lattice limit. -/
theorem tendstoInDistribution_rescaled_of_interp {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → ℝ) (T : ℝ) (x : Space d)
    (hconv : TendstoInDistribution
      (fun (R : ℝ) σ => multilinearInterp R
        (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) x)
      atTop U (fun _ => Sandpile.centeredMassLaw d ν) P)
    (hmod : ∀ K : Set (Space d), IsCompact K →
      ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
        Sandpile.centeredMassLaw d ν
          {σ | ∃ z ∈ K, ∃ z' ∈ K, dist z z' < δ ∧
            η < |multilinearInterp R
              (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z -
              multilinearInterp R
              (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z'|} ≤
          ENNReal.ofReal ε) :
    TendstoInDistribution (fun R : ℝ => rescaledOdometer d R T x)
      atTop U (fun _ => Sandpile.centeredMassLaw d ν) P := by
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ hconv
    (rescaledOdometer_sub_interp_tendstoInMeasure d ν T x hmod)
  intro R
  exact (measurable_const.mul (Sandpile.measurable_odometer _ _)).aemeasurable

end Sandpile.Support
