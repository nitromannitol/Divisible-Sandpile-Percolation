import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Square-integrability from an exponential tail

Square-integrability from an exponential upper tail beyond a threshold. The bound follows by
the layer-cake identity and an integrable exponential tail. `lintegral_sq_eq_lintegral_abs_tail`
rewrites `∫⁻ F²` as the layer-cake integral of `r ↦ μ{|F| > r} · 2r`; `lintegral_initial_linear`
evaluates the contribution of that layer-cake integral up to a threshold `L` in closed form as
`L²`; and `exists_square_bound_of_exponential_tail` combines the two with an exponential tail
bound `μ{|F| > r} ≤ C·exp(-c r)` for `r ≥ L` to produce a uniform bound `L² + M`, with `M` an
`F`-independent constant coming from the tail integral of `2C·r·exp(-c r)`, on the second moment
of any measurable `F` satisfying that tail bound.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

/-- The layer-cake identity for the square: `∫⁻ F²` equals the tail integral of
`r ↦ μ{|F| > r} · 2r` over `r ∈ (0, ∞)`, obtained from
`lintegral_comp_eq_lintegral_meas_lt_mul` applied to `|F|` with weight `g r = 2r`, whose
antiderivative `∫₀ˣ 2r dr = x²` matches `x ↦ x²` composed with `abs`. -/
theorem lintegral_sq_eq_lintegral_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (hF : Measurable F) :
    ∫⁻ ω, ENNReal.ofReal (F ω ^ 2) ∂μ =
      ∫⁻ r in Set.Ioi (0 : ℝ), μ {ω | r < |F ω|} * ENNReal.ofReal (2 * r) := by
  have he (x : ℝ) : (∫ r : ℝ in 0..x, 2 * r) = x ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have h := lintegral_comp_eq_lintegral_meas_lt_mul μ (f := fun ω => |F ω|)
    (g := fun r : ℝ => 2 * r) (Eventually.of_forall fun ω => abs_nonneg _)
    (continuous_abs.measurable.comp hF).aemeasurable
    (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
    (eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) (fun r hr => by
      exact mul_nonneg (by norm_num) hr.le))
  simpa only [he, sq_abs] using h

/-- The integral of the indicator of `2r` on `(0, L]` against the layer-cake measure equals
`L²`, computed directly via `∫₀ᴸ 2r dr = L²`; this is the "up to the threshold" piece of the
layer-cake decomposition used in `exists_square_bound_of_exponential_tail`. -/
theorem lintegral_initial_linear (L : ℝ) (hL : 0 ≤ L) :
    ∫⁻ r in Set.Ioi (0 : ℝ),
      (Set.Ioc (0 : ℝ) L).indicator (fun r => ENNReal.ofReal (2 * r)) r =
      ENNReal.ofReal (L ^ 2) := by
  rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  have he : Set.Ioc (0 : ℝ) L ∩ Set.Ioi 0 = Set.Ioc 0 L := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
    tauto
  rw [he]
  have hint : IntegrableOn (fun r : ℝ => 2 * r) (Set.Ioc 0 L) :=
    (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) L)] (fun r : ℝ => 2 * r) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    exact mul_nonneg (by norm_num) hr.1.le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  congr 1
  rw [← intervalIntegral.integral_of_le hL, intervalIntegral.integral_const_mul, integral_id]
  ring


/-- Given an exponential tail bound `μ{|F| > r} ≤ C·exp(-c r)` valid for all `r ≥ L`, `F` is
square-integrable and `∫ F² ≤ L² + M` for a single constant `M` (built from the tail integral of
`(2C)·r·exp(-c r)` via `integrableOn_rpow_mul_exp_neg_mul_rpow`) that works uniformly over every
such `F`, `L` and threshold. Combines `lintegral_sq_eq_lintegral_abs_tail`,
`lintegral_initial_linear`, and a pointwise bound on the tail integrand splitting at `L`. -/
theorem exists_square_bound_of_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ F : Ω → ℝ, Measurable F → ∀ L : ℝ, 0 ≤ L →
      (∀ r : ℝ, L ≤ r → μ {ω | r < |F ω|} ≤ ENNReal.ofReal (C * Real.exp (-c * r))) →
      Integrable (fun ω => F ω ^ 2) μ ∧ ∫ ω, F ω ^ 2 ∂μ ≤ L ^ 2 + M := by
  set B : ℝ → ℝ := fun r => (2 * C) * (r * Real.exp (-c * r))
  have hBi : Integrable B (volume.restrict (Set.Ioi 0)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 : ℝ)) (p := (1 : ℝ))
      (by norm_num) (by norm_num) hc
    simpa only [B, Real.rpow_one] using h.const_mul (2 * C)
  have hB0 : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] B := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    dsimp [B]
    exact mul_nonneg (mul_nonneg (by norm_num) hC)
      (mul_nonneg hr.le (Real.exp_pos _).le)
  refine ⟨∫ r in Set.Ioi 0, B r, integral_nonneg_of_ae hB0, ?_⟩
  intro F hF L hL htail
  have hpoint : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)),
      μ {ω | r < |F ω|} * ENNReal.ofReal (2 * r) ≤
        (Set.Ioc (0 : ℝ) L).indicator (fun r => ENNReal.ofReal (2 * r)) r +
          ENNReal.ofReal (B r) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    by_cases hrL : r ≤ L
    · rw [Set.indicator_of_mem (show r ∈ Set.Ioc 0 L from ⟨hr, hrL⟩)]
      calc μ {ω | r < |F ω|} * ENNReal.ofReal (2 * r) ≤ 1 * ENNReal.ofReal (2 * r) :=
            mul_le_mul' ((measure_mono (μ := μ) (Set.subset_univ _)).trans_eq (by simp)) le_rfl
        _ ≤ ENNReal.ofReal (2 * r) + ENNReal.ofReal (B r) := by simp
    · rw [Set.indicator_of_notMem (show r ∉ Set.Ioc 0 L from fun h => hrL h.2), zero_add]
      calc μ {ω | r < |F ω|} * ENNReal.ofReal (2 * r) ≤
          ENNReal.ofReal (C * Real.exp (-c * r)) * ENNReal.ofReal (2 * r) :=
            mul_le_mul' (htail r (lt_of_not_ge hrL).le) le_rfl
        _ = ENNReal.ofReal (B r) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg hC (Real.exp_pos _).le)]
          congr 1
          dsimp [B]
          ring
  have hlin : (∫⁻ ω, ENNReal.ofReal (F ω ^ 2) ∂μ) ≤
      ENNReal.ofReal (L ^ 2) + ENNReal.ofReal (∫ r in Set.Ioi 0, B r) := by
    rw [lintegral_sq_eq_lintegral_abs_tail μ F hF]
    refine (lintegral_mono_ae hpoint).trans_eq ?_
    have hAm : Measurable ((Set.Ioc (0 : ℝ) L).indicator
        (fun r : ℝ => ENNReal.ofReal (2 * r))) :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)).indicator
        measurableSet_Ioc
    rw [lintegral_add_left hAm, lintegral_initial_linear L hL,
      ← ofReal_integral_eq_lintegral_ofReal hBi hB0]
  have hFi : Integrable (fun ω => F ω ^ 2) μ := by
    refine ⟨(hF.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg (F ω))]
    exact lt_of_le_of_lt hlin
      (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
  refine ⟨hFi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall fun ω => sq_nonneg (F ω)),
    ← ENNReal.ofReal_add (sq_nonneg L) (integral_nonneg_of_ae hB0)] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (sq_nonneg L) (integral_nonneg_of_ae hB0))).mp hlin

end Sandpile
