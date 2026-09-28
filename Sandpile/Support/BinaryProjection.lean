import Mathlib

/-!
# The binary conditional projection of a real law

`binaryProjection ν S` collapses a random variable to the conditional mean on `S` and on its
complement, giving a two-valued function whose pushforward is the projection of `ν` onto the
two-cell partition `{S, Sᶜ}`. It preserves the mean of `ν`, agrees `ν`-almost everywhere with the
conditional expectation `ν[id | generateFrom {S}]`, and remains nondegenerate (positive variance,
integrable exponential moments) whenever `S` carries positive mass strictly below `0`. This
removes exponential-moment hypotheses from convex mean lower bounds, by replacing the original law
with its bounded two-point projection.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ENNReal

namespace Sandpile

/-- The conditional-mean projection of `ν` onto the two-cell partition `{S, Sᶜ}`: the piecewise
function equal to the average `⨍ z in S, z ∂ν` on `S` and to `⨍ z in Sᶜ, z ∂ν` on `Sᶜ`. -/
noncomputable def binaryProjection (ν : Measure ℝ) (S : Set ℝ) : ℝ → ℝ :=
  by
    classical
    exact S.piecewise (fun _ => ⨍ z in S, z ∂ν) (fun _ => ⨍ z in Sᶜ, z ∂ν)

/-- `binaryProjection ν S` is measurable, being piecewise-constant on the measurable set `S`. -/
theorem measurable_binaryProjection (ν : Measure ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    Measurable (binaryProjection ν S) := by
  classical
  exact measurable_const.piecewise hS measurable_const

/-- `binaryProjection ν S` is bounded uniformly by the sum of the absolute values of the two cell
averages `⨍ w in S, w ∂ν` and `⨍ w in Sᶜ, w ∂ν`. -/
theorem binaryProjection_bound (ν : Measure ℝ) (S : Set ℝ) (z : ℝ) :
    |binaryProjection ν S z| ≤ |⨍ w in S, w ∂ν| + |⨍ w in Sᶜ, w ∂ν| := by
  classical
  by_cases hz : z ∈ S
  · simp only [binaryProjection, Set.piecewise_eq_of_mem S _ _ hz]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · simp only [binaryProjection, Set.piecewise_eq_of_notMem S _ _ hz]
    exact le_add_of_nonneg_left (abs_nonneg _)

/-- `binaryProjection ν S` is integrable against `ν`, since it takes only the two constant values
`⨍ w in S, w ∂ν` and `⨍ w in Sᶜ, w ∂ν`. -/
theorem integrable_binaryProjection (ν : Measure ℝ) [IsFiniteMeasure ν]
    {S : Set ℝ} (hS : MeasurableSet S) : Integrable (binaryProjection ν S) ν := by
  classical
  exact Integrable.piecewise hS (integrable_const _).integrableOn (integrable_const _).integrableOn

/-- `binaryProjection ν S` has the same `ν`-integral as the identity: splitting the integral over
`S` and `Sᶜ` and evaluating each constant piece with `measure_smul_average` recovers
`∫ z, z ∂ν`. -/
theorem integral_binaryProjection (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hint : Integrable id ν) {S : Set ℝ} (hS : MeasurableSet S) :
    (∫ z, binaryProjection ν S z ∂ν) = ∫ z, z ∂ν := by
  classical
  rw [binaryProjection, integral_piecewise hS (integrable_const _).integrableOn
    (integrable_const _).integrableOn]
  simp only [integral_const]
  rw [measure_smul_average, measure_smul_average]
  simpa using integral_add_compl hS hint

/-- `binaryProjection ν S` agrees `ν`-almost everywhere with the conditional expectation
`ν[id | generateFrom {S}]`, checked by matching set integrals on the four generators of
`generateFrom {S}` (`∅`, `S`, `Sᶜ`, and `Set.univ`). -/
theorem binaryProjection_ae_eq_condExp (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) {S : Set ℝ} (hS : MeasurableSet S) :
    binaryProjection ν S =ᵐ[ν] ν[id | generateFrom {S}] := by
  classical
  have hm := generateFrom_singleton_le hS
  have hSm : MeasurableSet[generateFrom {S}] S := measurableSet_generateFrom rfl
  have hb : StronglyMeasurable[generateFrom {S}] (binaryProjection ν S) :=
    (stronglyMeasurable_const.piecewise hSm stronglyMeasurable_const)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hint
    (fun _ _ _ => (integrable_binaryProjection ν hS).integrableOn) ?_ hb.aestronglyMeasurable
  intro T hT _
  change (∫ z in T, binaryProjection ν S z ∂ν) = ∫ z in T, z ∂ν
  rcases measurableSet_generateFrom_singleton_iff.mp hT with h | h | h | h
  · simp [h]
  · rw [h]
    have he : (∫ z in S, binaryProjection ν S z ∂ν) = ∫ z in S, (⨍ w in S, w ∂ν) ∂ν := by
      apply setIntegral_congr_fun hS
      intro z hz
      exact Set.piecewise_eq_of_mem S _ _ hz
    rw [he, integral_const, measure_smul_average]
  · rw [h]
    have he : (∫ z in Sᶜ, binaryProjection ν S z ∂ν) = ∫ z in Sᶜ, (⨍ w in Sᶜ, w ∂ν) ∂ν := by
      apply setIntegral_congr_fun hS.compl
      intro z hz
      exact Set.piecewise_eq_of_notMem S _ _ hz
    rw [he, integral_const, measure_smul_average]
  · simpa [h] using integral_binaryProjection ν hint hS


/-- If `Set.Iic (-a)` has positive `ν`-mass, its conditional average `⨍ z in Set.Iic (-a), z ∂ν`
is at most `-a`, since every point of the set is at most `-a`. -/
theorem average_Iic_neg_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (a : ℝ) (hpa : 0 < ν (Set.Iic (-a))) :
    (⨍ z in Set.Iic (-a), z ∂ν) ≤ -a := by
  have hp : 0 < ν.real (Set.Iic (-a)) := ENNReal.toReal_pos hpa.ne' (measure_ne_top _ _)
  have hb : (∫ z in Set.Iic (-a), z ∂ν) ≤ ∫ _z in Set.Iic (-a), -a ∂ν := by
    refine integral_mono_ae hint.restrict (integrable_const _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
    exact hz
  rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at hb
  rw [setAverage_eq, smul_eq_mul, ← div_eq_inv_mul, div_le_iff₀ hp]
  nlinarith

/-- A bounded random variable has an integrable exponential and a uniform bound on it. -/
theorem integral_exp_abs_map_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ z, |f z| ≤ M) :
    Integrable (fun z => Real.exp |z|) (ν.map f) ∧
      (∫ z, Real.exp |z| ∂(ν.map f)) ≤ Real.exp M := by
  have hi : Integrable (fun z => Real.exp |f z|) ν :=
    (integrable_const (Real.exp M)).mono' (hf.abs.exp.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (hM z))
  refine ⟨(integrable_map_measure (by fun_prop) hf.aemeasurable).mpr hi, ?_⟩
  rw [integral_map hf.aemeasurable (by fun_prop)]
  calc (∫ z, Real.exp |f z| ∂ν) ≤ ∫ _z, Real.exp M ∂ν :=
      integral_mono hi (integrable_const _) (fun z => Real.exp_le_exp.mpr (hM z))
    _ = Real.exp M := by simp

/-- The projected law has a positive variance whenever one cell lies strictly to the left of
zero. -/
theorem binaryProjection_law_properties (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0) (a : ℝ) (ha : 0 < a)
    (hpa : 0 < ν (Set.Iic (-a))) :
    let ρ := ν.map (binaryProjection ν (Set.Iic (-a)))
    IsProbabilityMeasure ρ ∧ (∫ z, z ∂ρ = 0) ∧ 0 < evariance id ρ ∧
      Integrable (fun z => Real.exp |z|) ρ := by
  classical
  set S := Set.Iic (-a)
  set f := binaryProjection ν S
  have hfm : Measurable f := measurable_binaryProjection ν measurableSet_Iic
  have hfi : Integrable f ν := integrable_binaryProjection ν measurableSet_Iic
  set ρ := ν.map f
  haveI hρ : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hfm.aemeasurable
  have hρmean : (∫ z, z ∂ρ) = 0 := by
    change (∫ z, z ∂(ν.map f)) = 0
    rw [integral_map hfm.aemeasurable (by fun_prop)]
    exact (integral_binaryProjection ν hint measurableSet_Iic).trans hmean
  have hnegative : ∀ z ∈ S, f z ≤ -a := by
    intro z hz
    change S.piecewise (fun _ => ⨍ w in S, w ∂ν) (fun _ => ⨍ w in Sᶜ, w ∂ν) z ≤ -a
    rw [Set.piecewise_eq_of_mem S _ _ hz]
    exact average_Iic_neg_le ν hint a hpa
  have hvar : 0 < evariance id ρ := by
    by_contra hn
    have he : evariance id ρ = 0 := le_antisymm (not_lt.mp hn) zero_le
    have heq := (evariance_eq_zero_iff (measurable_id.aemeasurable : AEMeasurable id ρ)).mp he
    rw [show (∫ z, id z ∂ρ) = 0 from hρmean] at heq
    have hfzero : ∀ᵐ z ∂ν, f z = 0 := by
      exact (ae_of_ae_map hfm.aemeasurable heq)
    have hzero : ν S = 0 := by
      have hnull : ν {z | f z ≠ 0} = 0 := by simpa only [ae_iff, id_eq] using hfzero
      refine measure_mono_null (fun z hz => ?_) hnull
      change f z ≠ 0
      have := hnegative z hz
      linarith
    exact hpa.ne' hzero
  have hexp := (integral_exp_abs_map_le ν f hfm
    (|⨍ z in S, z ∂ν| + |⨍ z in Sᶜ, z ∂ν|) (binaryProjection_bound ν S)).1
  exact ⟨hρ, hρmean, hvar, hexp⟩

end Sandpile
