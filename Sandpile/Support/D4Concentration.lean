import Sandpile.Support.D4Difference
import Sandpile.Support.HeightLower

/-!
# Uniform pointwise concentration and logarithmic variance in dimension four

This file derives the uniform pointwise concentration bound and the logarithmic variance bound
for the dimension-four odometer, from the square sum and supremum of the finite-time Green
coefficients (`exists_greenTime_norm_bounds_four`). `exists_odometerOf_conc_four` and its
`centeredMassLaw` reformulation `exists_odometer_conc_four` give a two-regime sub-Gaussian and
sub-exponential tail bound for the deviation of the odometer from its mean, uniform over all
scenery laws with a common exponential-moment bound, by transferring the coordinatewise
concentration inequality `Sandpile.Frozen.weighted_exp_concentration` through the finite window of
sites actually touched by the odometer. `exists_odometer_variance_bound_four` then extracts from
the same coefficient bounds that the variance of the odometer grows at most logarithmically in
time.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

/-- The logarithm at time plus two is at most twice the logarithm at time. -/
theorem log_add_two_le_two_log (t : ℕ) (ht : 2 ≤ t) :
    Real.log ((t : ℝ) + 2) ≤ 2 * Real.log (t : ℝ) := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (t : ℝ) + 2)
    (show (t : ℝ) + 2 ≤ (t : ℝ) ^ 2 by nlinarith)
  rwa [Real.log_pow] at h

/-- For every exponential-moment rate `θ₀` and bound `K₀` there are constants `c, C > 0` giving a
uniform, two-regime tail bound `C * exp(-c * min(s ^ 2 / log t, s))` on the probability that the
`iidLaw`-sampled odometer at a site and time `t ≥ 2` deviates from its mean by at least `s`, over
every law `ν` with that exponential moment. -/
theorem exists_odometerOf_conc_four (hVS : Sandpile.External.VarianceScale)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ (x : Site 4) (t : ℕ), 2 ≤ t → ∀ (s : ℝ), 0 ≤ s →
          LatticeProb.iidLaw 4 ν
              {ζ | s ≤ |odometerOf ζ t x -
                ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)|} ≤
            ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2 / Real.log t) s))) := by
  classical
  obtain ⟨M₀, hM₀, hM₂, hMi⟩ := exists_greenTime_norm_bounds_four hVS
  set M := 2 * M₀
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hM2 (t : ℕ) (ht : 2 ≤ t) (x : Site 4) :
      (∑' z : Site 4, greenTime 4 t x z ^ 2) ≤ M * Real.log t := by
    have h1 := hM₂ t x
    have h2 := mul_le_mul_of_nonneg_left (log_add_two_le_two_log t ht) (by linarith : 0 ≤ M₀)
    dsimp [M]
    nlinarith
  have hMinf (t : ℕ) (x y : Site 4) : greenTime 4 t x y ≤ M := by
    have h1 := hMi t x y
    dsimp [M]
    linarith
  obtain ⟨c₀, C₀, hc₀, hC₀, hconc⟩ := Sandpile.Frozen.weighted_exp_concentration.2.1 θ₀ K₀ hθ₀
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  refine ⟨c₀ / M, max C₀ 1, div_pos hc₀ hM0, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro ν hprob hexpint hexp x t ht2 s hs
  have ht : 1 ≤ t := by omega
  have hlog : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  haveI := hprob
  rcases hs.eq_or_lt with hs0 | hspos
  · -- `s = 0`: the bound is at least one and a probability is at most one
    subst hs0
    refine le_trans prob_le_one ?_
    have : (0 : ℝ) ≤ 1 := zero_le_one
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (max C₀ 1 * Real.exp (-(c₀ / M * min ((0:ℝ) ^ 2 / Real.log t) 0))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          simp
  set N := (boxFinset x t).card with hN
  set ℓ : Fin N → ℝ := fun i => greenTime 4 t x (boxEnum x t i) with hℓ
  have hℓnn : ∀ i, 0 ≤ ℓ i := fun i => greenTime_nonneg _ _ _
  obtain ⟨i₀, hi₀⟩ := exists_siteEnum_eq (boxFinset x t)
    (mem_boxFinset (x := x) (y := x) (r := t) (by rw [boxDist_self]; exact Nat.zero_le t))
  have hℓi₀ : (1 : ℝ) ≤ ℓ i₀ := by
    have hval : ℓ i₀ = greenTime 4 t x x := congrArg (greenTime 4 t x) hi₀
    rw [hval]
    exact one_le_greenTime_self t ht x
  have hne : ∃ i, ℓ i ≠ 0 := ⟨i₀, by intro h; rw [h] at hℓi₀; linarith⟩
  -- the two norms of the coefficient vector
  have hTwo : lTwoNorm ℓ ^ 2 = ∑ i, ℓ i ^ 2 := lTwoNorm_sq ℓ
  have hTwoLe : lTwoNorm ℓ ^ 2 ≤ M * Real.log t := by
    rw [hTwo, hℓ]
    have hsum : ∑ i : Fin N, greenTime 4 t x (boxEnum x t i) ^ 2
        = ∑' z : Site 4, greenTime 4 t x z ^ 2 := by
      rw [tsum_greenTime_sq_eq_sum]
      exact sum_boxEnum x t fun z => greenTime 4 t x z ^ 2
    rw [hsum]
    exact hM2 t ht2 x
  have hTwoPos : 0 < lTwoNorm ℓ ^ 2 := by
    rw [hTwo]
    refine lt_of_lt_of_le (pow_pos (by linarith : (0:ℝ) < ℓ i₀) 2) ?_
    exact Finset.single_le_sum (f := fun i : Fin N => ℓ i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
  haveI : Nonempty (Fin N) := ⟨i₀⟩
  have hInfLe : lInfNorm ℓ ≤ M := ciSup_le fun i => hMinf t x _
  have hInfPos : 0 < lInfNorm ℓ := lt_of_lt_of_le (by linarith) (le_lInfNorm ℓ i₀)
  -- the concentration bound in the box coordinates
  have hkey := hconc N ν hprob hexpint hexp (boxOdometer t x)
    (measurable_boxOdometer t x) ℓ hℓnn hne
    (fun ξ i y => abs_boxOdometer_update_le t x ξ i y) s hs
  have hmp := LatticeProb.measurePreserving_pick _ ν (boxEnum x t) (boxEnum_injective x t)
  have hmean : (∫ ξ, boxOdometer t x ξ ∂(Measure.pi fun _ : Fin N => ν))
      = ∫ η, odometerOf η t (0 : Site 4) ∂(LatticeProb.iidLaw 4 ν) := by
    rw [← integral_pick ν (boxEnum x t) (boxEnum_injective x t) (boxOdometer t x)
      (measurable_boxOdometer t x).aestronglyMeasurable,
      integral_congr_ae (Filter.Eventually.of_forall fun ζ => boxOdometer_pick t x ζ)]
    exact integral_odometerOf_eq 4 ν t x
  have hmeasset : MeasurableSet {ξ : Fin N → ℝ | s ≤ |boxOdometer t x ξ -
      ∫ η, boxOdometer t x η ∂(Measure.pi fun _ : Fin N => ν)|} :=
    measurableSet_le measurable_const
      (((measurable_boxOdometer t x).sub measurable_const).abs)
  have hpre : {ζ : Site 4 → ℝ | s ≤ |odometerOf ζ t x -
        ∫ η, odometerOf η t (0 : Site 4) ∂(LatticeProb.iidLaw 4 ν)|}
      = (fun ζ : Site 4 → ℝ => fun i => ζ (boxEnum x t i)) ⁻¹'
        {ξ | s ≤ |boxOdometer t x ξ -
          ∫ η, boxOdometer t x η ∂(Measure.pi fun _ : Fin N => ν)|} := by
    ext ζ
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hmean, boxOdometer_pick t x ζ]
  -- the exponent comparison
  have hmin : (c₀ / M) * min (s ^ 2 / Real.log t) s
      ≤ c₀ * min (s ^ 2 / lTwoNorm ℓ ^ 2) (s / lInfNorm ℓ) := by
    rw [mul_min_of_nonneg _ _ (div_pos hc₀ hM0).le, mul_min_of_nonneg _ _ hc₀.le]
    refine min_le_min ?_ ?_
    · rw [show (c₀ / M) * (s ^ 2 / Real.log t) = c₀ * (s ^ 2 / (M * Real.log t)) by field_simp]
      refine mul_le_mul_of_nonneg_left ?_ hc₀.le
      exact div_le_div_of_nonneg_left (sq_nonneg s) hTwoPos hTwoLe
    · rw [show (c₀ / M) * s = c₀ * (s / M) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hc₀.le
      exact div_le_div_of_nonneg_left hs hInfPos hInfLe
  calc LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | s ≤ |odometerOf ζ t x -
          ∫ η, odometerOf η t (0 : Site 4) ∂(LatticeProb.iidLaw 4 ν)|}
      = (Measure.pi fun _ : Fin N => ν)
          {ξ | s ≤ |boxOdometer t x ξ -
            ∫ η, boxOdometer t x η ∂(Measure.pi fun _ : Fin N => ν)|} := by
        rw [hpre]; exact hmp.measure_preimage hmeasset.nullMeasurableSet
    _ ≤ ENNReal.ofReal (C₀ * Real.exp (-(c₀ *
          min (s ^ 2 / lTwoNorm ℓ ^ 2) (s / lInfNorm ℓ)))) := hkey
    _ ≤ ENNReal.ofReal (max C₀ 1 * Real.exp (-(c₀ / M * min (s ^ 2 / Real.log t) s))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr (by linarith))
          (Real.exp_nonneg _) (le_trans hC₀.le (le_max_left _ _))

/-- The `centeredMassLaw` form of `exists_odometerOf_conc_four`: the same two-regime tail bound
for the deviation of the odometer, sampled by `centeredMassLaw`, from the mean odometer. -/
theorem exists_odometer_conc_four (hVS : Sandpile.External.VarianceScale)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ (x : Site 4) (t : ℕ), 2 ≤ t → ∀ (s : ℝ), 0 ≤ s →
          centeredMassLaw 4 ν
              {σ | s ≤ |odometer σ t x - meanOdometer (centeredMassLaw 4 ν) t|} ≤
            ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2 / Real.log t) s))) := by
  obtain ⟨c, C, hc, hC, hconc⟩ := exists_odometerOf_conc_four hVS θ₀ K₀ hθ₀
  refine ⟨c, C, hc, hC, fun ν hprob hexpint hexp x t ht s hs => ?_⟩
  haveI := hprob
  have hd1 : 1 ≤ 4 := by norm_num
  have hmeas : MeasurableSet {ζ : Site 4 → ℝ | s ≤ |odometerOf ζ t x -
      ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)|} :=
    measurableSet_le measurable_const (((measurable_odometerOf t x).sub measurable_const).abs)
  have hpre : {σ : Site 4 → ℝ | s ≤ |odometer σ t x - meanOdometer (centeredMassLaw 4 ν) t|}
      = scenery 4 ⁻¹' {ζ : Site 4 → ℝ | s ≤ |odometerOf ζ t x -
          ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)|} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_preimage, meanOdometer_eq 4 ν hd1 t,
      congrFun (odometer_eq_odometerOf σ t) x]
  rw [hpre, centeredMassLaw_scenery_preimage 4 ν hd1 hmeas]
  exact hconc ν hprob hexpint hexp x t ht s hs

/-- The variance grows at most logarithmically in time. -/
theorem exists_odometer_variance_bound_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : Integrable (fun z => z ^ 2) ν) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (t : ℕ) (x : Site 4),
      ∫ σ, (odometer σ t x - meanOdometer (centeredMassLaw 4 ν) t) ^ 2
          ∂(centeredMassLaw 4 ν) ≤ V * Real.log ((t : ℝ) + 2) := by
  obtain ⟨M, hM, hM2, -⟩ := exists_greenTime_norm_bounds_four hVS
  obtain ⟨C, hC, hb⟩ := exists_odometer_moment_bound (d := 4) (p := (2 : ℝ)) le_rfl
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hpm : 0 ≤ pairMoment ν (2 : ℝ) := pairMoment_nonneg ν _
  refine ⟨C * pairMoment ν (2 : ℝ) * M, by positivity, fun t x => ?_⟩
  have h := hb ν ‹_› (integrable_abs_rpow_two ν hsq) t x
  rw [integral_odometerOf_eq 4 ν t x] at h
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one] at h
  have hmeas : AEStronglyMeasurable
      (fun ζ : Site 4 → ℝ =>
        (odometerOf ζ t x - ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) ^ 2)
      (LatticeProb.iidLaw 4 ν) :=
    (((measurable_odometerOf t x).sub measurable_const).pow_const 2).aestronglyMeasurable
  have hEq : ∫ σ, (odometer σ t x - meanOdometer (centeredMassLaw 4 ν) t) ^ 2
        ∂(centeredMassLaw 4 ν)
      = ∫ ζ, (odometerOf ζ t x - ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) ^ 2
        ∂(LatticeProb.iidLaw 4 ν) := by
    rw [← integral_scenery 4 ν (by norm_num) hmeas, meanOdometer_eq 4 ν (by norm_num) t]
    exact integral_congr_ae (Filter.Eventually.of_forall fun σ => by
      simp only [congrFun (odometer_eq_odometerOf σ t) x])
  rw [hEq]
  have hrpow : (∫ ζ, (odometerOf ζ t x - ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) ^ 2
        ∂(LatticeProb.iidLaw 4 ν)) =
      ∫ ζ, |odometerOf ζ t x - ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)| ^ (2 : ℝ)
        ∂(LatticeProb.iidLaw 4 ν) := by
    congr 1
    funext ζ
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [hrpow]
  refine h.trans ?_
  have hb := mul_le_mul_of_nonneg_left (hM2 t x) (show 0 ≤ C * pairMoment ν 2 by positivity)
  nlinarith

end Sandpile
