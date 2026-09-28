import Sandpile.Support.TailSquare
import Sandpile.Frozen.D4PointwiseLinearization

/-!
# Second-Moment Bound on the Dimension-Four Linearization Error

The dimension-four pointwise linearization error is negligible in the second moment
after normalization by the square root of logarithmic time.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

/-- There is a constant `M ≥ 0` such that for every `t ≥ 3` and site `x`, the squared
linearization error `(odometerOf ζ t x - E[odometerOf · t 0] - membrane ζ t x)²` is
integrable in `ζ` and its integral is at most `(1 + log log t)² + M`. Obtained by
combining the exponential tail `exists_pointwise_linearization_four` with the square
bound `exists_square_bound_of_exponential_tail`. -/
theorem exists_linearization_second_moment_four (hVS : External.VarianceScale)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℕ, 3 ≤ t → ∀ x : Site 4,
      Integrable (fun ζ => (odometerOf ζ t x -
        (∫ η, odometerOf η t 0 ∂LatticeProb.iidLaw 4 ν) - membrane ζ t x) ^ 2)
          (LatticeProb.iidLaw 4 ν) ∧
      (∫ ζ, (odometerOf ζ t x - (∫ η, odometerOf η t 0 ∂LatticeProb.iidLaw 4 ν) -
        membrane ζ t x) ^ 2 ∂LatticeProb.iidLaw 4 ν) ≤
        (1 + Real.log (Real.log t)) ^ 2 + M := by
  obtain ⟨c, C, hc, hC, htail⟩ := exists_pointwise_linearization_four hVS ν hmean θ hθ hexp
  obtain ⟨M, hM, hb⟩ :=
    exists_square_bound_of_exponential_tail (LatticeProb.iidLaw 4 ν) c C hc hC.le
  refine ⟨M, hM, ?_⟩
  intro t ht x
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hL : 0 < 1 + Real.log (Real.log (t : ℝ)) :=
    lt_of_lt_of_le zero_lt_one (log_time_bounds_four htR).2.1
  apply hb _ (((measurable_odometerOf t x).sub measurable_const).sub (measurable_membrane t x))
    _ hL.le
  intro r hr
  have hr0 : 0 ≤ r := hL.le.trans hr
  have hmin : min (r ^ 2 / (1 + Real.log (Real.log (t : ℝ)))) r = r := by
    apply min_eq_right
    rw [le_div_iff₀ hL]
    nlinarith
  have h := htail t ht r hr0 x
  rw [hmin] at h
  simpa only [neg_mul, Pi.sub_apply] using h

/-- The normalization `((1 + log log t)² + M) / log t` tends to `0` as `t → ∞`, for any
fixed `M`. Proved from `Real.tendsto_pow_log_div_mul_add_atTop` applied at exponents `1`
and `2`, combined by `ring` into the stated quotient. -/
theorem tendsto_log_log_square_div_log (M : ℝ) :
    Tendsto (fun t : ℕ => ((1 + Real.log (Real.log t)) ^ 2 + M) / Real.log t)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun t : ℕ => Real.log (t : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h0 := (tendsto_const_nhds (x := 1 + M)).div_atTop hlog
  have h1 : Tendsto (fun t : ℕ => Real.log (Real.log t) / Real.log t) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hlog
  have h2 : Tendsto (fun t : ℕ => Real.log (Real.log t) ^ 2 / Real.log t) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hlog
  have h := (h0.add (h1.const_mul 2)).add h2
  have he (t : ℕ) : (1 + M) / Real.log t + 2 * (Real.log (Real.log t) / Real.log t) +
      Real.log (Real.log t) ^ 2 / Real.log t =
      ((1 + Real.log (Real.log t)) ^ 2 + M) / Real.log t := by ring
  simpa only [he, mul_zero, zero_add, add_zero] using h

/-- The linearization error's second moment, normalized by `Real.log t`, tends to `0` as
`t → ∞` at every fixed site `x`. Obtained by squeezing between `0` and the bound of
`exists_linearization_second_moment_four`, whose normalized limit is
`tendsto_log_log_square_div_log`. -/
theorem tendsto_linearization_second_moment_div_log_four (hVS : External.VarianceScale)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) (x : Site 4) :
    Tendsto (fun t : ℕ => (∫ ζ, (odometerOf ζ t x -
      (∫ η, odometerOf η t 0 ∂LatticeProb.iidLaw 4 ν) - membrane ζ t x) ^ 2
        ∂LatticeProb.iidLaw 4 ν) / Real.log t) atTop (𝓝 0) := by
  obtain ⟨M, hM, hb⟩ := exists_linearization_second_moment_four hVS ν hmean θ hθ hexp
  refine squeeze_zero' ?_ ?_ (tendsto_log_log_square_div_log M)
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with t ht
    apply div_nonneg (integral_nonneg fun ζ => sq_nonneg _)
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t))
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with t ht
    exact div_le_div_of_nonneg_right (hb t ht x).2
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t)))

end Sandpile
