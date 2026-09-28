import Sandpile.Support.FiniteLindeberg
import Sandpile.Support.ScalarComposition
import Sandpile.Support.SmoothCutoff
import Sandpile.Support.ExponentialMoments

/-!
# Uniform Gaussian comparison for sublevel events

A uniform Gaussian comparison for sublevel events of finite fields with stable positive
derivative bounds and a smooth bottleneck approximation.  The chain of results moves from a
Lindeberg-type comparison of smooth test-function expectations
(`PositiveJet.Bounds.scalar_expectation_comparison`), through a shifted-cutoff sandwiching
step (`sublevel_measure_comparison_of_cutoff`), to the packaged statement
`exists_gaussian_sublevel_comparison_constant`: a Gaussian comparison for sublevel
probabilities of a `PositiveJet`-approximated field, uniform in the interaction weights once
they are small enough relative to the exponential-moment scale.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

noncomputable section

namespace Sandpile

/-- For a `PositiveJet` bounds datum `A.Bounds β n f` and a smooth bounded test function `ψ`
with bounded first three derivatives, the expectations of `ψ (f (linearField W ·))` under the
i.i.d. product measures `Measure.pi (fun _ => ν)` and `Measure.pi (fun _ => μ)` differ by at
most an explicit multiple of the third-moment overlap bound `Q`, whenever `μ` and `ν` share
their first three moments up to a Lindeberg-type error `T` (`MatchingThirdMoments`) and both
put mass at least `p` on `[-R, R]`.  Proved by specializing `finite_product_lindeberg` to
`ψ ∘ A.smooth`. -/
lemma PositiveJet.Bounds.scalar_expectation_comparison
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    {A : PositiveJet V} {β : ℝ} {n : ℕ} {f : (V → ℝ) → ℝ} (hA : A.Bounds β n f)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M c₁ c₂ c₃ : ℝ}
    (hψbound : ∀ x, |ψ x| ≤ M)
    (h₁ : ∀ x, |deriv ψ x| ≤ c₁) (h₂ : ∀ x, |deriv (deriv ψ) x| ≤ c₂)
    (h₃ : ∀ x, |deriv (deriv (deriv ψ)) x| ≤ c₃)
    (W : V → I → ℝ) {a R p T Q : ℝ}
    (ha : 0 ≤ a) (hR : 0 ≤ R) (hp : 0 < p) (hQ : 0 ≤ Q)
    (hW : ∀ v i, |W v i| ≤ a)
    (hoverlap : ∀ v w z, ∑ i, |W v i * W w i * W z i| ≤ Q)
    (hm : MatchingThirdMoments μ ν ((6 * |β| * n) * a) T)
    (hμsmall : p ≤ μ.real (Icc (-R) R)) (hνsmall : p ≤ ν.real (Icc (-R) R)) :
    |(∫ x, ψ (f (linearField W x)) ∂Measure.pi (fun _ : I => ν)) -
      (∫ x, ψ (f (linearField W x)) ∂Measure.pi (fun _ : I => μ))| ≤
      ((T / 3) * (Real.exp ((6 * |β| * n) * (a * R)) / p)) *
        ((c₁ * (6 * β ^ 2 * (n : ℝ) ^ 2) + 3 * c₂ * (2 * |β| * n) + c₃) * Q) := by
  have hc₁ : 0 ≤ c₁ := (abs_nonneg _).trans (h₁ 0)
  have hc₂ : 0 ≤ c₂ := (abs_nonneg _).trans (h₂ 0)
  have hc₃ : 0 ≤ c₃ := (abs_nonneg _).trans (h₃ 0)
  exact finite_product_lindeberg μ ν (hψ.comp hA.smooth) (fun F => hψbound _)
    W (hA.scalarThird_continuous c₁ c₂ c₃) (by positivity) ha hR hp hQ
    (hA.scalarThird_stable hc₁ hc₂ hc₃) (hA.scalarThird_bound hψ h₁ h₂ h₃)
    (hA.sum_scalarThird_le hc₁ hc₂ hc₃) hW hoverlap hm hμsmall hνsmall

/-- The composite `shiftedCutoff shift width ∘ f` is integrable against any finite measure
`μ`, for measurable `f`, since `shiftedCutoff` is nonnegative and bounded above by `1`
(`shiftedCutoff_nonneg`, `shiftedCutoff_le_one`). -/
lemma integrable_shiftedCutoff_comp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (shift width : ℝ) :
    Integrable (fun x => shiftedCutoff shift width (f x)) μ := by
  apply Integrable.of_bound
    ((contDiff_shiftedCutoff shift width).continuous.measurable.comp hf).aestronglyMeasurable 1
  filter_upwards [] with x
  simpa only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (shiftedCutoff_nonneg _ _ _)] using shiftedCutoff_le_one shift width (f x)

/-- If a smooth approximation `smooth` of `value` (within `error`) has its shifted-cutoff
expectations under `ν` and `μ` within `B` of each other, then the `μ`-probability of the
sublevel set `{value ≤ -shift - error}` is at most the `ν`-probability of the slightly larger
sublevel set `{value ≤ width - shift + error}` plus `B`.  Proved by sandwiching each
indicator between shifted-cutoff bounds (`shiftedCutoff_indicator_bounds`) and integrating. -/
lemma sublevel_measure_comparison_of_cutoff {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {value smooth : Ω → ℝ} (hv : Measurable value) (hs : Measurable smooth)
    {shift width error B : ℝ} (hw : 0 < width) (happrox : ∀ x, |smooth x - value x| ≤ error)
    (hcompare : |(∫ x, shiftedCutoff shift width (smooth x) ∂ν) -
      (∫ x, shiftedCutoff shift width (smooth x) ∂μ)| ≤ B) :
    μ.real {x | value x ≤ -shift - error} ≤
      ν.real {x | value x ≤ width - shift + error} + B := by
  have hlo : MeasurableSet {x | value x ≤ -shift - error} := measurableSet_le hv measurable_const
  have hhi : MeasurableSet {x | value x ≤ width - shift + error} :=
    measurableSet_le hv measurable_const
  have hμphi := integrable_shiftedCutoff_comp (μ := μ) hs shift width
  have hνphi := integrable_shiftedCutoff_comp (μ := ν) hs shift width
  have hlower : μ.real {x | value x ≤ -shift - error} ≤
      ∫ x, shiftedCutoff shift width (smooth x) ∂μ := by
    calc
      _ = ∫ x, {y | value y ≤ -shift - error}.indicator (fun _ => (1 : ℝ)) x ∂μ := by simp [hlo]
      _ ≤ _ := integral_mono ((integrable_const (1 : ℝ)).indicator hlo) hμphi (fun x => by
        simpa only [Set.indicator_apply, mem_setOf_eq]
          using (shiftedCutoff_indicator_bounds hw (happrox x)).1)
  have hupper : (∫ x, shiftedCutoff shift width (smooth x) ∂ν) ≤
      ν.real {x | value x ≤ width - shift + error} := by
    calc
      _ ≤ ∫ x, {y | value y ≤ width - shift + error}.indicator (fun _ => (1 : ℝ)) x ∂ν :=
        integral_mono hνphi ((integrable_const (1 : ℝ)).indicator hhi) (fun x => by
          simpa only [Set.indicator_apply, mem_setOf_eq]
            using (shiftedCutoff_indicator_bounds hw (happrox x)).2)
      _ = _ := by simp [hhi]
  have hd := (neg_le_abs ((∫ x, shiftedCutoff shift width (smooth x) ∂ν) -
    (∫ x, shiftedCutoff shift width (smooth x) ∂μ))).trans hcompare
  linarith

/-- The packaged Gaussian comparison for sublevel probabilities: for every exponential-moment
threshold `θ` there is a constant `C` such that, whenever the one-site law `μ` has second
moment `v` and exponential moment bounded by `K`, the interaction weights `W` are small
enough relative to `θ` and the third-moment overlap `Q`, and `value` is approximated by the
`PositiveJet` output `f` within `error`, the `Measure.pi (fun _ => μ)`-probability of the
sublevel set `{value ∘ linearField W ≤ level}` is bounded by the corresponding Gaussian
probability at level `level + 3 * error` plus an explicit `C * (…) * Q` error term.  Proved by
combining `PositiveJet.Bounds.scalar_expectation_comparison` on a shifted-cutoff test function
with `sublevel_measure_comparison_of_cutoff` and the derivative bounds of `shiftedCutoff`
(`exists_shiftedCutoff_derivative_bounds`). -/
lemma exists_gaussian_sublevel_comparison_constant (θ K : ℝ) (hθ : 0 < θ) :
    ∃ C > 0, ∀ (V I : Type) [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I],
      ∀ (A : PositiveJet V) (β : ℝ) (n : ℕ) (f value : (V → ℝ) → ℝ),
        A.Bounds β n f → Measurable value →
      ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
        Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
        (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ v : ℝ≥0, (∫ x : ℝ, x ^ 2 ∂μ) = v →
      ∀ (W : V → I → ℝ) (a Q : ℝ), 0 ≤ a → 0 ≤ Q →
        (∀ z i, |W z i| ≤ a) → (∀ z w y, ∑ i, |W z i * W w i * W y i| ≤ Q) →
        (6 * |β| * n) * a ≤ θ / 2 →
      ∀ (level error : ℝ), 0 < error → (∀ F, |f F - value F| ≤ error) →
        (Measure.pi (fun _ : I => μ)).real {x | value (linearField W x) ≤ level} ≤
          (Measure.pi (fun _ : I => gaussianReal 0 v)).real
            {x | value (linearField W x) ≤ level + 3 * error} +
          C * (β ^ 2 * (n : ℝ) ^ 2 / error + |β| * n / error ^ 2 + 1 / error ^ 3) * Q := by
  obtain ⟨R, hR, T, hT, hinputs⟩ := exists_uniform_matching_gaussian_inputs θ K hθ
  obtain ⟨D, hD, hcut⟩ := exists_shiftedCutoff_derivative_bounds
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let C := 4 * T * Real.exp ((θ / 2) * R) * D
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro V I _ _ _ _ A β n f value hA hvalue μ hμ hexp hK hmean v hsecond
    W a Q ha hQ hW hoverlap hκ level error herr happrox
  letI : IsProbabilityMeasure μ := hμ
  obtain ⟨hm, hμsmall, hνsmall⟩ := hinputs μ hμ hexp hK hmean v hsecond _ hκ
  obtain ⟨hc1, hc2, hc3⟩ := hcut (-level - error) error herr
  have hcompare := hA.scalar_expectation_comparison μ (gaussianReal 0 v)
    (contDiff_shiftedCutoff (-level - error) error)
    (fun x => by rw [abs_of_nonneg (shiftedCutoff_nonneg _ _ _)]; exact shiftedCutoff_le_one _ _ _)
    hc1 hc2 hc3 W ha hR.le (by norm_num : (0 : ℝ) < 1 / 2) hQ hW hoverlap hm hμsmall hνsmall
  have hprob := sublevel_measure_comparison_of_cutoff
    (Measure.pi (fun _ : I => μ)) (Measure.pi (fun _ : I => gaussianReal 0 v))
    (hvalue.comp (continuous_linearField W).measurable)
    (hA.smooth.continuous.measurable.comp (continuous_linearField W).measurable)
    herr (fun x => happrox (linearField W x)) hcompare
  have helo : -(-level - error) - error = level := by ring
  have hehi : error - (-level - error) + error = level + 3 * error := by ring
  simp only [helo, hehi] at hprob
  apply hprob.trans (add_le_add le_rfl ?_)
  let S := β ^ 2 * (n : ℝ) ^ 2 / error + |β| * n / error ^ 2 + 1 / error ^ 3
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have henv : D / error * (6 * β ^ 2 * (n : ℝ) ^ 2) +
      3 * (D / error ^ 2) * (2 * |β| * n) + D / error ^ 3 ≤ 6 * D * S := by
    dsimp [S]
    have ht : 0 ≤ D / error ^ 3 := by positivity
    nlinarith [show D / error * (6 * β ^ 2 * (n : ℝ) ^ 2) +
      3 * (D / error ^ 2) * (2 * |β| * n) + D / error ^ 3 =
      6 * D * (β ^ 2 * (n : ℝ) ^ 2 / error + |β| * n / error ^ 2 + 1 / error ^ 3) -
        5 * (D / error ^ 3) by ring]
  have hexple : Real.exp ((6 * |β| * n) * (a * R)) ≤ Real.exp ((θ / 2) * R) := by
    apply Real.exp_le_exp.mpr
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hκ hR.le
  calc
    _ ≤ ((T / 3) * (Real.exp ((6 * |β| * n) * (a * R)) / (1 / 2))) * ((6 * D * S) * Q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right henv hQ) (by positivity)
    _ ≤ ((T / 3) * (Real.exp ((θ / 2) * R) / (1 / 2))) * ((6 * D * S) * Q) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hexple (by norm_num)) (by positivity))
        (by positivity)
    _ = _ := by dsimp only [C, S]; ring

end Sandpile
