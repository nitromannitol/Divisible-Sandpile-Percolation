import Mathlib

/-!
# Splitting an expectation across an exit event

Elementary integration lemmas used in the future-height lower bound. `payoff_split` shows that
if a payoff `E` is at least `m` on a measurable, finite-measure event `A`, then the integral of
`E` over `A` is at least `m * (μ A).toReal`, by comparing `E` on `A` to the constant indicator
`m • 𝟙_A`. `infinite_measure_trivial` handles the complementary case `μ A = ∞`, where the bound
is trivial since `(μ A).toReal = 0` and `E` is assumed nonnegative on `A`. `exit_tail_half`
is a purely numerical estimate: once `r` clears the threshold `log 2 + log C ≤ c r²`, the tail
quantity `C * exp (-(c r²))` is at most `1/2`.
-/

open MeasureTheory
open scoped ENNReal

/-- Expectation splitting for the future-height lower bound: a stopped
payoff bounded below by `m` on the exit event contributes at least `m`
times the probability of that event. -/
theorem Sandpile.Support.PayoffSplit.payoff_split
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (E : Ω → ℝ) (m : ℝ)
    (A : Set Ω) (hA : MeasurableSet A)
    (_hm : 0 ≤ m) (hE : ∀ ω ∈ A, m ≤ E ω)
    (hfin : μ A < ∞) (hint : Integrable E μ) :
    m * (μ A).toReal ≤ ∫ ω in A, E ω ∂μ := by
  have h1 : ∫ ω in A, E ω ∂μ = ∫ ω, Set.indicator A E ω ∂μ :=
    (integral_indicator hA).symm
  have h2 : ∫ ω, Set.indicator A (fun _ => m) ω ∂μ = m * (μ A).toReal := by
    have hx := integral_indicator_const (μ := μ) m hA
    simp only [smul_eq_mul] at hx
    rw [hx, mul_comm]
    rfl
  have h3 : ∀ ω, Set.indicator A (fun _ => m) ω ≤ Set.indicator A E ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω]
      exact hE ω hω
    · simp only [Set.indicator_of_notMem hω]
      exact le_rfl
  have h4 : ∫ ω, Set.indicator A (fun _ => m) ω ∂μ ≤ ∫ ω, Set.indicator A E ω ∂μ :=
    integral_mono
      (IntegrableOn.integrable_indicator (integrableOn_const (ne_of_lt hfin)) hA)
      (hint.indicator hA) h3
  rw [← h2, h1]
  exact h4

/-- Infinite-measure case of the expectation split: when the event has
infinite measure the bound is trivial because the real-valued measure
reduction of infinity is zero, and the stopped payoff is nonnegative on
the event. -/
theorem Sandpile.Support.PayoffSplit.infinite_measure_trivial
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω)
    (E : Ω → ℝ) (m : ℝ) (hA : MeasurableSet A) (h : μ A = ∞) (hE : ∀ ω ∈ A, 0 ≤ E ω) :
    m * (μ A).toReal ≤ ∫ ω in A, E ω ∂μ := by
  rw [h]
  simp
  rw [← integral_indicator hA]
  apply integral_nonneg
  intro ω
  by_cases hω : ω ∈ A
  · simp [Set.indicator, hω]
    exact hE ω hω
  · simp [Set.indicator, hω]

/-- Exit-tail arithmetic for the future-height bound: the exit probability
deficit `C exp(-c r²)` is at most `1/2` once `r` is beyond the threshold
`log 2 + log C ≤ c r²`. -/
theorem Sandpile.Support.PayoffSplit.exit_tail_half
    (C c : ℝ) (r : ℕ) (hC : 0 < C) (_hc : 0 < c)
    (hbig : Real.log 2 + Real.log C ≤ c * (r : ℝ) ^ 2) :
    C * Real.exp (-(c * (r : ℝ) ^ 2)) ≤ 1 / 2 := by
  have h1 : C * Real.exp (-(c * (r : ℝ) ^ 2)) = Real.exp (Real.log C - c * (r : ℝ) ^ 2) := by
    rw [Real.exp_sub, Real.exp_log hC, Real.exp_neg, div_eq_inv_mul, mul_comm]
  rw [h1]
  have h2 : Real.log C - c * (r : ℝ) ^ 2 ≤ -Real.log 2 := by linarith
  have h3 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  exact h3 ▸ Real.exp_le_exp.mpr h2
