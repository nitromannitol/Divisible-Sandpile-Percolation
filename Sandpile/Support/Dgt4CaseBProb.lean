/-
The first half of Step 2 of case (b) of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:5383-5385`): "By \eqref{eq:dgt4-origin-fixed-mean} and Markov's
inequality, $\E Pw_n(0)\sim\E u_n(0)/G(0,0)$ and $Pw_n(0)/\E Pw_n(0)\to1$ in
probability."

The second conclusion is the `hprob` hypothesis of the replacement theorem of
`Support/Dgt4CaseBReplace.lean`, and it follows from the two clauses of
`lem:dgt4-origin-frozen` that the paper cites: the uniform `p`-th moment bound on
`Pw_n(0)-\E Pw_n(0)` and the divergence of the mean.  The lemma below is that
deduction, with the centring `m_n` and the level `a_n` kept apart, since the paper
centres at `\E Pw_n(0)` and divides by `\E u_n(0)/G(0,0)`.
-/
import Sandpile.Support.Dgt4CaseBReplace

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Sandpile

/-- Markov's inequality at the `p`-th power, for a uniformly bounded `p`-th moment. -/
theorem measure_ge_le_of_moment {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {Y : Omega → ℝ} {p M t : ℝ} (hp : 0 < p)
    (hint : Integrable (fun ω => |Y ω| ^ p) P) (hmom : (∫ ω, |Y ω| ^ p ∂P) ≤ M)
    (ht : 0 < t) : (P {ω | t ≤ |Y ω|}).toReal ≤ M / t ^ p := by
  have hnn : ∀ ω, 0 ≤ |Y ω| ^ p := fun ω => Real.rpow_nonneg (abs_nonneg _) p
  have h1 := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => |Y ω| ^ p)
    (Filter.Eventually.of_forall hnn) hint (t ^ p)
  have hsub : {ω | t ≤ |Y ω|} ⊆ {ω | t ^ p ≤ |Y ω| ^ p} := fun ω hω =>
    Real.rpow_le_rpow ht.le hω hp.le
  have h2 : (P {ω | t ≤ |Y ω|}).toReal ≤ (P {ω | t ^ p ≤ |Y ω| ^ p}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have h3 : 0 ≤ (P {ω | t ^ p ≤ |Y ω| ^ p}).toReal := ENNReal.toReal_nonneg
  rw [le_div_iff₀ htp]
  simp only [measureReal_def] at h1
  nlinarith [h1, h2, hmom]

/-- `Pw_n(0)/\E u_n(0)\to1` in probability (`sandpile.tex:5379`): a uniform `p`-th moment
bound around a centring asymptotic to the level gives convergence in probability to one. -/
theorem tendsto_prob_ratio_zero_of_moment {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {X : ℕ → Omega → ℝ}
    {m a : ℕ → ℝ} {p M : ℝ} (hp : 0 < p)
    (hint : ∀ n : ℕ, Integrable (fun ω => |X n ω - m n| ^ p) P)
    (hmom : ∀ n : ℕ, (∫ ω, |X n ω - m n| ^ p ∂P) ≤ M)
    (hainf : Tendsto a atTop atTop)
    (hma : Tendsto (fun n : ℕ => m n / a n) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (P {ω | ε < |X n ω / a n - 1|}).toReal) atTop (𝓝 0) := by
  intro ε hε
  have hapos : ∀ᶠ n : ℕ in atTop, 0 < a n := hainf.eventually_gt_atTop 0
  have habs : ∀ n : ℕ, 0 < a n → ∀ y : ℝ, |y / a n - 1| * a n = |y - a n| := by
    intro n ha y
    have h1 : |y / a n - 1| * a n = |(y / a n - 1) * a n| := by
      rw [abs_mul, abs_of_pos ha]
    rw [h1]
    congr 1
    field_simp
  have hincl : ∀ᶠ n : ℕ in atTop,
      {ω | ε < |X n ω / a n - 1|} ⊆ {ω | ε / 2 * a n ≤ |X n ω - m n|} := by
    filter_upwards [hma.eventually (Metric.ball_mem_nhds (1 : ℝ) (half_pos hε)), hapos]
      with n hn ha
    have hn' : |m n / a n - 1| < ε / 2 := by
      rwa [Real.dist_eq] at hn
    intro ω hω
    have t1 : ε * a n < |X n ω - a n| := by
      rw [← habs n ha (X n ω)]
      exact mul_lt_mul_of_pos_right hω ha
    have t2 : |m n - a n| < ε / 2 * a n := by
      rw [← habs n ha (m n)]
      exact mul_lt_mul_of_pos_right hn' ha
    have t3 : |X n ω - a n| ≤ |X n ω - m n| + |m n - a n| := by
      have hsplit : X n ω - a n = (X n ω - m n) + (m n - a n) := by ring
      rw [hsplit]
      exact abs_add_le _ _
    show ε / 2 * a n ≤ |X n ω - m n|
    linarith
  refine squeeze_zero' (g := fun n : ℕ => M / (ε / 2 * a n) ^ p)
    (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_ ?_
  · filter_upwards [hincl, hapos] with n hn ha
    refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hn)) ?_
    exact measure_ge_le_of_moment hp (hint n) (hmom n) (mul_pos (half_pos hε) ha)
  · have h1 : Tendsto (fun n : ℕ => ε / 2 * a n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (half_pos hε) hainf
    have h2 : Tendsto (fun n : ℕ => (ε / 2 * a n) ^ p) atTop atTop :=
      (tendsto_rpow_atTop hp).comp h1
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h2

end Sandpile
