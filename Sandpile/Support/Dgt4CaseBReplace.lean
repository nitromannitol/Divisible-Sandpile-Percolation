import Sandpile.Support.Dgt4CaseBPassage

/-!
# Regularly varying replacement at a concentrated random level

The analytic core of Step 2 of case (b) of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:5383-5404`): a regularly varying antitone function may be evaluated at a random
argument concentrated at a deterministic level, up to a relative error tending to zero.

The paper states it twice, once for the integrated lower tail (`eq:dgt4-rv-mean-tail-replacement`)
and once for the lower tail itself (`eq:dgt4-rv-contact-tail-replacement`), and proves both the
same way: on the event where the random argument is at least a fixed fraction of the level the
ratio is bounded and converges to one in probability, and the complementary event has probability
`o(F(a_n))` by Step 1. Both instances are `tendsto_integral_abs_ratio` below, whose proof uses
only the DEFINITION of regular variation, at the three fixed ratios `\theta`, `1-\eta` and
`1+\eta`, together with the monotonicity of `F`; Potter's bounds are not needed, because
monotonicity already squeezes `F` at a nearby argument between its values at the two fixed ratios.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Sandpile

/-- Monotonicity squeezes `F` at an argument within `η` of `a` between its values at
`(1-η)a` and `(1+η)a`. -/
theorem abs_ratio_sub_one_le_of_near {F : ℝ → ℝ} (hFanti : Antitone F)
    (hFpos : ∀ r : ℝ, 0 < F r) {η a x : ℝ} (ha : 0 < a) (hx : |x / a - 1| ≤ η) :
    |F x / F a - 1| ≤ |F ((1 - η) * a) / F a - 1| + |F ((1 + η) * a) / F a - 1| := by
  have hFa : 0 < F a := hFpos a
  rw [abs_le] at hx
  have hane : a ≠ 0 := ha.ne'
  have h1 : (1 - η) * a ≤ x := by
    have hxa : 1 - η ≤ x / a := by linarith [hx.1]
    have hmul : (1 - η) * a ≤ (x / a) * a := by nlinarith
    rwa [div_mul_cancel₀ _ hane] at hmul
  have h2 : x ≤ (1 + η) * a := by
    have hxa : x / a ≤ 1 + η := by linarith [hx.2]
    have hmul : (x / a) * a ≤ (1 + η) * a := by nlinarith
    rwa [div_mul_cancel₀ _ hane] at hmul
  have hd1 : F ((1 + η) * a) / F a ≤ F x / F a :=
    div_le_div_of_nonneg_right (hFanti h2) hFa.le
  have hd2 : F x / F a ≤ F ((1 - η) * a) / F a :=
    div_le_div_of_nonneg_right (hFanti h1) hFa.le
  have e1 := le_abs_self (F ((1 - η) * a) / F a - 1)
  have e2 := neg_abs_le (F ((1 + η) * a) / F a - 1)
  have e3 := abs_nonneg (F ((1 - η) * a) / F a - 1)
  have e4 := abs_nonneg (F ((1 + η) * a) / F a - 1)
  rw [abs_le]
  constructor <;> linarith

/-- For every `c > 0` there is a ratio `η ∈ (0,1)` at which the two limit values of the
squeeze are within `c` of one. -/
theorem exists_eta_rpow_close {ρ c : ℝ} (hc : 0 < c) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ |(1 - η) ^ ρ - 1| + |(1 + η) ^ ρ - 1| < c := by
  have h1 : ContinuousAt (fun η : ℝ => (1 - η) ^ ρ) 0 := by
    refine ContinuousAt.rpow_const ?_ (Or.inl ?_)
    · fun_prop
    · norm_num
  have h2 : ContinuousAt (fun η : ℝ => (1 + η) ^ ρ) 0 := by
    refine ContinuousAt.rpow_const ?_ (Or.inl ?_)
    · fun_prop
    · norm_num
  have hcont : ContinuousAt (fun η : ℝ => |(1 - η) ^ ρ - 1| + |(1 + η) ^ ρ - 1|) 0 :=
    ((h1.sub continuousAt_const).abs).add ((h2.sub continuousAt_const).abs)
  have h0 : |(1 - (0 : ℝ)) ^ ρ - 1| + |(1 + (0 : ℝ)) ^ ρ - 1| = 0 := by
    norm_num [Real.one_rpow]
  have htend : Tendsto (fun η : ℝ => |(1 - η) ^ ρ - 1| + |(1 + η) ^ ρ - 1|) (𝓝 0) (𝓝 0) := by
    have hct := hcont.tendsto
    rwa [h0] at hct
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (htend (gt_mem_nhds hc))
  refine ⟨min (δ / 2) (1 / 2), by positivity, ?_, hδ' ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  · rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

/-- `eq:dgt4-rv-mean-tail-replacement` and `eq:dgt4-rv-contact-tail-replacement`
(`sandpile.tex:5380-5390`), in the common abstract form: if the nonnegative random
argument `X_n` converges to the deterministic level `a_n` in probability, and falls below
the fraction `θ` of it with probability `o(F(a_n))`, then `F(X_n)` is `F(a_n)` up to a
relative error tending to zero in mean. -/
theorem tendsto_integral_abs_ratio {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {F : ℝ → ℝ} {ρ : ℝ} (hFrv : LatticeProb.RegularlyVaryingAtTop F ρ)
    (hFanti : Antitone F) (hFpos : ∀ r : ℝ, 0 < F r)
    {X : ℕ → Omega → ℝ} (hXmeas : ∀ n, Measurable (X n)) (hXnn : ∀ n ω, 0 ≤ X n ω)
    {a : ℕ → ℝ} (hapos : ∀ᶠ n in atTop, 0 < a n) (ha : Tendsto a atTop atTop)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hprob : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (P {ω | ε < |X n ω / a n - 1|}).toReal) atTop (𝓝 0))
    (hsmall : Tendsto (fun n : ℕ => (P {ω | X n ω < θ * a n}).toReal / F (a n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ ω, |F (X n ω) / F (a n) - 1| ∂P) atTop (𝓝 0) := by
  have hFmeas : Measurable F := hFanti.measurable
  have hmeasX : ∀ n : ℕ, Measurable fun ω => F (X n ω) := fun n => hFmeas.comp (hXmeas n)
  have hFa : ∀ n : ℕ, 0 < F (a n) := fun n => hFpos _
  have hbFX : ∀ (n : ℕ) (ω : Omega), F (X n ω) ≤ F 0 := fun n ω => hFanti (hXnn n ω)
  have hratio_pos : ∀ (n : ℕ) (ω : Omega), 0 < F (X n ω) / F (a n) :=
    fun n ω => div_pos (hFpos _) (hFa n)
  have hint : ∀ n : ℕ, Integrable (fun ω => |F (X n ω) / F (a n) - 1|) P := by
    intro n
    refine Integrable.mono' (integrable_const (F 0 / F (a n) + 1))
      (((hmeasX n).div_const _).sub_const _).abs.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := hratio_pos n ω
    have h2 : F (X n ω) / F (a n) ≤ F 0 / F (a n) :=
      div_le_div_of_nonneg_right (hbFX n ω) (hFa n).le
    have h3 : 0 < F 0 / F (a n) := div_pos (hFpos 0) (hFa n)
    rw [abs_le]
    constructor <;> linarith
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · exact Filter.Eventually.of_forall fun n =>
      lt_of_lt_of_le hc (integral_nonneg fun ω => abs_nonneg _)
  · obtain ⟨η, hη0, hη1, hηc⟩ := exists_eta_rpow_close (ρ := ρ) (half_pos hc)
    have hSmeas : ∀ n : ℕ, MeasurableSet {ω | η < |X n ω / a n - 1|} := fun n =>
      measurableSet_lt measurable_const (((hXmeas n).div_const _).sub_const _).abs
    have hTmeas : ∀ n : ℕ, MeasurableSet {ω | X n ω < θ * a n} := fun n =>
      measurableSet_lt (hXmeas n) measurable_const
    set E : ℕ → ℝ := fun n =>
      |F ((1 - η) * a n) / F (a n) - 1| + |F ((1 + η) * a n) / F (a n) - 1| with hEdef
    set C : ℕ → ℝ := fun n => F (θ * a n) / F (a n) + 1 with hCdef
    set D : ℕ → ℝ := fun n => F 0 / F (a n) + 1 with hDdef
    set pS : ℕ → ℝ := fun n => (P {ω | η < |X n ω / a n - 1|}).toReal with hpSdef
    set pT : ℕ → ℝ := fun n => (P {ω | X n ω < θ * a n}).toReal with hpTdef
    have hEnn : ∀ n : ℕ, 0 ≤ E n := fun n => by
      rw [hEdef]; positivity
    have hC1 : ∀ n : ℕ, 1 < C n := fun n => by
      rw [hCdef]
      have := div_pos (hFpos (θ * a n)) (hFa n)
      simpa using this
    have hD1 : ∀ n : ℕ, 1 < D n := fun n => by
      rw [hDdef]
      have := div_pos (hFpos 0) (hFa n)
      simpa using this
    have hi1 : ∀ n : ℕ, Integrable
        (Set.indicator {ω | η < |X n ω / a n - 1|} (fun _ => C n)) P := fun n =>
      (integrable_const (C n)).indicator (hSmeas n)
    have hi2 : ∀ n : ℕ, Integrable
        (Set.indicator {ω | X n ω < θ * a n} (fun _ => D n)) P := fun n =>
      (integrable_const (D n)).indicator (hTmeas n)
    have hptwise : ∀ (n : ℕ), 0 < a n → ∀ ω : Omega, |F (X n ω) / F (a n) - 1| ≤
        E n + (Set.indicator {ω | η < |X n ω / a n - 1|} (fun _ => C n) ω +
          Set.indicator {ω | X n ω < θ * a n} (fun _ => D n) ω) := by
      intro n han ω
      have hn1 : 0 ≤ Set.indicator {ω | η < |X n ω / a n - 1|} (fun _ => C n) ω :=
        Set.indicator_nonneg (fun _ _ => le_of_lt (lt_trans zero_lt_one (hC1 n))) ω
      have hn2 : 0 ≤ Set.indicator {ω | X n ω < θ * a n} (fun _ => D n) ω :=
        Set.indicator_nonneg (fun _ _ => le_of_lt (lt_trans zero_lt_one (hD1 n))) ω
      by_cases hA : |X n ω / a n - 1| ≤ η
      · have hkey := abs_ratio_sub_one_le_of_near hFanti hFpos han hA
        rw [hEdef]
        linarith
      · have hA' : η < |X n ω / a n - 1| := not_le.mp hA
        have hmemA : ω ∈ {ω | η < |X n ω / a n - 1|} := hA'
        have hind1 : Set.indicator {ω | η < |X n ω / a n - 1|} (fun _ => C n) ω = C n :=
          Set.indicator_of_mem hmemA (fun _ => C n)
        by_cases hB : X n ω < θ * a n
        · have hmemB : ω ∈ {ω | X n ω < θ * a n} := hB
          have hind2 : Set.indicator {ω | X n ω < θ * a n} (fun _ => D n) ω = D n :=
            Set.indicator_of_mem hmemB (fun _ => D n)
          have h1 := hratio_pos n ω
          have h2 : F (X n ω) / F (a n) ≤ F 0 / F (a n) :=
            div_le_div_of_nonneg_right (hbFX n ω) (hFa n).le
          have h3 := hEnn n
          have h4 : |F (X n ω) / F (a n) - 1| ≤ D n := by
            rw [hDdef, abs_le]
            constructor <;> linarith
          rw [hind1, hind2]
          have h5 := lt_trans zero_lt_one (hC1 n)
          linarith
        · have hB' : θ * a n ≤ X n ω := not_lt.mp hB
          have h1 := hratio_pos n ω
          have h2 : F (X n ω) / F (a n) ≤ F (θ * a n) / F (a n) :=
            div_le_div_of_nonneg_right (hFanti hB') (hFa n).le
          have h3 := hEnn n
          have h4 : |F (X n ω) / F (a n) - 1| ≤ C n := by
            rw [hCdef, abs_le]
            constructor <;> linarith
          rw [hind1]
          linarith
    have hIR : ∀ n : ℕ, (∫ ω, (E n +
        (Set.indicator {ω | η < |X n ω / a n - 1|} (fun _ => C n) ω +
          Set.indicator {ω | X n ω < θ * a n} (fun _ => D n) ω)) ∂P)
        = E n + (C n * pS n + D n * pT n) := by
      intro n
      have hA : (∫ ω, (E n +
          (Set.indicator {ω | η < |X n ω / a n - 1|} (fun _ => C n) ω +
            Set.indicator {ω | X n ω < θ * a n} (fun _ => D n) ω)) ∂P)
          = (∫ _ω : Omega, E n ∂P) +
            ∫ ω, (Set.indicator {ω | η < |X n ω / a n - 1|} (fun _ => C n) ω +
              Set.indicator {ω | X n ω < θ * a n} (fun _ => D n) ω) ∂P :=
        integral_add (integrable_const (E n)) ((hi1 n).add (hi2 n))
      have hB : (∫ ω, (Set.indicator {ω | η < |X n ω / a n - 1|} (fun _ => C n) ω +
            Set.indicator {ω | X n ω < θ * a n} (fun _ => D n) ω) ∂P)
          = (∫ ω, Set.indicator {ω | η < |X n ω / a n - 1|} (fun _ => C n) ω ∂P) +
            ∫ ω, Set.indicator {ω | X n ω < θ * a n} (fun _ => D n) ω ∂P :=
        integral_add (hi1 n) (hi2 n)
      rw [hA, hB, integral_const, integral_indicator_const _ (hSmeas n),
        integral_indicator_const _ (hTmeas n)]
      simp [hpSdef, hpTdef, measureReal_def, mul_comm]
    have hle : ∀ n : ℕ, 0 < a n →
        (∫ ω, |F (X n ω) / F (a n) - 1| ∂P) ≤ E n + (C n * pS n + D n * pT n) := by
      intro n han
      rw [← hIR n]
      exact integral_mono (hint n) ((integrable_const (E n)).add ((hi1 n).add (hi2 n)))
        (fun ω => hptwise n han ω)
    have hEtend : Tendsto E atTop (𝓝 (|(1 - η) ^ ρ - 1| + |(1 + η) ^ ρ - 1|)) := by
      have h1 : Tendsto (fun n : ℕ => F ((1 - η) * a n) / F (a n)) atTop (𝓝 ((1 - η) ^ ρ)) := by
        simpa [Function.comp_def] using (hFrv (1 - η) (by linarith)).comp ha
      have h2 : Tendsto (fun n : ℕ => F ((1 + η) * a n) / F (a n)) atTop (𝓝 ((1 + η) ^ ρ)) := by
        simpa [Function.comp_def] using (hFrv (1 + η) (by linarith)).comp ha
      exact ((h1.sub_const 1).abs).add ((h2.sub_const 1).abs)
    have hCtend : Tendsto C atTop (𝓝 (θ ^ ρ + 1)) := by
      have h1 : Tendsto (fun n : ℕ => F (θ * a n) / F (a n)) atTop (𝓝 (θ ^ ρ)) := by
        simpa [Function.comp_def] using (hFrv θ hθ).comp ha
      exact h1.add_const 1
    have hpStend : Tendsto pS atTop (𝓝 0) := hprob η hη0
    have hpTtend : Tendsto pT atTop (𝓝 0) := by
      have hsub : ∀ᶠ n : ℕ in atTop,
          {ω | X n ω < θ * a n} ⊆ {ω | (1 - θ) / 2 < |X n ω / a n - 1|} := by
        filter_upwards [hapos] with n han
        intro ω hω
        have hx : X n ω / a n < θ := by
          rw [div_lt_iff₀ han]
          exact hω
        have h1 : X n ω / a n - 1 < θ - 1 := by linarith
        have h2 : 1 - θ ≤ |X n ω / a n - 1| := by
          rw [le_abs]
          right
          linarith
        have h3 : (1 - θ) / 2 < 1 - θ := by linarith
        exact lt_of_lt_of_le h3 h2
      refine squeeze_zero' (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_
        (hprob ((1 - θ) / 2) (by linarith))
      filter_upwards [hsub] with n hn
      exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hn)
    have hDT : Tendsto (fun n : ℕ => D n * pT n) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => F 0 * ((P {ω | X n ω < θ * a n}).toReal / F (a n)) + pT n)
          atTop (𝓝 (F 0 * 0 + 0)) := (tendsto_const_nhds.mul hsmall).add hpTtend
      rw [mul_zero, add_zero] at h1
      refine h1.congr fun n => ?_
      rw [hDdef, hpTdef]
      field_simp
    have hfinal : Tendsto (fun n : ℕ => E n + (C n * pS n + D n * pT n)) atTop
        (𝓝 (|(1 - η) ^ ρ - 1| + |(1 + η) ^ ρ - 1| + ((θ ^ ρ + 1) * 0 + 0))) :=
      hEtend.add ((hCtend.mul hpStend).add hDT)
    rw [mul_zero, add_zero, add_zero] at hfinal
    have hlt : |(1 - η) ^ ρ - 1| + |(1 + η) ^ ρ - 1| < c := lt_trans hηc (half_lt_self hc)
    filter_upwards [hfinal.eventually (gt_mem_nhds hlt), hapos] with n hn han
    exact lt_of_le_of_lt (hle n han) hn

/-- A positive antitone function of a nonnegative random variable is bounded by its value
at the origin, hence integrable on a probability space. -/
theorem integrable_antitone_comp {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {F : ℝ → ℝ} (hFanti : Antitone F)
    (hFpos : ∀ r : ℝ, 0 < F r) {Y : Omega → ℝ} (hY : Measurable Y) (hYnn : ∀ ω, 0 ≤ Y ω) :
    Integrable (fun ω => F (Y ω)) P := by
  refine Integrable.mono' (integrable_const (F 0))
    ((hFanti.measurable.comp hY).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (hFpos _)]
  exact hFanti (hYnn ω)

/-- `eq:dgt4-rv-mean-tail-replacement` (`sandpile.tex:5381-5383`) in the form the mean
increment consumes: the expectation of `F` at the random argument is asymptotic to its
value at the deterministic level. -/
theorem tendsto_integral_div_of_abs_ratio {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {F : ℝ → ℝ} (hFanti : Antitone F) (hFpos : ∀ r : ℝ, 0 < F r)
    {X : ℕ → Omega → ℝ} (hXmeas : ∀ n, Measurable (X n)) (hXnn : ∀ n ω, 0 ≤ X n ω)
    {a : ℕ → ℝ}
    (h : Tendsto (fun n : ℕ => ∫ ω, |F (X n ω) / F (a n) - 1| ∂P) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∫ ω, F (X n ω) ∂P) / F (a n)) atTop (𝓝 1) := by
  refine tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h)
  have hYint : Integrable (fun ω => F (X n ω)) P :=
    integrable_antitone_comp hFanti hFpos (hXmeas n) (hXnn n)
  have hdint : Integrable (fun ω => F (X n ω) / F (a n) - 1) P :=
    (hYint.div_const _).sub (integrable_const 1)
  have hsplit : (∫ ω, (F (X n ω) / F (a n) - 1) ∂P)
      = (∫ ω, F (X n ω) / F (a n) ∂P) - 1 := by
    rw [integral_sub (hYint.div_const _) (integrable_const 1), integral_const]
    simp
  rw [Real.norm_eq_abs, ← integral_div, ← hsplit]
  exact abs_integral_le_integral_abs

/-- `eq:dgt4-rv-contact-tail-replacement` (`sandpile.tex:5385-5388`) in the form the
threshold comparison consumes: the mean absolute difference between the value of `F` at
the random argument and at the deterministic level is `o(F(a_n))`. -/
theorem tendsto_integral_abs_sub_div_of_abs_ratio {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {F : ℝ → ℝ} (hFpos : ∀ r : ℝ, 0 < F r) {X : ℕ → Omega → ℝ} {a : ℕ → ℝ}
    (h : Tendsto (fun n : ℕ => ∫ ω, |F (X n ω) / F (a n) - 1| ∂P) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∫ ω, |F (X n ω) - F (a n)| ∂P) / F (a n)) atTop (𝓝 0) := by
  refine h.congr fun n => ?_
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hpos : 0 < F (a n) := hFpos (a n)
  rw [eq_div_iff hpos.ne']
  have hmul : |F (X n ω) / F (a n) - 1| * F (a n)
      = |(F (X n ω) / F (a n) - 1) * F (a n)| := by
    rw [abs_mul, abs_of_pos hpos]
  rw [hmul]
  congr 1
  field_simp

end Sandpile
