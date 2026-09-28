import Sandpile.Support.Dgt4MeanDiv
import Sandpile.Support.ContLogisticLaw

/-!
# Step 2's lower tail cannot be centered at the scenery value

The record that part (i) of Step 2 of `thm:dgt4-many-limits` must be stated about the
origin-frozen average `W_n = avg (originOdometer (scenery d σ) n) 0`, and not about the scenery
value at the origin. An earlier transcription of `eq:dgt4-band-origin-fixed-lower-tail`, the
predicate `BandStep2Input`, read the lower tail of the FIXED scenery value at the origin minus a
deterministic sequence diverging to `+∞`. That statement is FALSE, and this module proves it:
every real random variable has a finite sublevel set of positive probability, so choosing `r` so
large that `C e^{-λ r}` drops below that probability and then `n` so large that the sublevel set
lies inside `{X - m_n ≤ -r}` contradicts the bound, whatever `C` is. The refutation holds at every
centered integrable nondegenerate scenery law in the paper's dimension range, and in particular at
the standardized logistic law that the repository already uses as its explicit scenery witness.

The predicate itself was deleted, so that nothing can be built on it; this module is kept,
restated against the shape rather than the name, so that the negative result remains a
machine-checked artefact rather than a note.

The paper's correct estimates are the two ORIGIN-FIXED ones,
`eq:dgt4-band-origin-fixed-concentration` and `eq:dgt4-band-origin-fixed-lower-tail`
(`sandpile.tex:6065-6090`), which are about `W_n`, centered at `E u_n(0)/G(0,0)` and at `E W_n`
respectively. Both are PROVED, as `Sandpile.Support.band_origin_concentration` and
`Sandpile.Support.band_origin_lower_tail` (`Sandpile/Support/Dgt4ABandConcentration.lean`).
Step 2 consumes those.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support

/-- A fixed real random variable cannot have uniformly exponentially small lower
tails after subtracting a deterministic sequence diverging to `+∞`. -/
theorem no_uniform_translated_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (a : ℝ) (hp : 0 < P.real {ω | X ω ≤ a})
    (m : ℕ → ℝ) (hm : Tendsto m atTop atTop) (lam : ℝ) (hlam : 0 < lam) :
    ¬ ∃ C : ℝ, ∀ n r : ℕ,
      P.real {ω | X ω - m n ≤ -(r : ℝ)} ≤ C * Real.exp (-(lam * r)) := by
  rintro ⟨C, hC⟩
  have hlin : Tendsto (fun r : ℕ => lam * (r : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hlam tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun r : ℕ => C * Real.exp (-(lam * r))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).const_mul C
  obtain ⟨r, hr⟩ := (hexp.eventually (gt_mem_nhds hp)).exists
  obtain ⟨n, hn⟩ := (hm.eventually_ge_atTop (a + r)).exists
  have hsub : {ω | X ω ≤ a} ⊆ {ω | X ω - m n ≤ -(r : ℝ)} := by
    intro ω hω
    dsimp only [Set.mem_setOf_eq] at hω ⊢
    linarith
  have hle := measureReal_mono (μ := P) hsub (measure_ne_top P _)
  exact (not_lt_of_ge (hle.trans (hC n r))) hr

/-- In a probability space at least one finite sublevel set has positive mass,
with no measurability requirement on the function. -/
theorem exists_positive_sublevel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) :
    ∃ a : ℝ, 0 < P.real {ω | X ω ≤ a} := by
  by_contra h
  push Not at h
  have hzero : ∀ n : ℕ, P {ω | X ω ≤ (n : ℝ)} = 0 := by
    intro n
    have hz : (P {ω | X ω ≤ (n : ℝ)}).toReal = 0 :=
      le_antisymm (h n) ENNReal.toReal_nonneg
    exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top P _)
  have huniv : (⋃ n : ℕ, {ω | X ω ≤ (n : ℝ)}) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge (X ω)
    exact ⟨n, hn⟩
  have hz := measure_iUnion_null hzero
  rw [huniv, measure_univ] at hz
  exact one_ne_zero hz

/-- **The scenery-centered lower tail of Step 2 is false.**  No constant makes
`P(ζ(0) - E u_n(0) ≤ -r) ≤ C e^{-λ r}` hold uniformly in `n` and `r`, at any
centered integrable nondegenerate scenery law with `d ≥ 5`.  The estimate
`eq:dgt4-band-origin-fixed-lower-tail` must therefore be read about the
origin-frozen average and centered at its own mean, as
`Sandpile.Support.band_origin_lower_tail` is. -/
theorem not_scenery_centered_lower_tail (d : ℕ) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (id : ℝ → ℝ) ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z) {lam : ℝ} (hlam : 0 < lam) :
    ¬ ∃ C : ℝ, ∀ n r : ℕ,
      ((Sandpile.centeredMassLaw d ν)
        {σ | Sandpile.scenery d σ 0 -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n ≤ -(r : ℝ)}).toReal
        ≤ C * Real.exp (-(lam * r)) := by
  rintro ⟨C, hC⟩
  obtain ⟨a, ha⟩ := exists_positive_sublevel (Sandpile.centeredMassLaw d ν)
    (fun σ => Sandpile.scenery d σ 0)
  refine no_uniform_translated_tail (Sandpile.centeredMassLaw d ν)
    (fun σ => Sandpile.scenery d σ 0) a ha
    (fun n => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n)
    (Sandpile.tendsto_meanOdometer_atTop hd ν hint hmean hnondeg) lam hlam ⟨C, fun n r => ?_⟩
  simpa only [Measure.real] using hC n r

/-- **The refutation at the repository's own explicit scenery witness**, the
standardized logistic law, which has mean zero, variance one, a strictly positive
smooth density and exponential tails. -/
theorem not_scenery_centered_lower_tail_logistic {lam : ℝ} (hlam : 0 < lam) :
    ¬ ∃ C : ℝ, ∀ n r : ℕ,
      ((Sandpile.centeredMassLaw 5
          (logisticMeasure (Real.sqrt (logisticSecondMoment 1))))
        {σ | Sandpile.scenery 5 σ 0 -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw 5
            (logisticMeasure (Real.sqrt (logisticSecondMoment 1)))) n ≤ -(r : ℝ)}).toReal
        ≤ C * Real.exp (-(lam * r)) := by
  have ha : 0 < Real.sqrt (logisticSecondMoment 1) :=
    Real.sqrt_pos.mpr (logisticSecondMoment_pos one_pos)
  haveI := isProbabilityMeasure_logisticMeasure ha
  refine not_scenery_centered_lower_tail 5 (by norm_num)
    (logisticMeasure (Real.sqrt (logisticSecondMoment 1)))
    ((memLp_id_logisticMeasure ha).integrable (by norm_num))
    (integral_id_logisticMeasure ha) ?_ hlam
  apply Sandpile.ne_dirac_of_atomless
  intro z
  simp [logisticMeasure]

/-- **The summed profile cannot be read along a single sequence.**
`eq:dgt4-band-summed-profile` is about `y_{k,n} = z_{k,n}^{-ϑ_k}`, which depends
on the scale `k` as well as on the time `n`.  If the same one sequence `y` were
required to have increments within `η_kω_k` of `ω_k/(G(0,0)κ_k)` for all large
`k`, in the regime of the band construction, the requirement would be
contradictory: the band weights tend to zero, so the first increment of `y` is
forced to be zero, and then `1/(G(0,0)κ_k) ≤ η_k` for all large `k`, which the
bounded exponents and `η_k → 0` forbid.  Hence the summation must be read along a
FAMILY of sequences indexed by the scale. -/
theorem no_single_sequence_summed_profile
    (y : ℕ → ℝ) (R ω η kap : ℕ → ℝ) (κ0 κ1 G00 : ℝ)
    (hκ0 : 0 < κ0) (hG : 0 < G00)
    (hkap0 : ∀ k, κ0 ≤ kap k) (hkap1 : ∀ k, kap k ≤ κ1)
    (hω : ∀ k, 0 < ω k) (hωz : Tendsto ω atTop (𝓝 0))
    (hR : Tendsto R atTop atTop)
    (hη : Tendsto η atTop (𝓝 0))
    (hinc : ∀ T : ℝ, 0 < T → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
        (n : ℝ) ≤ T * R k ^ 2 → ∀ i : ℕ, i < n →
          |(y (i + 1) - y i) - ω k / (G00 * kap k)| ≤ η k * ω k) :
    False := by
  have hκ1 : 0 < κ1 := lt_of_lt_of_le hκ0 (le_trans (hkap0 0) (hkap1 0))
  have hRsq : Tendsto (fun k : ℕ => R k ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hR
  have hRbig : ∀ᶠ k : ℕ in atTop, (1 : ℝ) ≤ R k ^ 2 := hRsq.eventually_ge_atTop 1
  have hηabs : ∀ᶠ k : ℕ in atTop, |η k| ≤ 1 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hη 1 one_pos
    filter_upwards [eventually_ge_atTop N] with k hk
    have hd := hN k hk
    rw [Real.dist_eq, sub_zero] at hd
    exact hd.le
  have hstep : ∀ᶠ k : ℕ in atTop,
      |(y 1 - y 0) - ω k / (G00 * kap k)| ≤ η k * ω k := by
    filter_upwards [hinc 1 one_pos, hRbig] with k hk hRk
    have h1 : ((1 : ℕ) : ℝ) ≤ 1 * R k ^ 2 := by push_cast; linarith
    simpa using hk 1 h1 0 (by norm_num)
  have hdenom : ∀ k : ℕ, ω k / (G00 * kap k) ≤ ω k / (G00 * κ0) := by
    intro k
    refine div_le_div_of_nonneg_left (hω k).le (by positivity) ?_
    exact mul_le_mul_of_nonneg_left (hkap0 k) hG.le
  have hsmall : ∀ᶠ k : ℕ in atTop,
      |y 1 - y 0| ≤ ω k / (G00 * κ0) + ω k := by
    filter_upwards [hstep, hηabs] with k hk hηk
    have h1 : |y 1 - y 0| ≤ |(y 1 - y 0) - ω k / (G00 * kap k)| + ω k / (G00 * kap k) := by
      have hpos : (0 : ℝ) ≤ ω k / (G00 * kap k) :=
        div_nonneg (hω k).le (mul_pos hG (lt_of_lt_of_le hκ0 (hkap0 k))).le
      have h := abs_sub_le (y 1 - y 0) (ω k / (G00 * kap k)) 0
      rw [sub_zero, sub_zero] at h
      rwa [abs_of_nonneg hpos] at h
    have h3 : η k * ω k ≤ ω k := by
      have := (abs_le.mp hηk).2
      nlinarith [(hω k).le]
    linarith [hdenom k]
  have hzero : Tendsto (fun k : ℕ => ω k / (G00 * κ0) + ω k) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ω k / (G00 * κ0)) atTop (𝓝 0) := by
      simpa using hωz.div_const (G00 * κ0)
    simpa using h1.add hωz
  have hΔ : |y 1 - y 0| ≤ 0 := ge_of_tendsto hzero hsmall
  have hΔ0 : y 1 - y 0 = 0 := by
    have := abs_nonneg (y 1 - y 0)
    have h : |y 1 - y 0| = 0 := le_antisymm hΔ this
    exact abs_eq_zero.mp h
  have hforce : ∀ᶠ k : ℕ in atTop, 1 / (G00 * κ1) ≤ η k := by
    filter_upwards [hstep] with k hk
    rw [hΔ0, zero_sub, abs_neg] at hk
    have hkp : 0 < G00 * kap k := mul_pos hG (lt_of_lt_of_le hκ0 (hkap0 k))
    have habs : ω k / (G00 * kap k) ≤ η k * ω k := by
      have h2 : |ω k / (G00 * kap k)| = ω k / (G00 * kap k) :=
        abs_of_nonneg (div_nonneg (hω k).le hkp.le)
      rw [h2] at hk
      exact hk
    have hdiv : 1 / (G00 * kap k) ≤ η k := by
      rw [div_le_iff₀ hkp] at habs ⊢
      nlinarith [(hω k).le, hω k]
    refine le_trans ?_ hdiv
    refine one_div_le_one_div_of_le hkp ?_
    exact mul_le_mul_of_nonneg_left (hkap1 k) hG.le
  have : 1 / (G00 * κ1) ≤ 0 := ge_of_tendsto hη hforce
  have hpos : 0 < 1 / (G00 * κ1) := div_pos one_pos (mul_pos hG hκ1)
  linarith

end Sandpile.Support
