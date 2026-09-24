/-
The two-sided linear log tail `eq:dgt4-band-tail-order` of the constructed
one-site law, the fourth analytic clause of `thm:dgt4-many-limits`
(`sandpile.tex:5905-5911`, `sandpile.tex:5980-5995`).

The paper's argument is exactly the one here.  Markov's inequality applied to the
exponential moment gives `P(ζ(0) ≤ -r) ≤ Ce^{-θr}`, hence the LOWER bound
`cr ≤ -log P(ζ(0) ≤ -r)`.  For the UPPER bound, take the least `j` with
`ℓ_1 a_j ≥ r`: the whole `j`th band then lies below `-r`, so
`P(ζ(0) ≤ -r) ≥ ω_j = c_0e^{-a_j}`, while minimality gives `a_j ≤ Ar/ℓ_1`, so
`-log P(ζ(0) ≤ -r) ≤ Ar/ℓ_1 - log c_0 ≤ Cr`.
-/
import Sandpile.Support.Dgt4ABandLawMoment

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

variable {w0 mu : ℝ} {v : ℝ≥0} {l1 : ℝ} {a w θ : ℕ → ℝ} {m : ℕ → ℕ}

/-- **A band lying entirely below `-r` contributes its whole weight to the lower
tail.** -/
theorem weight_le_bandLaw_Iic (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 < θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hsum : Summable w)
    (j : ℕ) {r : ℝ} (hr : r ≤ l1 * a j) :
    w j ≤ (bandLaw w0 mu v l1 a w θ m (Iic (-r))).toReal := by
  rw [bandLaw_toReal_Iic hw0 hw hθ hl0 hl1 ha hm hatop hsum (-r)]
  have hgnn : 0 ≤ ∫ x in Iic (-r), gaussianPDFReal mu v x :=
    setIntegral_nonneg measurableSet_Iic fun x _ => gaussianPDFReal_nonneg mu v x
  have hcdf : bandComponentCDF l1 (a j) (θ j) (m j) (-r) = 1 :=
    bandComponentCDF_eq_one_of_ge (hθ j) (hm j) hl1 (ha j) (by linarith)
  have hfsum := summable_weight_mul_bandComponentCDF (l1 := l1) (a := a) (θ := θ) (m := m)
    hw hθ hm hsum (-r)
  have hterm : w j * bandComponentCDF l1 (a j) (θ j) (m j) (-r)
      ≤ ∑' k, w k * bandComponentCDF l1 (a k) (θ k) (m k) (-r) :=
    hfsum.le_tsum j fun k _ =>
      mul_nonneg (hw k) (bandComponentCDF_nonneg (hθ k).le _)
  rw [hcdf, mul_one] at hterm
  have hg := mul_nonneg hw0 hgnn
  linarith

/-- Every level is eventually covered by a band. -/
theorem exists_band_below (P : BandParameters) (r : ℝ) :
    ∃ j : ℕ, r ≤ P.l1 * P.level j :=
  ((Filter.Tendsto.const_mul_atTop P.hl1.1 P.level_tendsto).eventually_ge_atTop r).exists

/-- **The two-sided linear log tail of the constructed one-site law**
(`eq:dgt4-band-tail-order`), together with the exponential moment that its lower
half comes from. -/
theorem exists_log_tail_law (P : BandParameters)
    (m : ℕ → ℕ) (hm : ∀ k, 0 < m k) (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (htot : ∑' k, P.weight k ≤ 1) :
    ∃ c C θ0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ0 ∧
      Integrable (fun z : ℝ => Real.exp (θ0 * |z|)) (P.law m mu v) ∧
      ∀ᶠ r : ℝ in atTop,
        c * r ≤ -Real.log ((P.law m mu v) (Iic (-r))).toReal ∧
          -Real.log ((P.law m mu v) (Iic (-r))).toReal ≤ C * r := by
  classical
  set ν : Measure ℝ := P.law m mu v with hν
  have hl0 : 0 < P.l1 := P.hl1.1
  have hl1 : P.l1 < 1 := P.hl1.2
  have hA : 1 < P.A := P.hA
  have hw0 : (0 : ℝ) ≤ 1 - ∑' k, P.weight k := by linarith
  have hwtot : (1 - ∑' k, P.weight k) + ∑' k, P.weight k = 1 := by ring
  have hθpos : ∀ k, 0 < P.theta k := fun k => lt_of_lt_of_le one_pos (P.htheta k).1
  haveI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_bandLaw hw0 (fun k => (P.weight_pos k).le) hθpos hl0 hl1
      P.level_pos hm P.level_tendsto hv P.summable_weight hwtot
  -- the exponential moment at rate one half
  have hexp : Integrable (fun z : ℝ => Real.exp ((1 / 2 : ℝ) * |z|)) ν :=
    integrable_exp_abs_law P m hm mu v hv htot (by norm_num) (by norm_num)
  set M : ℝ := ∫ z, Real.exp ((1 / 2 : ℝ) * |z|) ∂ν with hM
  have hM1 : 1 ≤ M := by
    have hle : ∀ z : ℝ, (1 : ℝ) ≤ Real.exp ((1 / 2 : ℝ) * |z|) := by
      intro z
      refine Real.one_le_exp ?_
      positivity
    have hmono := integral_mono (integrable_const (1 : ℝ)) hexp hle
    rw [hM]
    simpa using hmono
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  -- Markov's inequality on the exponential moment
  have hmarkov : ∀ r : ℝ, 0 ≤ r → (ν (Iic (-r))).toReal * Real.exp ((1 / 2 : ℝ) * r) ≤ M := by
    intro r hr
    have hmono : ∀ x ∈ Iic (-r), Real.exp ((1 / 2 : ℝ) * r) ≤ Real.exp ((1 / 2 : ℝ) * |x|) := by
      intro x hx
      refine Real.exp_le_exp.mpr ?_
      have hx' : x ≤ -r := hx
      have habs : r ≤ |x| := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      linarith
    have h1 : ∫ _x in Iic (-r), Real.exp ((1 / 2 : ℝ) * r) ∂ν
        ≤ ∫ x in Iic (-r), Real.exp ((1 / 2 : ℝ) * |x|) ∂ν :=
      setIntegral_mono_on (integrableOn_const (measure_ne_top ν _)) hexp.integrableOn
        measurableSet_Iic hmono
    have h2 : ∫ x in Iic (-r), Real.exp ((1 / 2 : ℝ) * |x|) ∂ν ≤ M :=
      setIntegral_le_integral hexp
        (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)
    rw [setIntegral_const, smul_eq_mul, measureReal_def] at h1
    linarith
  -- the band that lies below the level
  have hband : ∀ r : ℝ, 0 < r → P.l1 < r →
      ∃ j : ℕ, P.weight j ≤ (ν (Iic (-r))).toReal ∧ P.level j ≤ P.A * r / P.l1 := by
    intro r hr0 hrl
    have hex : ∃ j : ℕ, r ≤ P.l1 * P.level j := exists_band_below P r
    set j : ℕ := Nat.find hex with hj
    have hjspec : r ≤ P.l1 * P.level j := Nat.find_spec hex
    have hjpos : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · exfalso
        rw [h] at hjspec
        simp only [BandParameters.level, pow_zero, mul_one] at hjspec
        linarith
      · exact h
    have hmin : ¬ (r ≤ P.l1 * P.level (j - 1)) := Nat.find_min hex (by omega)
    have hstep : P.level j = P.level (j - 1) * P.A := by
      simp only [BandParameters.level]
      rw [← pow_succ]
      congr 1
      omega
    have hlev : P.level j ≤ P.A * r / P.l1 := by
      have hlt : P.l1 * P.level (j - 1) < r := lt_of_not_ge hmin
      rw [hstep, le_div_iff₀ hl0]
      nlinarith [zero_lt_one.trans hA]
    exact ⟨j, weight_le_bandLaw_Iic hw0 (fun k => (P.weight_pos k).le) hθpos hl0 hl1
      P.level_pos hm P.level_tendsto P.summable_weight j hjspec, hlev⟩
  refine ⟨1 / 4, P.A / P.l1 + |Real.log P.c0| + 1, 1 / 2, by norm_num, by positivity,
    by norm_num, hexp, ?_⟩
  filter_upwards [eventually_gt_atTop (max P.l1 1), eventually_ge_atTop (4 * M)] with r hr hrM
  have hr1 : (1 : ℝ) < r := lt_of_le_of_lt (le_max_right P.l1 1) hr
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr1
  have hrl : P.l1 < r := lt_of_le_of_lt (le_max_left P.l1 1) hr
  obtain ⟨j, hwj, hlev⟩ := hband r hr0 hrl
  have hwjpos : 0 < P.weight j := P.weight_pos j
  have hSpos : 0 < (ν (Iic (-r))).toReal := lt_of_lt_of_le hwjpos hwj
  constructor
  · -- the lower bound, from Markov
    have hmk := hmarkov r hr0.le
    have hle : (ν (Iic (-r))).toReal ≤ M * Real.exp (-((1 / 2 : ℝ) * r)) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
      linarith
    have hlog := Real.log_le_log hSpos hle
    rw [Real.log_mul (ne_of_gt hMpos) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hlog
    have hlogM : Real.log M ≤ M := by
      have := Real.log_le_sub_one_of_pos hMpos
      linarith
    have hMr : Real.log M ≤ r / 4 := by
      have : 4 * M ≤ r := hrM
      linarith
    linarith
  · -- the upper bound, from the band below the level
    have hlog := Real.log_le_log hwjpos hwj
    have hwlog : Real.log (P.weight j) = Real.log P.c0 - P.level j := by
      rw [BandParameters.weight, Real.log_mul (ne_of_gt P.hc0) (ne_of_gt (Real.exp_pos _)),
        Real.log_exp]
      ring
    rw [hwlog] at hlog
    have hc0 : -Real.log P.c0 ≤ |Real.log P.c0| := by
      rw [← abs_neg]
      exact le_abs_self _
    have hlevr : P.level j ≤ P.A / P.l1 * r := by
      rw [div_mul_eq_mul_div]
      exact hlev
    have habs : (0 : ℝ) ≤ |Real.log P.c0| := abs_nonneg _
    nlinarith [hlog, hc0, hlevr, hr1]

end Sandpile.Support
