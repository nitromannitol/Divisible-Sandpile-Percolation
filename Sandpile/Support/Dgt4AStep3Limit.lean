/-
**Step 3 of case (a), the two limits** (`eq:dgt4-gaussian-conditional-contact` and
`eq:dgt4-gaussian-reflected-limit`, `sandpile.tex:5141-5155`), at a fixed level `y`.

Everything needed is in place: the pointwise comparison of `Support/Dgt4AStep3Point.lean`,
the exceptional set of `Support/Dgt4AStep3Level.lean`, the mean and probability comparisons
of `Support/Dgt4AStep3Mean.lean`, the conclusion of Step 2 and the hitting limit
`tendsto_avg_srwHitBy`.  What is assembled here is the passage from the errors to the
limits.

The horizon is below the time: `k_n=\lceil(\log(n+2))^{6/(d-4)}\rceil` is a power of a
logarithm, so `k_n\leq n` for all large `n`, which is what lets the comparison be read at
`m=n-k_n` and `m+k_n=n`.
-/
import Sandpile.Support.Dgt4AStep3Level
import Sandpile.Support.Dgt4AStep3Mean
import Sandpile.Support.Dgt4ACondStep2Limit

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The horizon is eventually below the time. -/
theorem eventually_dgt4Horizon_le (hd : 5 ≤ d) : ∀ᶠ n : ℕ in atTop, dgt4Horizon d n ≤ n := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set q : ℝ := 6 / ((d : ℝ) - 4) with hq
  have hqpos : 0 < q := by
    rw [hq]
    exact div_pos (by norm_num) (by linarith)
  have hlim := tendsto_log_rpow_mul_rpow_neg (p := q) (b := 1) one_pos
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ)) ^ q * (n : ℝ) ^ (-(1 : ℝ)) ≤ (2 : ℝ) ^ (-q) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-q) := Real.rpow_pos_of_pos (by norm_num) _
    exact hlim.eventually_le_const hpos
  filter_upwards [hsmall, eventually_ge_atTop 3] with n hn hn3
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn0 : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hLle : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log (n : ℝ) := by
    have hsq : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    have h1 : Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) hsq
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  have hLnn : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hstep : (Real.log ((n : ℝ) + 2)) ^ q ≤ (2 : ℝ) ^ q * (Real.log (n : ℝ)) ^ q := by
    have h1 : (Real.log ((n : ℝ) + 2)) ^ q ≤ (2 * Real.log (n : ℝ)) ^ q :=
      Real.rpow_le_rpow hLnn hLle hqpos.le
    rwa [Real.mul_rpow (by norm_num) hlogn0] at h1
  have hnrw : (Real.log (n : ℝ)) ^ q * (n : ℝ) ^ (-(1 : ℝ))
      = (Real.log (n : ℝ)) ^ q / (n : ℝ) := by
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  rw [hnrw, div_le_iff₀ hnpos] at hn
  have hprod : (2 : ℝ) ^ q * ((2 : ℝ) ^ (-q) * (n : ℝ)) = (n : ℝ) := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num)]
    simp
  have hfinal : (Real.log ((n : ℝ) + 2)) ^ q ≤ (n : ℝ) := by
    calc (Real.log ((n : ℝ) + 2)) ^ q ≤ (2 : ℝ) ^ q * (Real.log (n : ℝ)) ^ q := hstep
      _ ≤ (2 : ℝ) ^ q * ((2 : ℝ) ^ (-q) * (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (by norm_num) q)
      _ = (n : ℝ) := hprod
  rw [dgt4Horizon]
  exact Nat.ceil_le.2 hfinal

/-- A sequence whose distance to a limit is eventually below every positive number
converges to it. -/
theorem tendsto_of_forall_pos_eventually_le {f : ℕ → ℝ} {L : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, |f n - L| ≤ ε) :
    Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h (ε / 2) (by linarith)] with n hn
  rw [Real.dist_eq]
  linarith

/-- **The conditional mean of the terminal quantity at the level of Step 3 vanishes**
(`eq:dgt4-gaussian-conditional-terminal` at the level `condLevel`). -/
theorem tendsto_meanOdometer_mul_integral_condTerminal_condLevel
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) (y : ℝ) :
    Tendsto (fun n : ℕ => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n *
        ∫ r, condTerminal d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n)
            (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)
            (n - dgt4Horizon d n) (dgt4Horizon d n + 1) r
          ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)))
      atTop (𝓝 0) := by
  have hcc : (0 : ℝ) < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 (coe_pos_of_ne_zero hv)
  have hN : (0 : ℝ) < ‖greenLp d hd (0 : Site d)‖ := norm_greenLp_pos hd
  have hS : (0 : ℝ) ≤ ((fieldVar d v : ℝ≥0) : ℝ) := (fieldVar d v).coe_nonneg
  set sseq : ℕ → ℝ := fun n =>
    if 1 ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n then condLevel d hd v y n
    else 0 with hsseq
  have hbound : ∀ n : ℕ, |sseq n| * (Real.sqrt (v : ℝ) * ‖greenLp d hd (0 : Site d)‖)
      ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
        + ((fieldVar d v : ℝ≥0) : ℝ) * |y| := by
    intro n
    have hann : (0 : ℝ) ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n :=
      meanOdometer_nonneg _ n
    by_cases h1 : 1 ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
    · rw [hsseq]
      simp only [h1, if_true]
      have hkey : |condLevel d hd v y n| * (Real.sqrt (v : ℝ) * ‖greenLp d hd (0 : Site d)‖)
          = |meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
            + ((fieldVar d v : ℝ≥0) : ℝ) * y
              / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n| := by
        have h := condLevel_mul hd hv y n
        have habs := congrArg abs h
        rw [abs_neg] at habs
        rw [← habs, abs_mul, abs_mul, abs_of_pos hcc, abs_of_pos hN]
        ring
      rw [hkey]
      have hdiv : |((fieldVar d v : ℝ≥0) : ℝ) * y
          / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n|
          ≤ ((fieldVar d v : ℝ≥0) : ℝ) * |y| := by
        rw [abs_div, abs_mul, abs_of_nonneg hS, abs_of_nonneg hann]
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg (mul_nonneg hS (abs_nonneg y)) (by linarith :
          (0:ℝ) ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n - 1)]
      have habs2 := abs_add_le (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)
        (((fieldVar d v : ℝ≥0) : ℝ) * y
          / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)
      rw [abs_of_nonneg hann] at habs2
      linarith
    · rw [hsseq]
      simp only [h1, if_false, abs_zero, zero_mul]
      have : (0 : ℝ) ≤ ((fieldVar d v : ℝ≥0) : ℝ) * |y| := mul_nonneg hS (abs_nonneg y)
      linarith
  have hmain := tendsto_meanOdometer_mul_integral_condTerminal hGH hd v hv hsq
    (((fieldVar d v : ℝ≥0) : ℝ) * |y|) (mul_nonneg hS (abs_nonneg y)) sseq hbound
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  refine hmain.congr' ?_
  filter_upwards [hatt.eventually_ge_atTop 1] with n hn
  rw [hsseq]
  simp only [hn, if_true]

/-- The good set of Step 3: off the exceptional set, with a convergent Green field and at the
conditioned level. -/
def condGood (d : ℕ) (hd : 5 ≤ d) (v : ℝ≥0) (y : ℝ) (n : ℕ) : Set (Site d → ℝ) :=
  {r | r ∉ condBad d hd v y n} ∩
    condConv d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n) ∩
    {r | infiniteGreenField (condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n)) 0
      = -(meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
        + ((fieldVar d v : ℝ≥0) : ℝ) * y
          / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)}

/-- Only the exceptional set of `eq:dgt4-gaussian-positive-off-origin` carries mass off the
good set. -/
theorem measure_compl_condGood_le (hd : 5 ≤ d) {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) (n : ℕ) :
    (((LatticeProb.gaussLaw (Site d)).map (residField d hd))
        (condGood d hd v y n)ᶜ).toReal
      ≤ (((LatticeProb.gaussLaw (Site d)).map (residField d hd))
        (condBad d hd v y n)).toReal := by
  set ρ : Measure (Site d → ℝ) :=
    (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  have hconv : ρ (condConv d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n))ᶜ = 0 := by
    have h := ae_mem_condConv hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n)
    rw [Filter.eventually_iff, mem_ae_iff] at h
    simpa using h
  have hlevel : ρ {r : Site d → ℝ |
      infiniteGreenField (condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n)) 0
        = -(meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
          + ((fieldVar d v : ℝ≥0) : ℝ) * y
            / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)}ᶜ = 0 := by
    have h := ae_infiniteGreenField_condLevel hd hv y n
    rw [Filter.eventually_iff, mem_ae_iff] at h
    simpa using h
  have hsub : (condGood d hd v y n)ᶜ ⊆ condBad d hd v y n ∪
      ((condConv d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n))ᶜ ∪
        {r : Site d → ℝ |
          infiniteGreenField (condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n)) 0
            = -(meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
              + ((fieldVar d v : ℝ≥0) : ℝ) * y
                / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)}ᶜ) := by
    intro r hr
    by_cases h1 : r ∈ condBad d hd v y n
    · exact Or.inl h1
    by_cases h2 : r ∈ condConv d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n)
    · refine Or.inr (Or.inr ?_)
      intro h3
      exact hr ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inr (Or.inl h2)
  have hle : ρ (condGood d hd v y n)ᶜ ≤ ρ (condBad d hd v y n) := by
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [measure_union_null hconv hlevel, add_zero]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- The horizon tends to infinity. -/
theorem tendsto_dgt4Horizon_atTop (hd : 5 ≤ d) :
    Tendsto (fun n : ℕ => dgt4Horizon d n) atTop atTop := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set q : ℝ := 6 / ((d : ℝ) - 4) with hq
  have hqpos : 0 < q := by
    rw [hq]
    exact div_pos (by norm_num) (by linarith)
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  refine tendsto_atTop_mono (fun n => Nat.le_ceil _) ?_
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  exact (_root_.tendsto_rpow_atTop hqpos).comp hlog

/-- **`eq:dgt4-gaussian-reflected-limit`** (`sandpile.tex:5143-5150`) at a fixed level `y`:
the scaled conditional mean of the positive part of the reflected increment converges to
`\max(y,0)/G(0,0)`. -/
theorem tendsto_integral_condReflected_posPart
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) (y : ℝ) :
    Tendsto (fun n : ℕ => ∫ r, max (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
          / ((fieldVar d v : ℝ≥0) : ℝ)
          * condReflected d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n) n r) 0
        ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)))
      atTop (𝓝 (max y 0 / green d 0 0)) := by
  set ρ : Measure (Site d → ℝ) :=
    (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  haveI : IsProbabilityMeasure ρ := by
    rw [hρ]
    exact Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  set cc : ℝ := Real.sqrt (v : ℝ) with hcc
  set S : ℝ := ((fieldVar d v : ℝ≥0) : ℝ) with hSdef
  have hSpos : (0 : ℝ) < S := coe_pos_of_ne_zero (fieldVar_ne_zero hd hv)
  have hGpos : (0 : ℝ) < green d 0 0 :=
    lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green (by omega))
  set a : ℕ → ℝ := fun n => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hadef
  set X : ℕ → (Site d → ℝ) → ℝ := fun n r =>
    a n / S * condReflected d hd cc (condLevel d hd v y n) n r with hXdef
  set T : ℕ → (Site d → ℝ) → ℝ := fun n r =>
    a n / S * condTerminal d hd cc (condLevel d hd v y n) (a n)
      (n - dgt4Horizon d n) (dgt4Horizon d n + 1) r with hTdef
  set mu : ℕ → ℝ := fun n => y - avg (LatticeProb.srwHitBy d (dgt4Horizon d n)) 0 * max y 0
    with hmudef
  set Lim : ℝ := y - (1 - 1 / green d 0 0) * max y 0 with hLimdef
  have hmaxL : max Lim 0 = max y 0 / green d 0 0 := by
    rcases le_or_gt y 0 with hy | hy
    · rw [max_eq_right hy, hLimdef, max_eq_right hy]
      simp only [mul_zero, sub_zero]
      rw [max_eq_right hy]
      simp
    · rw [max_eq_left hy.le, hLimdef, max_eq_left hy.le]
      have hval : y - (1 - 1 / green d 0 0) * y = y / green d 0 0 := by
        field_simp
        ring
      rw [hval, max_eq_left (by positivity)]
  -- the three errors
  have hkkatt : Tendsto (fun n : ℕ => dgt4Horizon d n) atTop atTop :=
    tendsto_dgt4Horizon_atTop hd
  have hmu : Tendsto mu atTop (𝓝 Lim) := by
    have h := (tendsto_avg_srwHitBy (d := d) (by omega)).comp hkkatt
    have h2 : Tendsto (fun n : ℕ => y - avg (LatticeProb.srwHitBy d (dgt4Horizon d n)) 0
        * max y 0) atTop (𝓝 (y - (1 - 1 / green d 0 0) * max y 0)) :=
      tendsto_const_nhds.sub (h.mul tendsto_const_nhds)
    exact h2
  have hbad : Tendsto (fun n : ℕ => (ρ (condGood d hd v y n)ᶜ).toReal) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg)
      (Filter.Eventually.of_forall fun n => measure_compl_condGood_le hd hv y n)
      (tendsto_measure_condBad hGH hd v hv (K := |y|) le_rfl)
  have hT : Tendsto (fun n : ℕ => ∫ r, T n r ∂ρ) atTop (𝓝 0) := by
    have hmain := tendsto_meanOdometer_mul_integral_condTerminal_condLevel hGH hd v hv hsq y
    have hdiv := hmain.div_const S
    rw [zero_div] at hdiv
    refine hdiv.congr fun n => ?_
    rw [hTdef]
    rw [integral_const_mul]
    ring
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  rw [← hmaxL]
  refine tendsto_of_forall_pos_eventually_le ?_
  intro ε hε
  set δ : ℝ := ε / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hmax0 : Tendsto (fun n : ℕ => max (mu n) 0) atTop (𝓝 (max Lim 0)) :=
    hmu.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  have hcoef : Tendsto (fun n : ℕ => |y| + max (mu n) 0) atTop (𝓝 (|y| + max Lim 0)) :=
    tendsto_const_nhds.add hmax0
  have herr : Tendsto (fun n : ℕ =>
      (|y| + max (mu n) 0) * ((ρ (condGood d hd v y n)ᶜ).toReal + (∫ r, T n r ∂ρ) / δ)
        + (∫ r, T n r ∂ρ) + |max (mu n) 0 - max Lim 0|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (ρ (condGood d hd v y n)ᶜ).toReal
        + (∫ r, T n r ∂ρ) / δ) atTop (𝓝 0) := by
      have h := hbad.add (hT.div_const δ)
      simpa using h
    have h2 := hcoef.mul h1
    rw [mul_zero] at h2
    have h3 : Tendsto (fun n : ℕ => |max (mu n) 0 - max Lim 0|) atTop (𝓝 0) := by
      have h := (hmax0.sub_const (max Lim 0)).abs
      simpa using h
    have h4 := (h2.add hT).add h3
    simpa using h4
  have hmain : ∀ᶠ n : ℕ in atTop,
      |(∫ r, max (X n r) 0 ∂ρ) - max (mu n) 0|
        ≤ δ + (|y| + max (mu n) 0)
            * ((ρ (condGood d hd v y n)ᶜ).toReal + (∫ r, T n r ∂ρ) / δ)
          + ∫ r, T n r ∂ρ := by
    filter_upwards [hatt.eventually_gt_atTop 0, eventually_dgt4Horizon_le hd] with n ha hk
    have hTnn : ∀ r, 0 ≤ T n r := fun r =>
      mul_nonneg (div_nonneg (le_of_lt ha) hSpos.le)
        (condTerminal_nonneg hd cc (condLevel d hd v y n) (a n) (n - dgt4Horizon d n)
          (dgt4Horizon d n + 1) r)
    have hTint : Integrable (T n) ρ :=
      (integrable_condTerminal hGH hd v hsq (a n) (n - dgt4Horizon d n)
        (dgt4Horizon d n + 1) (by omega) (condLevel d hd v y n)).const_mul _
    have hXm : Measurable (X n) :=
      (measurable_condReflected hd cc (condLevel d hd v y n) n).const_mul _
    have hdom : ∀ᵐ r ∂ρ, max (X n r) 0 ≤ |y| + T n r := by
      filter_upwards [ae_mem_condConv hd cc (condLevel d hd v y n),
        ae_infiniteGreenField_condLevel hd hv y n] with r hr hlev
      have hrw : max (X n r) 0
          = a n / S * max (condReflected d hd cc (condLevel d hd v y n) n r) 0 := by
        simp only [hXdef]
        rw [mul_max_of_nonneg _ _ (div_nonneg ha.le hSpos.le), mul_zero]
      rw [hrw]
      exact condReflected_pos_le hd cc (condLevel d hd v y n) (a n) S y hSpos ha
        (dgt4Horizon d n) n hk r hr hlev
    have hXint : Integrable (fun r => max (X n r) 0) ρ := by
      refine Integrable.mono' ((integrable_const |y|).add hTint)
        ((hXm.max measurable_const).aestronglyMeasurable) ?_
      filter_upwards [hdom] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact hr
    have hcomp : ∀ r ∈ condGood d hd v y n, |X n r - mu n| ≤ T n r := by
      intro r hr
      obtain ⟨⟨hbad', hconv'⟩, hlev'⟩ := hr
      have h := abs_condReflected_sub_le hd cc (condLevel d hd v y n) (a n) S y hSpos ha
        (dgt4Horizon d n) (n - dgt4Horizon d n) r hconv' hlev'
        (good_of_notMem_condBad hd v y n hbad')
      rwa [show n - dgt4Horizon d n + dgt4Horizon d n = n from by omega] at h
    exact abs_integral_posPart_sub_le ρ (X n) (T n) (condGood d hd v y n) (mu n) |y| δ hδ
      (abs_nonneg y) hXm hTnn hTint hXint hcomp hdom
  filter_upwards [hmain, herr.eventually_le_const (by linarith : (0:ℝ) < ε / 2)] with n h1 h2
  have habs := abs_sub_abs_le_abs_sub (∫ r, max (X n r) 0 ∂ρ) (max Lim 0)
  have htri : |(∫ r, max (X n r) 0 ∂ρ) - max Lim 0|
      ≤ |(∫ r, max (X n r) 0 ∂ρ) - max (mu n) 0| + |max (mu n) 0 - max Lim 0| := by
    have := abs_add_le ((∫ r, max (X n r) 0 ∂ρ) - max (mu n) 0) (max (mu n) 0 - max Lim 0)
    simpa using this
  have hδε : δ = ε / 2 := hδdef
  linarith

/-- **`eq:dgt4-gaussian-conditional-contact`** (`sandpile.tex:5136-5142`) at a fixed level
`y\ne0`: the conditional probability of the contact event converges to the indicator of
`\{y>0\}`. -/
theorem tendsto_measure_condReflected_pos
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun n : ℕ => (((LatticeProb.gaussLaw (Site d)).map (residField d hd))
        {r | 0 < condReflected d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n) n r}).toReal)
      atTop (𝓝 (if 0 < y then 1 else 0)) := by
  set ρ : Measure (Site d → ℝ) :=
    (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  haveI : IsProbabilityMeasure ρ := by
    rw [hρ]
    exact Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  set cc : ℝ := Real.sqrt (v : ℝ) with hcc
  set S : ℝ := ((fieldVar d v : ℝ≥0) : ℝ) with hSdef
  have hSpos : (0 : ℝ) < S := coe_pos_of_ne_zero (fieldVar_ne_zero hd hv)
  have hGpos : (0 : ℝ) < green d 0 0 :=
    lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green (by omega))
  set a : ℕ → ℝ := fun n => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hadef
  set X : ℕ → (Site d → ℝ) → ℝ := fun n r =>
    a n / S * condReflected d hd cc (condLevel d hd v y n) n r with hXdef
  set T : ℕ → (Site d → ℝ) → ℝ := fun n r =>
    a n / S * condTerminal d hd cc (condLevel d hd v y n) (a n)
      (n - dgt4Horizon d n) (dgt4Horizon d n + 1) r with hTdef
  set mu : ℕ → ℝ := fun n => y - avg (LatticeProb.srwHitBy d (dgt4Horizon d n)) 0 * max y 0
    with hmudef
  set Lim : ℝ := y - (1 - 1 / green d 0 0) * max y 0 with hLimdef
  have hLimval : (0 < y → Lim = y / green d 0 0) ∧ (y < 0 → Lim = y) := by
    constructor
    · intro hpos
      rw [hLimdef, max_eq_left hpos.le]
      field_simp
      ring
    · intro hneg
      rw [hLimdef, max_eq_right hneg.le]
      ring
  have hLimne : Lim ≠ 0 := by
    rcases hy.lt_or_gt with hneg | hpos
    · rw [hLimval.2 hneg]; exact hy
    · rw [hLimval.1 hpos]
      positivity
  have hsign : (0 < Lim) = (0 < y) := by
    refine propext ?_
    constructor
    · intro h
      rcases hy.lt_or_gt with hneg | hpos
      · rw [hLimval.2 hneg] at h; linarith
      · exact hpos
    · intro h
      rw [hLimval.1 h]
      positivity
  have hkkatt : Tendsto (fun n : ℕ => dgt4Horizon d n) atTop atTop :=
    tendsto_dgt4Horizon_atTop hd
  have hmu : Tendsto mu atTop (𝓝 Lim) :=
    tendsto_const_nhds.sub
      (((tendsto_avg_srwHitBy (d := d) (by omega)).comp hkkatt).mul tendsto_const_nhds)
  have hbad : Tendsto (fun n : ℕ => (ρ (condGood d hd v y n)ᶜ).toReal) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg)
      (Filter.Eventually.of_forall fun n => measure_compl_condGood_le hd hv y n)
      (tendsto_measure_condBad hGH hd v hv (K := |y|) le_rfl)
  have hT : Tendsto (fun n : ℕ => ∫ r, T n r ∂ρ) atTop (𝓝 0) := by
    have hmain := tendsto_meanOdometer_mul_integral_condTerminal_condLevel hGH hd v hv hsq y
    have hdiv := hmain.div_const S
    rw [zero_div] at hdiv
    refine hdiv.congr fun n => ?_
    rw [hTdef, integral_const_mul]
    ring
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  have hLimpos : 0 < |Lim| := abs_pos.mpr hLimne
  have herr : Tendsto (fun n : ℕ =>
      (ρ (condGood d hd v y n)ᶜ).toReal + (∫ r, T n r ∂ρ) / (|Lim| / 2)) atTop (𝓝 0) := by
    have h := hbad.add (hT.div_const (|Lim| / 2))
    simpa using h
  have hmusign : ∀ᶠ n : ℕ in atTop,
      (if 0 < mu n then (1 : ℝ) else 0) = (if 0 < y then (1 : ℝ) else 0) := by
    rcases hy.lt_or_gt with hneg | hpos
    · have hL : Lim < 0 := by
        rw [hLimval.2 hneg]
        exact hneg
      filter_upwards [hmu.eventually_lt_const hL] with n hn
      rw [if_neg (by linarith), if_neg (by linarith)]
    · have hL : (0 : ℝ) < Lim := by
        rw [hLimval.1 hpos]
        positivity
      filter_upwards [hmu.eventually_const_lt hL] with n hn
      rw [if_pos hn, if_pos hpos]
  refine tendsto_of_forall_pos_eventually_le ?_
  intro ε hε
  have hmuabs : Tendsto (fun n : ℕ => |mu n|) atTop (𝓝 |Lim|) := hmu.abs
  filter_upwards [hatt.eventually_gt_atTop 0, eventually_dgt4Horizon_le hd,
    herr.eventually_le_const hε,
    hmuabs.eventually_const_lt (show |Lim| / 2 < |Lim| by linarith),
    hmusign] with n ha hk herrn hmun' hifeq
  have hmun : |Lim| / 2 ≤ |mu n| := le_of_lt hmun'
  have hmupos : 0 < |mu n| := lt_of_lt_of_le (by linarith) hmun
  have hTnn : ∀ r, 0 ≤ T n r := fun r =>
    mul_nonneg (div_nonneg (le_of_lt ha) hSpos.le)
      (condTerminal_nonneg hd cc (condLevel d hd v y n) (a n) (n - dgt4Horizon d n)
        (dgt4Horizon d n + 1) r)
  have hTint : Integrable (T n) ρ :=
    (integrable_condTerminal hGH hd v hsq (a n) (n - dgt4Horizon d n)
      (dgt4Horizon d n + 1) (by omega) (condLevel d hd v y n)).const_mul _
  have hXm : Measurable (X n) :=
    (measurable_condReflected hd cc (condLevel d hd v y n) n).const_mul _
  have hcomp : ∀ r ∈ condGood d hd v y n, |X n r - mu n| ≤ T n r := by
    intro r hr
    obtain ⟨⟨hbad', hconv'⟩, hlev'⟩ := hr
    have h := abs_condReflected_sub_le hd cc (condLevel d hd v y n) (a n) S y hSpos ha
      (dgt4Horizon d n) (n - dgt4Horizon d n) r hconv' hlev'
      (good_of_notMem_condBad hd v y n hbad')
    rwa [show n - dgt4Horizon d n + dgt4Horizon d n = n from by omega] at h
  have hmune' : mu n ≠ 0 := by
    intro h
    exact hmupos.ne' (by rw [h, abs_zero])
  have hbnd := abs_measure_pos_sub_le ρ (X n) (T n) (condGood d hd v y n) (mu n) hmune'
    hXm hTnn hTint hcomp
  have hac : (0 : ℝ) < a n / S := div_pos ha hSpos
  have hset : {r | 0 < X n r}
      = {r | 0 < condReflected d hd cc (condLevel d hd v y n) n r} := by
    ext r
    simp only [Set.mem_setOf_eq, hXdef]
    constructor
    · intro h
      by_contra hcon
      nlinarith [hac, not_lt.mp hcon]
    · intro h
      exact mul_pos hac h
  rw [hset] at hbnd
  rw [hifeq] at hbnd
  have hdivle : (∫ r, T n r ∂ρ) / |mu n| ≤ (∫ r, T n r ∂ρ) / (|Lim| / 2) := by
    refine div_le_div_of_nonneg_left ?_ (by linarith) hmun
    exact integral_nonneg hTnn
  linarith

end Sandpile
