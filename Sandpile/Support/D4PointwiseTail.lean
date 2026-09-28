import Sandpile.Support.D4Scale
import Sandpile.Support.D4SmoothedTail
import Sandpile.Support.D4Reflection

/-!
# Step 4 pointwise linearization tail in dimension four

Step 4 of `prop:d4-pointwise-linearization` (`sandpile.tex:3188-3231`).
The backward decomposition splits the centered difference into a smoothed
term and a centered reflection window.  A short window has a small mean;
above a fixed multiple of `log(t+2)` the exponential reflection bound applies.
`diffField_centered_decomp` records this backward decomposition, and
`exists_pointwise_linearization_four` assembles it with the smoothed-difference tail
`exists_smoothed_difference_tail_four` and the reflection-sum tail
`measure_reflectionSum_tail_four`, splitting on the size of the deviation `lam` relative to
`B * log(t+2)`, to obtain the final tail bound with variance scale `1 + log log t`.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

/-- The backward decomposition of the centered odometer difference: subtracting the mean and the
membrane splits as the centered `n`-step backward-averaged difference field `diffField` plus the
centered `reflectionSum` window, combining the pointwise identity `diffField_decomp` with the
mean identity `integral_reflectionSum`. -/
theorem diffField_centered_decomp {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν)
    (ζ : Site d → ℝ) (n t : ℕ) (hnt : n ≤ t) (x : Site d) :
    odometerOf ζ t x - (∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)) - membrane ζ t x
      = ((avg^[n] (diffField ζ (t - n))) x -
          ∫ η, odometerOf η (t - n) 0 ∂(LatticeProb.iidLaw d ν)) +
        (reflectionSum ζ n t x - ∫ η, reflectionSum η n t x ∂(LatticeProb.iidLaw d ν)) := by
  rw [integral_reflectionSum hd ν hint hmean hpos x n t hnt]
  have h := diffField_decomp ζ n t hnt x
  change odometerOf ζ t x - membrane ζ t x =
    (avg^[n] (diffField ζ (t - n))) x + reflectionSum ζ n t x at h
  linarith

/-- The pointwise difference has variance scale `1 + log log t`. -/
theorem exists_pointwise_linearization_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ t : ℕ, 3 ≤ t → ∀ lam : ℝ, 0 ≤ lam → ∀ x : Site 4,
        LatticeProb.iidLaw 4 ν
            {ζ | lam < |odometerOf ζ t x -
              (∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) - membrane ζ t x|} ≤
          ENNReal.ofReal (C * Real.exp
            (-(c * min (lam ^ 2 / (1 + Real.log (Real.log t))) lam))) := by
  have hint : Integrable id ν := integrable_id_of_exp_moment ν θ hθ hexp
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    Integrable.mono' hint.abs (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  set K := ∫ z, Real.exp (θ * |z|) ∂ν
  obtain ⟨M, hM, hmeanUpper⟩ := exists_crude_log_upper_four hVS ν inferInstance hmean
    θ K hθ hexp le_rfl hint hpos
  obtain ⟨cs, Cs, hcs, hCs, hsmooth⟩ := exists_smoothed_difference_tail_four hVS θ K hθ
  obtain ⟨A, cr, Cr, hA, hcr, hCr, hreflect⟩ := measure_reflectionSum_tail_four hVS θ K hθ
  set B := max 1 (max (8 * A) (4 * M))
  have hB : 1 ≤ B := le_max_left _ _
  have hBA : 8 * A ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBM : 4 * M ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  set c := min (cs / 32) (min (cr / 8) (min 1 (1 / (2 * B))))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcs' : c ≤ cs / 32 := min_le_left _ _
  have hcr' : c ≤ cr / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hc1 : c ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcB : c ≤ 1 / (2 * B) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set C := Real.exp 1 + Cs + 72 * M + Cr
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨c, C, hc, hC, ?_⟩
  intro t ht lam hlam x
  have ht3 : (3 : ℝ) ≤ t := by exact_mod_cast ht
  obtain ⟨-, hell, hL, hLt⟩ := log_time_bounds_four ht3
  set ell := 1 + Real.log (Real.log t)
  set L := Real.log ((t : ℝ) + 2)
  set m := min (lam ^ 2 / ell) lam
  have hm0 : 0 ≤ m := le_min (div_nonneg (sq_nonneg _) (by dsimp [ell]; linarith)) hlam
  have hml : m ≤ lam := min_le_right _ _
  set P := LatticeProb.iidLaw 4 ν
  set E := Real.exp (-(c * m))
  have hE : 0 < E := Real.exp_pos _
  change P _ ≤ ENNReal.ofReal (C * E)
  by_cases hsmall : lam < 1
  · refine prob_le_one.trans (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal (C * E) from ?_)
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hcm : c * m ≤ 1 := by nlinarith
    have h1 : 1 ≤ Real.exp 1 * E := by
      dsimp [E]
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    have h2 : Real.exp 1 ≤ C := by dsimp [C]; linarith
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hE.le)
  have hlam1 : 1 ≤ lam := le_of_not_gt hsmall
  set Y : ℕ → ℝ := fun n => ∫ η, reflectionSum η n t x ∂P
  have hY0 (n : ℕ) : 0 ≤ Y n := integral_nonneg fun η => reflectionSum_nonneg η n t x
  have hYmean (n : ℕ) (hn : n ≤ t) :
      Y n = (∫ η, odometerOf η t 0 ∂P) - ∫ η, odometerOf η (t - n) 0 ∂P :=
    integral_reflectionSum (by norm_num) ν hint hmean hpos x n t hn
  have hYupper (n : ℕ) (hn : n ≤ t) : Y n ≤ M * L := by
    rw [hYmean n hn]
    have h0 : 0 ≤ ∫ η, odometerOf η (t - n) 0 ∂P :=
      integral_nonneg fun η => odometerOf_nonneg η (t - n) 0
    have h := hmeanUpper t
    change (∫ η, odometerOf η t 0 ∂P) ≤ M * L at h
    linarith
  have hfinish (n : ℕ) (hn : 1 ≤ n) (hnt : n < t)
      (hW : 1 + Real.log (((t : ℝ) + 2) / ((n : ℝ) + 2)) ≤ 4 * (ell + lam))
      (hR : P {ζ | lam / 2 < |reflectionSum ζ n t x - Y n|} ≤
        ENNReal.ofReal ((72 * M + Cr) * E)) :
      P {ζ | lam < |odometerOf ζ t x - (∫ η, odometerOf η t 0 ∂P) - membrane ζ t x|}
        ≤ ENNReal.ofReal (C * E) := by
    have hW0 : 0 < 1 + Real.log (((t : ℝ) + 2) / ((n : ℝ) + 2)) := by
      have hr : (1 : ℝ) ≤ ((t : ℝ) + 2) / ((n : ℝ) + 2) := by
        rw [le_div_iff₀ (by positivity)]
        have : (n : ℝ) ≤ t := by exact_mod_cast hnt.le
        linarith
      linarith [Real.log_nonneg hr]
    have hcomp := linearization_exponent_four (by dsimp [ell]; linarith) hlam hW0 hW
      (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    have hcexp : c * m ≤ cs * min ((lam / 2) ^ 2 /
        (1 + Real.log (((t : ℝ) + 2) / ((n : ℝ) + 2)))) (lam / 2 * n) := by
      calc c * m ≤ (cs / 32) * m := mul_le_mul_of_nonneg_right hcs' hm0
        _ = cs * (m / 32) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcomp hcs.le
    have hS : P {ζ | lam / 2 < |(avg^[n] (diffField ζ (t - n))) x -
        ∫ η, odometerOf η (t - n) 0 ∂P|} ≤ ENNReal.ofReal (Cs * E) := by
      refine (hsmooth ν inferInstance hmean hexp le_rfl n t hn hnt x (lam / 2)
        (by positivity)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hcexp)) hCs.le
    have hsub : {ζ | lam < |odometerOf ζ t x - (∫ η, odometerOf η t 0 ∂P) - membrane ζ t x|}
        ⊆ {ζ | lam / 2 < |(avg^[n] (diffField ζ (t - n))) x -
          ∫ η, odometerOf η (t - n) 0 ∂P|} ∪
          {ζ | lam / 2 < |reflectionSum ζ n t x - Y n|} := by
      intro ζ hζ
      simp only [Set.mem_setOf_eq, Set.mem_union] at hζ ⊢
      by_contra h
      push Not at h
      have hdec := diffField_centered_decomp (by norm_num) ν hint hmean hpos ζ n t hnt.le x
      have htriangle := abs_add_le ((avg^[n] (diffField ζ (t - n))) x -
        ∫ η, odometerOf η (t - n) 0 ∂P) (reflectionSum ζ n t x - Y n)
      change odometerOf ζ t x - (∫ η, odometerOf η t 0 ∂P) - membrane ζ t x = _ at hdec
      rw [hdec] at hζ
      change lam < |((avg^[n] (diffField ζ (t - n))) x -
        ∫ η, odometerOf η (t - n) 0 ∂P) + (reflectionSum ζ n t x - Y n)| at hζ
      linarith [h.1, h.2]
    calc P _ ≤ P (_ ∪ _) := measure_mono hsub
      _ ≤ P _ + P _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Cs * E) + ENNReal.ofReal ((72 * M + Cr) * E) := add_le_add hS hR
      _ ≤ ENNReal.ofReal (C * E) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        dsimp [C]
        nlinarith [Real.exp_pos (1 : ℝ)]
  by_cases hmedium : lam ≤ B * L
  · obtain ⟨n, hn, hnt, hn23, hnq, hW⟩ := exists_linearization_scale_four t ht lam hlam1
    apply hfinish n hn hnt hW
    have hw := meanOdometerOf_window_le (d := 4) (by norm_num) ν hint hmean hpos n t hnt.le
    have hw' : ((t : ℝ) - n) * Y n ≤ (n : ℝ) * (M * L) := by
      rw [hYmean n hnt.le]
      rw [Nat.cast_sub hnt.le] at hw
      have hprev : (∫ η, odometerOf η (t - n) 0 ∂P) ≤ M * L := by
        exact (meanOdometerOf_mono ν hpos (Nat.sub_le t n)).trans (hmeanUpper t)
      exact hw.trans (mul_le_mul_of_nonneg_left hprev (Nat.cast_nonneg n))
    have hmarkov := linearization_scale_markov_four ht3 hlam1 hB hmedium hn23 hnq hM.le (hY0 n) hw'
    have hcompare : c * m ≤ lam / (2 * B) := by
      calc c * m ≤ (1 / (2 * B)) * m := mul_le_mul_of_nonneg_right hcB hm0
        _ ≤ (1 / (2 * B)) * lam := mul_le_mul_of_nonneg_left hml (by positivity)
        _ = lam / (2 * B) := by ring
    refine (measure_reflectionSum_markov ν hint hpos n t x (lam / 2) (by linarith)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    calc 2 * Y n / (lam / 2) ≤ 72 * M * Real.exp (-(lam / (2 * B))) := hmarkov
      _ ≤ 72 * M * E := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg hcompare)) (by positivity)
      _ ≤ (72 * M + Cr) * E := by nlinarith
  · have hlarge : B * L ≤ lam := le_of_not_ge hmedium
    have hAL : 8 * A * L ≤ lam :=
      (mul_le_mul_of_nonneg_right hBA (by dsimp [L]; linarith)).trans hlarge
    have hML : 4 * M * L ≤ lam :=
      (mul_le_mul_of_nonneg_right hBM (by dsimp [L]; linarith)).trans hlarge
    have hLl : L ≤ lam := by
      have := mul_le_mul_of_nonneg_right hB (show 0 ≤ L by dsimp [L]; linarith)
      nlinarith
    apply hfinish 1 (by omega) (by omega)
    · norm_num only [Nat.cast_one]
      rw [Real.log_div (by positivity) (by norm_num)]
      have : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      dsimp [L, ell] at *
      linarith
    · have hR := hreflect ν inferInstance hmean hexp le_rfl 1 t (by omega) (by omega) x
        (lam / 2) (by linarith [hYupper 1 (by omega)]) (by dsimp [L] at hAL; linarith)
      have hcompare : c * m ≤ cr * (lam / 2 / 2 - A * L) := by
        have h1 : c * m ≤ (cr / 8) * lam :=
          (mul_le_mul_of_nonneg_right hcr' hm0).trans
            (mul_le_mul_of_nonneg_left hml (by positivity))
        nlinarith
      refine hR.trans (ENNReal.ofReal_le_ofReal ?_)
      calc Cr * Real.exp (-(cr * (lam / 2 / 2 - A * L))) / ((t : ℝ) + 2) ^ 2
          ≤ Cr * Real.exp (-(cr * (lam / 2 / 2 - A * L))) :=
            div_le_self (by positivity) (by nlinarith)
        _ ≤ Cr * E := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (neg_le_neg hcompare)) hCr.le
        _ ≤ (72 * M + Cr) * E := by nlinarith

end Sandpile
