/-
The origin-frozen concentration estimate in Step 2 of the many-limits theorem
(`sandpile.tex:6060-6079`). The estimate is uniform over every time whose mean
height lies below the band level. All expectations below are integrable.
-/
import Sandpile.Support.Dgt4OriginProb
import Sandpile.Support.LinJacobianFirstConjunct
import Sandpile.External.GreenBoundsHighProved

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

open Sandpile

/-- The average of the origin-frozen odometer, in mass coordinates, is integrable. -/
theorem integrable_band_origin_average {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable id ν) (n : ℕ) :
    Integrable (fun σ => avg (originOdometer (scenery d σ) n) 0)
      (centeredMassLaw d ν) := by
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    hint.abs.mono' (by fun_prop) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
      exact max_le (le_abs_self z) (abs_nonneg z))
  have hi := integrable_avg_field (fun x => integrable_localizedOdometer hd ν
    hpos {x : Site d | x ≠ 0} n x) 0
  exact integrable_comp_scenery ν hd _ hi.aestronglyMeasurable hi

/-- The mean absolute error of the origin-frozen average is bounded by any
positive multiple of the mean height, plus a constant independent of time. -/
theorem band_origin_error_le {d : ℕ} (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν) (γ : ℝ) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫ σ, |avg (originOdometer (scenery d σ) n) 0 -
        meanOdometer (centeredMassLaw d ν) n / green d 0 0|
          ∂centeredMassLaw d ν) ≤
        γ * (meanOdometer (centeredMassLaw d ν) n / green d 0 0) + C := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hint : Integrable id ν :=
    ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hsq).integrable
      (by norm_num)
  let μ := centeredMassLaw d ν
  let W : ℕ → (Site d → ℝ) → ℝ := fun n σ => avg (originOdometer (scenery d σ) n) 0
  let b : ℕ → ℝ := fun n => meanOdometer μ n / green d 0 0
  let m : ℕ → ℝ := fun n => ∫ σ, W n σ ∂μ
  have hb : ∀ n, 0 ≤ b n := fun n => div_nonneg (meanOdometer_nonneg ν n) hG.le
  have hWi : ∀ n, Integrable (W n) μ := integrable_band_origin_average hd1 ν hint
  have hmom : Integrable (fun z : ℝ => |z| ^ (2 : ℝ)) ν :=
    integrable_abs_rpow_two ν hsq
  obtain ⟨M, hM⟩ := origin_frozen_moment_bound External.greenBoundsHigh hd ν
    (by norm_num : (2 : ℝ) ≤ 2) hmom
  have hsqW : ∀ n, Integrable (fun σ => (W n σ - m n) ^ 2) μ := by
    intro n
    have hi := integrable_avg_originOdometer_centred_rpow hd ν
      (by norm_num : (1 : ℝ) ≤ 2) hmom n (m n)
    have hi' := integrable_comp_scenery ν hd1 _ hi.aestronglyMeasurable hi
    simpa only [Real.rpow_two, sq_abs] using hi'
  have hfluct : ∀ n, (∫ σ, |W n σ - m n| ∂μ) ≤ 1 + M := by
    intro n
    have hm : (∫ σ, (W n σ - m n) ^ 2 ∂μ) ≤ M := by
      simpa only [Real.rpow_two, sq_abs] using hM n
    have hi := integral_mono ((hWi n).sub (integrable_const _)).abs
      ((integrable_const (1 : ℝ)).add (hsqW n))
      (fun σ => show |W n σ - m n| ≤ 1 + (W n σ - m n) ^ 2 by
        nlinarith [sq_nonneg (|W n σ - m n| - 1), sq_abs (W n σ - m n)])
    change (∫ σ, |W n σ - m n| ∂μ) ≤ ∫ σ, 1 + (W n σ - m n) ^ 2 ∂μ at hi
    rw [integral_add (integrable_const _) (hsqW n)] at hi
    simp only [integral_const, probReal_univ, one_smul] at hi
    linarith
  have hratio : Tendsto (fun n => m n / b n) atTop (𝓝 1) := by
    have hr := origin_frozen_mean_ratio hd ν hint hmean (ne_dirac_of_atomless ν hatom)
    convert hr using 1
    funext n
    dsimp [m, b, W, μ]
    rw [div_div_eq_mul_div, mul_comm]
  have hbtop : Tendsto b atTop atTop :=
    (tendsto_meanOdometer_atTop hd ν hint hmean (ne_dirac_of_atomless ν hatom)).atTop_div_const hG
  have he : ∀ᶠ n : ℕ in atTop, |m n - b n| ≤ γ * b n := by
    filter_upwards [hbtop.eventually_gt_atTop 0,
      (Metric.tendsto_nhds.mp hratio γ hγ)] with n hn hclose
    have heq : m n / b n - 1 = (m n - b n) / b n := by
      rw [sub_div, div_self hn.ne']
    rw [Real.dist_eq, heq, abs_div, abs_of_pos hn] at hclose
    exact ((div_lt_iff₀ hn).mp hclose).le
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  let C₀ : ℝ := ∑ n ∈ Finset.range N, |m n - b n|
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hbias : ∀ n, |m n - b n| ≤ γ * b n + C₀ := by
    intro n
    by_cases hn : N ≤ n
    · exact (hN n hn).trans (le_add_of_nonneg_right hC₀)
    · have hs : |m n - b n| ≤ C₀ :=
        Finset.single_le_sum (fun i _ => abs_nonneg (m i - b i))
          (Finset.mem_range.mpr (by omega))
      exact hs.trans (le_add_of_nonneg_left (mul_nonneg hγ.le (hb n)))
  refine ⟨1 + |M| + C₀, by positivity, fun n => ?_⟩
  have hi := integral_mono ((hWi n).sub (integrable_const (b n))).abs
    (((hWi n).sub (integrable_const (m n))).abs.add (integrable_const |m n - b n|))
    (fun σ => abs_sub_le (W n σ) (m n) (b n))
  change (∫ σ, |W n σ - b n| ∂μ) ≤ ∫ σ, |W n σ - m n| + |m n - b n| ∂μ at hi
  rw [integral_add (f := fun σ => |W n σ - m n|)
    ((hWi n).sub (integrable_const (m n))).abs (integrable_const _)] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  change (∫ σ, |W n σ - b n| ∂μ) ≤ γ * b n + (1 + |M| + C₀)
  linarith [hfluct n, hbias n, le_abs_self M]

/-- Uniform concentration below any diverging band levels. This is the
epsilon formulation of `eq:dgt4-band-origin-fixed-concentration`. -/
theorem band_origin_concentration {d : ℕ} (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) :
    (∀ n : ℕ, Integrable (fun σ => |avg (originOdometer (scenery d σ) n) 0 -
        meanOdometer (centeredMassLaw d ν) n / green d 0 0|) (centeredMassLaw d ν)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, 0 < a k ∧ ∀ n : ℕ,
      meanOdometer (centeredMassLaw d ν) n / green d 0 0 ≤ a k →
        ((∫ σ, |avg (originOdometer (scenery d σ) n) 0 -
          meanOdometer (centeredMassLaw d ν) n / green d 0 0|
            ∂centeredMassLaw d ν) + 1) / a k ≤ ε := by
  have hint : Integrable id ν :=
    ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hsq).integrable
      (by norm_num)
  refine ⟨fun n => ((integrable_band_origin_average (by omega) ν hint n).sub
    (integrable_const _)).abs, fun ε hε => ?_⟩
  obtain ⟨C, hC, hbound⟩ := band_origin_error_le hd ν hatom hmean hsq (ε / 2) (by positivity)
  have hsmall : Tendsto (fun k => (C + 1) / a k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ha
  filter_upwards [ha.eventually_gt_atTop 0,
    hsmall.eventually_lt_const (show (0 : ℝ) < ε / 2 by positivity)] with k hk hsmallk
  refine ⟨hk, fun n hn => (div_le_iff₀ hk).mpr ?_⟩
  have hc := (div_lt_iff₀ hk).mp hsmallk
  have hb := hbound n
  have hn' := mul_le_mul_of_nonneg_left hn (show 0 ≤ ε / 2 by positivity)
  linarith

/-- The lower-tail estimate of Step 2, centered at the expectation of the
origin-frozen average and valid for every nonnegative real deviation. -/
theorem band_origin_lower_tail {d : ℕ} (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (θ lam : ℝ)
    (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hlam : 0 < lam) (hgap : lam < θ / LatticeProb.greenRatioSup d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
      ((centeredMassLaw d ν)
        {σ | avg (originOdometer (scenery d σ) n) 0 -
          (∫ σ', avg (originOdometer (scenery d σ') n) 0 ∂centeredMassLaw d ν) ≤ -r}).toReal ≤
        C * Real.exp (-(lam * r)) := by
  have hB : 0 < LatticeProb.greenRatioSup d := by
    by_contra hn
    have hb := div_nonpos_of_nonneg_of_nonpos hθ.le (le_of_not_gt hn)
    linarith
  obtain ⟨C, hC⟩ := origin_frozen_lower_tail External.greenBoundsHigh hd ν hθ hexp hB.le
    (fun z hz => LatticeProb.le_greenRatioSup (by omega) hz) hlam
    ((lt_div_iff₀ hB).mp hgap)
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun n r _ => ?_⟩
  have hb := (hC n r).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.exp_nonneg _)))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg
      (zero_le_one.trans (le_max_right C 1)) (Real.exp_nonneg _)))

end Sandpile.Support
