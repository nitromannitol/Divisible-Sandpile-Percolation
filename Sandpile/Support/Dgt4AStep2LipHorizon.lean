/-
The clause that closes Step 2 of case (a) (`sandpile.tex:5124-5126`):

  "because `\E|b+V_\infty(0)|=O(\E u_n(0))` and `(\E u_n(0))^2k_n^{-(d-4)/2}\to0`."

The Lipschitz constant of the conditioning (`Support/Dgt4AStep2Lip.lean`) is at most
`Ck_n^{-(d-4)/4}`, and the mean odometer is at most `K\sqrt{\log n}`
(`Support/Dgt4AStep1Gaussian.lean`), so the product of the square of the height with the
Lipschitz constant is at most `CK^2\log n\,k_n^{-(d-4)/4}`, which vanishes at the horizon
`k_n=\lceil(\log(n+2))^{6/(d-4)}\rceil` of `Support/Dgt4AStep2Horizon.lean`: there
`k_n^{(d-4)/4}\geq(\log(n+2))^{3/2}`.
-/
import Sandpile.Support.Dgt4AStep2Lip
import Sandpile.Support.Dgt4AStep2Horizon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The horizon is at least one, since `\log(n+2)>0`. -/
theorem one_le_dgt4Horizon (hd : 5 ≤ d) (n : ℕ) : 1 ≤ dgt4Horizon d n := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h4 : (0 : ℝ) < (d : ℝ) - 4 := by linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hL : (0 : ℝ) < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hpos : (0 : ℝ) < (Real.log ((n : ℝ) + 2)) ^ (6 / ((d : ℝ) - 4)) :=
    Real.rpow_pos_of_pos hL _
  refine Nat.one_le_iff_ne_zero.2 fun hzero => ?_
  rw [dgt4Horizon] at hzero
  have h2 := Nat.ceil_eq_zero.1 hzero
  linarith

theorem tendsto_meanOdometer_sq_mul_horizon_lip
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) :
    Tendsto (fun n : ℕ =>
        (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2 *
          (|(avg^[dgt4Horizon d n + 1]
              (fun x => ∑' z : Site d, green d x z * green d 0 z)) 0| / greenSqSum d))
      atTop (𝓝 0) := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hθ : (0 : ℝ) < ((d : ℝ) - 4) / 4 := by
    have h4 : (0 : ℝ) < (d : ℝ) - 4 := by linarith
    positivity
  have hgs1 : (1 : ℝ) ≤ greenSqSum d := one_le_greenSqSum hd
  have hgs : (0 : ℝ) < greenSqSum d := lt_of_lt_of_le zero_lt_one hgs1
  obtain ⟨C, hC, hlip⟩ := exists_avgIterate_greenCovariance_le hGH hd
  obtain ⟨K, hK, hKb⟩ := exists_meanOdometer_le_sqrt_log hGH hd v hv
  have hmaj : Tendsto (fun n : ℕ => (C * K ^ 2) *
      (Real.log n * (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4)))) atTop (𝓝 0) := by
    simpa using (tendsto_log_mul_horizon_rpow_neg hd).const_mul (C * K ^ 2)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop 0] with n _
    have h1 : (0 : ℝ) ≤ (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ |(avg^[dgt4Horizon d n + 1]
        (fun x => ∑' z : Site d, green d x z * green d 0 z)) 0| / greenSqSum d := by positivity
    exact mul_nonneg h1 h2
  · filter_upwards [eventually_ge_atTop 2] with n hn2
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1R
    have haK := hKb n hn2
    have han : (0 : ℝ) ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n := by
      have hmem2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := by
        simpa using memLp_id_gaussianReal (μ := 0) (v := v) 2
      have hint : Integrable (id : ℝ → ℝ) (gaussianReal 0 v) := hmem2.integrable (by norm_num)
      have hposint : Integrable (fun z : ℝ => max z 0) (gaussianReal 0 v) := by
        refine hint.mono ((continuous_id.max continuous_const).measurable.aestronglyMeasurable) ?_
        refine Filter.Eventually.of_forall fun z => ?_
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        show |max z 0| ≤ |z|
        rcases le_or_gt 0 z with h | h
        · rw [max_eq_left h]
        · rw [max_eq_right h.le, abs_zero]
          exact abs_nonneg z
      have h0 : meanOdometer (centeredMassLaw d (gaussianReal 0 v)) 0
          ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n :=
        meanOdometer_mono (by omega) (gaussianReal 0 v) hposint (Nat.zero_le n)
      rwa [meanOdometer_zero d (gaussianReal 0 v)] at h0
    have hsqlog : (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2
        ≤ K ^ 2 * Real.log n := by
      nlinarith [haK, han, Real.sq_sqrt hlogn, Real.sqrt_nonneg (Real.log n), hK]
    have hk1 : 1 ≤ dgt4Horizon d n := one_le_dgt4Horizon hd n
    have hkR : (0 : ℝ) < (dgt4Horizon d n : ℝ) := by exact_mod_cast hk1
    have hlipn := hlip (dgt4Horizon d n + 1) (by omega)
    have hmono : ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ ((4 - (d : ℝ)) / 4)
        ≤ (dgt4Horizon d n : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
      refine Real.rpow_le_rpow_of_nonpos hkR ?_ (by linarith)
      push_cast
      linarith
    have hneg : ((4 : ℝ) - (d : ℝ)) / 4 = -(((d : ℝ) - 4) / 4) := by ring
    rw [hneg] at hmono
    have hLip : |(avg^[dgt4Horizon d n + 1]
        (fun x => ∑' z : Site d, green d x z * green d 0 z)) 0| / greenSqSum d
        ≤ C * (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4)) := by
      refine le_trans hlipn ?_
      rw [hneg] at hlipn ⊢
      exact mul_le_mul_of_nonneg_left hmono hC.le
    have hLipnn : (0 : ℝ) ≤ |(avg^[dgt4Horizon d n + 1]
        (fun x => ∑' z : Site d, green d x z * green d 0 z)) 0| / greenSqSum d := by positivity
    have hrpnn : (0 : ℝ) ≤ (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4)) :=
      Real.rpow_nonneg hkR.le _
    calc (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2 *
          (|(avg^[dgt4Horizon d n + 1]
              (fun x => ∑' z : Site d, green d x z * green d 0 z)) 0| / greenSqSum d)
        ≤ (K ^ 2 * Real.log n) * (C * (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4))) := by
          exact mul_le_mul hsqlog hLip hLipnn (by positivity)
      _ = (C * K ^ 2) * (Real.log n * (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4))) := by ring


end Sandpile
