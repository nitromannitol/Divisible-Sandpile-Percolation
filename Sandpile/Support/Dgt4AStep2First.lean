/-
The first display of Step 2 of case (a) (`sandpile.tex:5104-5107`):

  "By `eq:dgt4-centered-value-decay`, stationarity, Jensen's inequality, and
   `eq:dgt4-mean-increment-bound`,
   `\E u_n(0)\,\E[P^{k_n+1}|V_\infty-u_{n-k_n}+\E u_n(0)|(0)]\to0`."

The four inputs are exactly the four used here.  `P^{k_n+1}` leaves the mean unchanged
because the mean of `|V_\infty-u_m+c|` does not depend on the site
(`Support/Dgt4AStep2Site.lean`); Jensen's inequality turns the second moment of Step 1 into
the first moment; `eq:dgt4-centered-value-decay` bounds that first moment by
`Cm^{-(d-4)/(4d)}` at `m=n-k_n`; and the mean-increment bound replaces the centring constant
`\E u_{n-k_n}(0)` of Step 1 by the constant `\E u_n(0)` of the display, at the cost of
`k_n\E u_n(0)/(n-k_n)`.

The horizon enters only through the two conditions imposed here: `2k_n\leq n`, so that
`n-k_n` is at least `n/2`, and `k_n\log n/n\to0`.  The paper's
`k_n=\lceil(\log(n+2))^{6/(d-4)}\rceil` satisfies both, and so does any polylogarithmic
horizon; the display does not see which.
-/
import Sandpile.Support.Dgt4AStep2Site
import Sandpile.Support.Dgt4AMeanIncrement

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

theorem integral_abs_add_const_le {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (c c' : ℝ)
    (h1 : Integrable (fun x => |f x + c|) μ) (h2 : Integrable (fun x => |f x + c'|) μ) :
    (∫ x, |f x + c| ∂μ) ≤ (∫ x, |f x + c'| ∂μ) + |c - c'| := by
  have hpt : ∀ x, |f x + c| ≤ |f x + c'| + |c - c'| := by
    intro x
    have hx : f x + c = (f x + c') + (c - c') := by ring
    rw [hx]
    exact abs_add_le _ _
  calc (∫ x, |f x + c| ∂μ) ≤ ∫ x, (|f x + c'| + |c - c'|) ∂μ :=
        integral_mono h1 (h2.add (integrable_const _)) hpt
    _ = (∫ x, |f x + c'| ∂μ) + |c - c'| := by
        rw [integral_add h2 (integrable_const _), integral_const]
        simp

theorem meanOdometer_diff_le (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z => max z 0) ν) (m : ℕ) (hm : 1 ≤ m) :
    ∀ n : ℕ, m ≤ n →
      (m : ℝ) * (meanOdometer (centeredMassLaw d ν) n - meanOdometer (centeredMassLaw d ν) m)
        ≤ ((n : ℝ) - m) * meanOdometer (centeredMassLaw d ν) n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnR : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hmR hmn
    have hstep := meanOdometer_increment_le_div hd ν hint hmean hpos n (le_trans hm hn)
    rw [le_div_iff₀ hnR] at hstep
    have hmono : meanOdometer (centeredMassLaw d ν) n
        ≤ meanOdometer (centeredMassLaw d ν) (n + 1) := meanOdometer_mono hd ν hpos (Nat.le_succ n)
    have hnn : (0 : ℝ) ≤ meanOdometer (centeredMassLaw d ν) n := by
      have h0 : meanOdometer (centeredMassLaw d ν) 0 ≤ meanOdometer (centeredMassLaw d ν) n :=
        meanOdometer_mono hd ν hpos (Nat.zero_le n)
      rwa [meanOdometer_zero d ν] at h0
    have hBA : (0 : ℝ) ≤ meanOdometer (centeredMassLaw d ν) (n + 1)
        - meanOdometer (centeredMassLaw d ν) n := by linarith
    have h1 : (m : ℝ) * (meanOdometer (centeredMassLaw d ν) (n + 1)
        - meanOdometer (centeredMassLaw d ν) n) ≤ meanOdometer (centeredMassLaw d ν) n := by
      nlinarith [hstep, hmn, hBA]
    push_cast
    nlinarith [ih, h1, hmono, hnn, hmn]

/-- `\sqrt{\log n}\,n^{-\delta}\to0` for every `\delta>0`: `\log n\leq n^{\delta}/\delta`. -/
theorem tendsto_sqrt_log_mul_rpow_neg (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => Real.sqrt (Real.log n) * (n : ℝ) ^ (-δ)) atTop (𝓝 0) := by
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have hsq : (0 : ℝ) < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hmaj : Tendsto (fun n : ℕ => (Real.sqrt δ)⁻¹ * (n : ℝ) ^ (-(δ / 2))) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(δ / 2))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hhalf).comp tendsto_natCast_atTop_atTop
    simpa using h.const_mul (Real.sqrt δ)⁻¹
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => ?_) ?_ hmaj
  · have h1 : (0 : ℝ) ≤ Real.sqrt (Real.log n) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-δ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlog : Real.log n ≤ (n : ℝ) ^ δ / δ := Real.log_le_rpow_div (by linarith) hδ
    have hrpowpos : (0 : ℝ) < (n : ℝ) ^ δ := Real.rpow_pos_of_pos hnpos δ
    have hhalfeq : δ * (1 / 2 : ℝ) = δ / 2 := by ring
    have hsplit : Real.sqrt ((n : ℝ) ^ δ / δ) = (Real.sqrt δ)⁻¹ * (n : ℝ) ^ (δ / 2) := by
      rw [div_eq_mul_inv, Real.sqrt_mul hrpowpos.le, Real.sqrt_inv, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hnpos.le, hhalfeq, mul_comm]
    have hrootle : Real.sqrt (Real.log n) ≤ (Real.sqrt δ)⁻¹ * (n : ℝ) ^ (δ / 2) := by
      rw [← hsplit]
      exact Real.sqrt_le_sqrt hlog
    have hcomb : (n : ℝ) ^ (δ / 2) * (n : ℝ) ^ (-δ) = (n : ℝ) ^ (-(δ / 2)) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-δ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc Real.sqrt (Real.log n) * (n : ℝ) ^ (-δ)
        ≤ ((Real.sqrt δ)⁻¹ * (n : ℝ) ^ (δ / 2)) * (n : ℝ) ^ (-δ) :=
          mul_le_mul_of_nonneg_right hrootle hnn
      _ = (Real.sqrt δ)⁻¹ * (n : ℝ) ^ (-(δ / 2)) := by rw [mul_assoc, hcomb]


set_option maxHeartbeats 1000000 in
theorem exists_step2_first_bound
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0)
    (k : ℕ → ℕ) (hk2 : ∀ᶠ n : ℕ in atTop, 2 * k n ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n *
        (∫ ζ, |infiniteGreenField ζ 0 - odometerOf ζ (n - k n) 0
            + meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n|
          ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
        ≤ C * (Real.sqrt (Real.log n) * (n : ℝ) ^ (-(((d : ℝ) - 4) / (4 * d))))
          + C * ((k n : ℝ) * Real.log n / n) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨C, hC, hbnd⟩ := exists_integral_abs_centeredValue_le_gaussian hGH hd v hv
  obtain ⟨K, hK, hKb⟩ := exists_meanOdometer_le_sqrt_log hGH hd v hv
  have hmem2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := by
    simpa using memLp_id_gaussianReal (μ := 0) (v := v) 2
  have hint : Integrable (id : ℝ → ℝ) (gaussianReal 0 v) := hmem2.integrable (by norm_num)
  have hmeanz : (∫ z, z ∂(gaussianReal 0 v)) = 0 := ProbabilityTheory.integral_id_gaussianReal
  have hposint : Integrable (fun z : ℝ => max z 0) (gaussianReal 0 v) := by
    refine hint.mono ((continuous_id.max continuous_const).measurable.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    show |max z 0| ≤ |z|
    rcases le_or_gt 0 z with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h.le, abs_zero]
      exact abs_nonneg z
  have hsqint : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
    simpa using h
  set δ : ℝ := ((d : ℝ) - 4) / (4 * d) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    have h4 : (0 : ℝ) < (d : ℝ) - 4 := by linarith
    have hdpos : (0 : ℝ) < 4 * (d : ℝ) := by linarith
    positivity
  have htwo : (0 : ℝ) < (2 : ℝ) ^ δ := Real.rpow_pos_of_pos (by norm_num) δ
  have hexp : (4 - (d : ℝ)) / (4 * (d : ℝ)) = -δ := by rw [hδdef]; ring
  have hmtend : Tendsto (fun n : ℕ => n - k n) atTop atTop := by
    refine tendsto_atTop.2 fun N => ?_
    filter_upwards [hk2, eventually_ge_atTop (2 * N)] with n hn h2
    omega
  refine ⟨C * K * (2 : ℝ) ^ δ + 2 * K ^ 2 + 1, by positivity, ?_⟩
  filter_upwards [hk2, eventually_ge_atTop 2, hmtend.eventually hbnd,
    hmtend.eventually (eventually_ge_atTop 1)] with n hk hn2 hbm hm1
  set m : ℕ := n - k n with hmdef
  set A : ℕ → ℝ := fun t => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) t with hAdef
  set X : (Site d → ℝ) → ℝ := fun ζ => infiniteGreenField ζ 0 - odometerOf ζ m 0 with hXdef
  have hmn : m ≤ n := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
  have han : (0 : ℝ) ≤ A n := by
    have h0 : meanOdometer (centeredMassLaw d (gaussianReal 0 v)) 0
        ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n :=
      meanOdometer_mono hd1 (gaussianReal 0 v) hposint (Nat.zero_le n)
    rw [meanOdometer_zero d (gaussianReal 0 v)] at h0
    exact h0
  have hAmn : A m ≤ A n :=
    (meanOdometer_mono hd1 (gaussianReal 0 v) hposint hmn :
      meanOdometer (centeredMassLaw d (gaussianReal 0 v)) m
        ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)
  have haK : A n ≤ K * Real.sqrt (Real.log n) := hKb n hn2
  have hIabs : (∫ ζ, |X ζ + A n| ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      ≤ (∫ ζ, |X ζ + A m| ∂(LatticeProb.iidLaw d (gaussianReal 0 v))) + |A n - A m| :=
    integral_abs_add_const_le _ _
      ((memLp_two_centeredValue hd v hsqint m (A n)).abs.integrable (by norm_num))
      ((memLp_two_centeredValue hd v hsqint m (A m)).abs.integrable (by norm_num))
  have hIm : (∫ ζ, |X ζ + A m| ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      ≤ C * (m : ℝ) ^ (-δ) := by
    rw [← hexp]
    exact hbm
  have hInonneg : (0 : ℝ) ≤ ∫ ζ, |X ζ + A m| ∂(LatticeProb.iidLaw d (gaussianReal 0 v)) :=
    integral_nonneg fun _ => abs_nonneg _
  have hnm : ((n : ℝ) - (m : ℝ)) = (k n : ℝ) := by
    rw [hmdef, Nat.cast_sub (by omega : k n ≤ n)]
    ring
  have hdiff := meanOdometer_diff_le hd1 (gaussianReal 0 v) hint hmeanz hposint m hm1 n hmn
  rw [hnm] at hdiff
  have hn2m : (n : ℝ) ≤ 2 * (m : ℝ) := by
    have : n ≤ 2 * m := by omega
    exact_mod_cast this
  have hdiffle : |A n - A m| ≤ 2 * (k n : ℝ) * A n / (n : ℝ) := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ A n - A m), le_div_iff₀ hnR]
    nlinarith [hdiff, hn2m, (by linarith : (0 : ℝ) ≤ A n - A m)]
  have hmge : (n : ℝ) / 2 ≤ (m : ℝ) := by linarith
  have hhalfpos : (0 : ℝ) < (n : ℝ) / 2 := by linarith
  have hrp : (m : ℝ) ^ (-δ) ≤ ((n : ℝ) / 2) ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos hhalfpos hmge (by linarith)
  have hdivr : ((n : ℝ) / 2) ^ (-δ) = (2 : ℝ) ^ δ * (n : ℝ) ^ (-δ) := by
    rw [Real.div_rpow hnR.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  have hsqlog : A n ^ 2 ≤ K ^ 2 * Real.log n := by
    nlinarith [haK, han, Real.sq_sqrt hlogn, Real.sqrt_nonneg (Real.log n), hK]
  have hnrn : (0 : ℝ) ≤ (n : ℝ) ^ (-δ) := Real.rpow_nonneg hnR.le _
  have hknn : (0 : ℝ) ≤ (k n : ℝ) := Nat.cast_nonneg _
  have hterm1 : A n * (∫ ζ, |X ζ + A m| ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      ≤ (C * K * (2 : ℝ) ^ δ) * (Real.sqrt (Real.log n) * (n : ℝ) ^ (-δ)) := by
    have h1 : (∫ ζ, |X ζ + A m| ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
        ≤ C * ((2 : ℝ) ^ δ * (n : ℝ) ^ (-δ)) := by
      refine le_trans hIm ?_
      rw [← hdivr]
      exact mul_le_mul_of_nonneg_left hrp hC.le
    have h2 := mul_le_mul haK h1 hInonneg (by positivity)
    calc A n * (∫ ζ, |X ζ + A m| ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
        ≤ (K * Real.sqrt (Real.log n)) * (C * ((2 : ℝ) ^ δ * (n : ℝ) ^ (-δ))) := h2
      _ = (C * K * (2 : ℝ) ^ δ) * (Real.sqrt (Real.log n) * (n : ℝ) ^ (-δ)) := by ring
  have hterm2 : A n * |A n - A m| ≤ (2 * K ^ 2) * ((k n : ℝ) * Real.log n / (n : ℝ)) := by
    have h1 : A n * |A n - A m| ≤ A n * (2 * (k n : ℝ) * A n / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiffle han
    refine le_trans h1 ?_
    have hkn : (0 : ℝ) ≤ (k n : ℝ) / (n : ℝ) := by positivity
    have heq1 : A n * (2 * (k n : ℝ) * A n / (n : ℝ))
        = (2 * A n ^ 2) * ((k n : ℝ) / (n : ℝ)) := by
      field_simp
    have heq2 : (2 * K ^ 2) * ((k n : ℝ) * Real.log n / (n : ℝ))
        = (2 * (K ^ 2 * Real.log n)) * ((k n : ℝ) / (n : ℝ)) := by
      field_simp
    rw [heq1, heq2]
    exact mul_le_mul_of_nonneg_right (by linarith [hsqlog]) hkn
  have hfinal : A n * (∫ ζ, |X ζ + A n| ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      ≤ (C * K * (2 : ℝ) ^ δ) * (Real.sqrt (Real.log n) * (n : ℝ) ^ (-δ))
        + (2 * K ^ 2) * ((k n : ℝ) * Real.log n / (n : ℝ)) := by
    have h0 := mul_le_mul_of_nonneg_left hIabs han
    rw [mul_add] at h0
    linarith [h0, hterm1, hterm2]
  refine le_trans hfinal ?_
  have hq1 : (0 : ℝ) ≤ Real.sqrt (Real.log n) * (n : ℝ) ^ (-δ) := by positivity
  have hq2 : (0 : ℝ) ≤ (k n : ℝ) * Real.log n / (n : ℝ) := by positivity
  have hc1 : C * K * (2 : ℝ) ^ δ ≤ C * K * (2 : ℝ) ^ δ + 2 * K ^ 2 + 1 := by nlinarith
  have hc2 : 2 * K ^ 2 ≤ C * K * (2 : ℝ) ^ δ + 2 * K ^ 2 + 1 := by
    nlinarith [mul_pos (mul_pos hC hK) htwo]
  exact add_le_add (mul_le_mul_of_nonneg_right hc1 hq1) (mul_le_mul_of_nonneg_right hc2 hq2)


/-- **The first display of Step 2 of case (a)** (`sandpile.tex:5099-5102`):
`\E u_n(0)\,\E[P^{k_n+1}|V_\infty-u_{n-k_n}+\E u_n(0)|(0)]\to0` for any horizon `k_n`
with `2k_n\leq n` and `k_n\log n/n\to0`. -/
theorem tendsto_meanOdometer_mul_avgIterate_abs_centeredValue
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0)
    (k : ℕ → ℕ) (hk2 : ∀ᶠ n : ℕ in atTop, 2 * k n ≤ n)
    (hklog : Tendsto (fun n : ℕ => (k n : ℝ) * Real.log n / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
        meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n *
          ∫ ζ, (avg^[k n + 1] (fun x => |infiniteGreenField ζ x - odometerOf ζ (n - k n) x
              + meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n|)) 0
            ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      atTop (𝓝 0) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsqint : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
    simpa using h
  have hposint : Integrable (fun z : ℝ => max z 0) (gaussianReal 0 v) := by
    have hmem2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := by
      simpa using memLp_id_gaussianReal (μ := 0) (v := v) 2
    have hint : Integrable (id : ℝ → ℝ) (gaussianReal 0 v) := hmem2.integrable (by norm_num)
    refine hint.mono ((continuous_id.max continuous_const).measurable.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    show |max z 0| ≤ |z|
    rcases le_or_gt 0 z with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h.le, abs_zero]
      exact abs_nonneg z
  set δ : ℝ := ((d : ℝ) - 4) / (4 * d) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    have h4 : (0 : ℝ) < (d : ℝ) - 4 := by linarith
    have hdpos : (0 : ℝ) < 4 * (d : ℝ) := by linarith
    positivity
  obtain ⟨C, hC, hbound⟩ := exists_step2_first_bound hGH hd v hv k hk2
  have hmaj : Tendsto (fun n : ℕ =>
      C * (Real.sqrt (Real.log n) * (n : ℝ) ^ (-δ)) + C * ((k n : ℝ) * Real.log n / n))
      atTop (𝓝 0) := by
    have h1 := (tendsto_sqrt_log_mul_rpow_neg δ hδ).const_mul C
    have h2 := hklog.const_mul C
    simpa using h1.add h2
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop 0] with n _
    have hA : (0 : ℝ) ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n := by
      have h0 : meanOdometer (centeredMassLaw d (gaussianReal 0 v)) 0
          ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n :=
        meanOdometer_mono hd1 (gaussianReal 0 v) hposint (Nat.zero_le n)
      rwa [meanOdometer_zero d (gaussianReal 0 v)] at h0
    have hI : (0 : ℝ) ≤ ∫ ζ, (avg^[k n + 1] (fun x =>
        |infiniteGreenField ζ x - odometerOf ζ (n - k n) x
          + meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n|)) 0
        ∂(LatticeProb.iidLaw d (gaussianReal 0 v)) := by
      refine integral_nonneg fun ζ => ?_
      rw [avg_iterate_eq_finsetSum]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (heatKernel_nonneg _ _ _) (abs_nonneg _)
    exact mul_nonneg hA hI
  · filter_upwards [hbound] with n hn
    rw [integral_avgIterate_abs_centeredValue_eq hd v hsqint (n - k n)
      (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) (k n + 1)]
    exact hn

end Sandpile
