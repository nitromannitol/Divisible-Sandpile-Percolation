import Sandpile.Support.D4Reflection

/-!
# Mean growth over a time block

The increase in the mean odometer over a time block.  Harris's inequality couples a
negative membrane fluctuation with a small averaged odometer, and summing the
increments over many blocks forces the mean odometer above a prescribed level.  This is
the deterministic-plus-correlation-inequality core of the block-increment argument, and
assumes only an i.i.d. scenery with an integrable identity and integrable positive part.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- The `m`-fold iterate of the averaging operator applied to `f` at `x` equals the finite
sum of `f` against the `m`-step `heatKernel`, weighted values on `boxFinset x m`, proved by
unfolding `avg_iterate` and `tsum_heatKernel_mul_eq_sum`. -/
theorem avg_iterate_eq_finsetSum (f : Site d → ℝ) (m : ℕ) (x : Site d) :
    (avg^[m] f) x = ∑ z ∈ boxFinset x m, heatKernel d m x z * f z := by
  rw [avg_iterate, tsum_heatKernel_mul_eq_sum]

/-- The `m`-fold averaged odometer `(avg^[m] (odometerOf ζ n)) x` is integrable under the
i.i.d. scenery law `LatticeProb.iidLaw d ν`, given that the positive part of `ν` is
integrable, proved by rewriting it as the `avg_iterate_eq_finsetSum` finite sum and summing
the integrability of each `odometerOf` term. -/
theorem integrable_avg_iterate_odometerOf (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (m n : ℕ) (x : Site d) :
    Integrable (fun ζ : Site d → ℝ => (avg^[m] (odometerOf ζ n)) x) (LatticeProb.iidLaw d ν) := by
  have he : (fun ζ : Site d → ℝ => (avg^[m] (odometerOf ζ n)) x) =
      fun ζ => ∑ z ∈ boxFinset x m, heatKernel d m x z * odometerOf ζ n z := by
    funext ζ
    exact avg_iterate_eq_finsetSum _ _ _
  rw [he]
  exact integrable_finsetSum _ fun z _ => (integrable_odometerOf d ν hpos n z).const_mul _

/-- The `m`-fold averaged odometer `(avg^[m] (odometerOf ζ n)) x` is measurable in `ζ`,
proved by the same `avg_iterate_eq_finsetSum` rewrite as `integrable_avg_iterate_odometerOf`,
followed by `Finset.measurable_sum`. -/
theorem measurable_avg_iterate_odometerOf (m n : ℕ) (x : Site d) :
    Measurable (fun ζ : Site d → ℝ => (avg^[m] (odometerOf ζ n)) x) := by
  have he : (fun ζ : Site d → ℝ => (avg^[m] (odometerOf ζ n)) x) =
      fun ζ => ∑ z ∈ boxFinset x m, heatKernel d m x z * odometerOf ζ n z := by
    funext ζ
    exact avg_iterate_eq_finsetSum _ _ _
  rw [he]
  exact Finset.measurable_sum _ fun z _ => (measurable_odometerOf n z).const_mul _

/-- The membrane field `membrane ζ m x` is integrable under `LatticeProb.iidLaw d ν` whenever
`ν` has an integrable identity, proved by rewriting `membrane` as the finite sum
`membrane_eq_sum_boxEnum` of `greenTime`-weighted coordinates and summing their
integrability. -/
theorem integrable_membrane (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (m : ℕ) (x : Site d) :
    Integrable (fun ζ : Site d → ℝ => membrane ζ m x) (LatticeProb.iidLaw d ν) := by
  have he : (fun ζ : Site d → ℝ => membrane ζ m x) =
      fun ζ => ∑ i : Fin (boxFinset x m).card,
        greenTime d m x (boxEnum x m i) * ζ (boxEnum x m i) := by
    funext ζ
    exact membrane_eq_sum_boxEnum m x ζ
  rw [he]
  exact integrable_finsetSum _ fun i _ => (integrable_coord ν hint (boxEnum x m i)).const_mul _

/-- The membrane field `fun ζ => membrane ζ m x` is monotone in `ζ` (pointwise order on
scenery configurations), proved by rewriting both sides via `membrane_eq_sum_boxEnum` and
using that each `greenTime` weight is nonnegative. -/
theorem monotone_membrane (m : ℕ) (x : Site d) :
    Monotone (fun ζ : Site d → ℝ => membrane ζ m x) := by
  intro ζ η h
  dsimp only
  rw [membrane_eq_sum_boxEnum m x ζ, membrane_eq_sum_boxEnum m x η]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h _) (greenTime_nonneg _ _ _)

/-- After `n + m` steps (`m ≥ 1`), the odometer at the origin is at least the positive part
of the membrane increment over the last `m` steps plus the `m`-fold averaged odometer at
time `n`, proved by iterating `odometerOf_iterate_lower` `m - 1` times and identifying the
resulting Green-time sum with `membrane` via `membrane_eq_greenTime`. -/
theorem odometerOf_block_lower (ζ : Site d → ℝ) (n m : ℕ) (hm : 1 ≤ m) :
    max 0 (membrane ζ m 0 + (avg^[m] (odometerOf ζ n)) 0) ≤ odometerOf ζ (n + m) 0 := by
  have hi := odometerOf_iterate_lower ζ (m - 1) n
  have hm' : m - 1 + 1 = m := by omega
  rw [hm', sum_avg_iterate_eq_tsum_greenTime] at hi
  have hid : membrane ζ m 0 = ∑' z, greenTime d m 0 z * ζ z := membrane_eq_greenTime ζ m 0
  rw [← hid] at hi
  have htime : n + m = (n + (m - 1)) + 1 := by omega
  rw [htime, odometerOf]
  exact max_le_max_left 0 hi

/-- If the mean odometer at time `n` is at most `h`, the mean increase in the odometer over
the next `m` steps is at least `h/2` times the probability that the membrane drops below
`-3h`, proved by Harris's inequality (`LatticeProb.infinitePi_harris_lower`) coupling the
lower-set event `{3h < -membrane ζ m 0}` with the lower-set event that the `m`-fold averaged
odometer stays below `2h`, then comparing `odometerOf_block_lower` against this coupling and
a Markov bound `h/2 ≤ P(H ≤ 2h)`. -/
theorem mean_block_increment_lower (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (m n : ℕ) (hm : 1 ≤ m)
    {h : ℝ} (hh : 0 < h) (hmeanle : (∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) ≤ h) :
    h / 2 * (LatticeProb.iidLaw d ν).real {ζ | 3 * h < -membrane ζ m 0} ≤
      (∫ ζ, odometerOf ζ (n + m) 0 ∂(LatticeProb.iidLaw d ν)) -
        ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
  classical
  set P := LatticeProb.iidLaw d ν
  set H : (Site d → ℝ) → ℝ := fun ζ => (avg^[m] (odometerOf ζ n)) 0
  set A : Set (Site d → ℝ) := {ζ | 3 * h < -membrane ζ m 0}
  set B : Set (Site d → ℝ) := {ζ | H ζ ≤ 2 * h}
  have hHm : Measurable H := measurable_avg_iterate_odometerOf m n 0
  have hHi : Integrable H P := integrable_avg_iterate_odometerOf ν hpos m n 0
  have hH0 (ζ : Site d → ℝ) : 0 ≤ H ζ := avg_iterate_nonneg (odometerOf_nonneg ζ n) m 0
  have hHE : (∫ ζ, H ζ ∂P) = ∫ ζ, odometerOf ζ n 0 ∂P := integral_avg_odometerOf hd ν hpos m n 0
  have hAm : MeasurableSet A := measurableSet_lt measurable_const (measurable_membrane m 0).neg
  have hBm : MeasurableSet B := measurableSet_le hHm measurable_const
  have hAl : IsLowerSet A := by
    intro η ζ hle hη
    have hv := monotone_membrane m (0 : Site d) hle
    change 3 * h < -membrane η m 0 at hη
    change 3 * h < -membrane ζ m 0
    linarith
  have hBl : IsLowerSet B := by
    intro η ζ hle hη
    have hv := avg_iterate_mono m (fun y => odometerOf_mono n y hle) (0 : Site d)
    change H η ≤ 2 * h at hη
    change H ζ ≤ 2 * h
    exact hv.trans hη
  have hhalf : (1 : ℝ) / 2 ≤ P.real B := by
    have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := H)
      (Filter.Eventually.of_forall hH0) hHi (2 * h)
    rw [hHE] at hmarkov
    have hsubset : Bᶜ ⊆ {ζ | 2 * h ≤ H ζ} := by
      intro ζ hζ
      change ¬H ζ ≤ 2 * h at hζ
      exact (lt_of_not_ge hζ).le
    have hmeasure := measureReal_mono (μ := P) hsubset (measure_ne_top _ _)
    rw [measureReal_compl hBm, probReal_univ] at hmeasure
    have hnn : 0 ≤ P.real {ζ | 2 * h ≤ H ζ} := measureReal_nonneg
    nlinarith
  have harris : P.real A * P.real B ≤ P.real (A ∩ B) :=
    LatticeProb.infinitePi_harris_lower (fun _ : Site d => ν) hAl hBl hAm hBm
  have hpt (ζ : Site d → ℝ) : membrane ζ m 0 + H ζ + h * (A ∩ B).indicator (1 : (Site d → ℝ) → ℝ) ζ
      ≤ odometerOf ζ (n + m) 0 := by
    by_cases hζ : ζ ∈ A ∩ B
    · rw [Set.indicator_of_mem hζ]
      have h1 : 3 * h < -membrane ζ m 0 := hζ.1
      have h2 : H ζ ≤ 2 * h := hζ.2
      have h3 := odometerOf_nonneg ζ (n + m) (0 : Site d)
      change membrane ζ m 0 + H ζ + h * 1 ≤ _
      linarith
    · rw [Set.indicator_of_notMem hζ, mul_zero, add_zero]
      exact (le_max_right _ _).trans (odometerOf_block_lower ζ n m hm)
  have hi : Integrable ((A ∩ B).indicator (1 : (Site d → ℝ) → ℝ)) P :=
    (integrable_const 1).indicator (hAm.inter hBm)
  have hbound := integral_mono
    (((integrable_membrane ν hint m 0).add hHi).add (hi.const_mul h))
    (integrable_odometerOf d ν hpos (n + m) 0) hpt
  simp only [Pi.add_apply] at hbound
  rw [integral_add (f := fun ζ => membrane ζ m 0 + H ζ)
      ((integrable_membrane ν hint m 0).add hHi) (hi.const_mul h),
    integral_add (integrable_membrane ν hint m 0) hHi,
    integral_const_mul, integral_membrane_zero ν hint hmean, hHE,
    integral_indicator_one (hAm.inter hBm)] at hbound
  have hA0 : 0 ≤ P.real A := measureReal_nonneg
  have hproduct := mul_le_mul_of_nonneg_left hhalf hA0
  nlinarith

/-- If `N` times the probability of a membrane drop below `-3h` is at least `2`, then the mean
odometer at time `N * m` is at least `h`, proved by summing `mean_block_increment_lower` over
the `N` blocks (a telescoping sum, `Finset.sum_range_sub`) and deriving a contradiction from
the contrary assumption that the mean odometer stays below `h` throughout, using monotonicity
of the mean odometer (`meanOdometerOf_mono`). -/
theorem mean_ge_of_block_probability (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (m N : ℕ) (hm : 1 ≤ m)
    {h : ℝ} (hh : 0 < h)
    (hp : 2 ≤ (N : ℝ) * (LatticeProb.iidLaw d ν).real {ζ | 3 * h < -membrane ζ m 0}) :
    h ≤ ∫ ζ, odometerOf ζ (N * m) 0 ∂(LatticeProb.iidLaw d ν) := by
  set a : ℕ → ℝ := fun n => ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)
  set p := (LatticeProb.iidLaw d ν).real {ζ | 3 * h < -membrane ζ m 0}
  have ha0 : a 0 = 0 := by simp [a, odometerOf]
  have hmono : Monotone a := meanOdometerOf_mono ν hpos
  change h ≤ a (N * m)
  by_contra hnot
  have hsmall : a (N * m) < h := lt_of_not_ge hnot
  have hstep (k : ℕ) (hk : k ∈ Finset.range N) :
      h / 2 * p ≤ a ((k + 1) * m) - a (k * m) := by
    have hkm : k * m ≤ N * m := Nat.mul_le_mul_right m (Finset.mem_range.mp hk).le
    have hmeanh : a (k * m) ≤ h := (hmono hkm).trans hsmall.le
    have hi := mean_block_increment_lower hd ν hint hmean hpos m (k * m) hm hh hmeanh
    simpa only [Nat.add_mul, Nat.one_mul] using hi
  have hsum := Finset.sum_le_sum hstep
  have htel := Finset.sum_range_sub (fun k => a (k * m)) N
  rw [Nat.zero_mul, ha0, sub_zero] at htel
  rw [htel, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have := mul_le_mul_of_nonneg_left hp (show 0 ≤ h / 2 by positivity)
  nlinarith

end Sandpile
