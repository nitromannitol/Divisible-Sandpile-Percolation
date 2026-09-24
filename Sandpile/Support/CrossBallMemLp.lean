/-
Square integrability of the ball kernel of `sandpile.tex:2076-2088`.

Every clause of `Sandpile.Continuum.IsWhiteNoise` is stated for square
integrable test functions, so nothing at all can be said about the ball field
`𝒳_s` until the kernel is known to be in `L²`.  That is proved here, for the two
dimensions the crossing statements fix.

The kernel depends on the point of the plane and the integration variable only
through `planePoint u - z`, so it is the kernel at the origin composed with
`z ↦ planePoint u - z`, which preserves Lebesgue measure; the statement for a
general centre follows from the statement at the origin.

At the origin the square of the kernel is dominated by a power of `1/‖y‖` below
the dimension, which is exactly the hypothesis of
`MeasureTheory.integrableOn_ball_of_norm_le_rpow`.  In dimension three the
kernel is `(1/‖y‖ - 1/s)/4π` inside the ball, so its square is at most
`‖y‖^{-2}/(4π)²`, and `2 < 3`.  In dimension two it is `log(s/‖y‖)/2π`, and
`log x ≤ 2√x` for `x ≥ 0` gives `log(s/‖y‖)² ≤ 4 s/‖y‖`, so the square is at most
`(4s/(2π)²)‖y‖^{-1}`, and `1 < 2`.  Outside the ball the kernel vanishes, so
integrability on the ball is integrability on the plane.

The one point where the bound fails is the centre in dimension three, where the
junk value `1/0 = 0` makes the kernel `-1/(4πs)` while `‖0‖^{-2} = 0`; a point
is null, so the hypothesis is taken almost everywhere.
-/
import Sandpile.Support.CrossBallGauss

open MeasureTheory Metric Set

namespace Sandpile.Frozen.FixedScaleCrossings

/-- The ball kernel written at the origin: `ballKernel d s u z` is this function
of `planePoint u - z`. -/
noncomputable def centredKernel (d : ℕ) (s : ℝ) (y : Sandpile.Continuum.Space d) : ℝ :=
  if ‖y‖ < s then
    (if d = 2 then (1 / (2 * Real.pi)) * Real.log (s / ‖y‖)
     else (1 / (4 * Real.pi)) * (1 / ‖y‖ - 1 / s))
  else 0

theorem ballKernel_eq_centredKernel (d : ℕ) (s : ℝ) (u : Sandpile.Continuum.Space 2) :
    ballKernel d s u = fun z => centredKernel d s (planePoint (d := d) u - z) := rfl

theorem measurable_centredKernel (d : ℕ) (s : ℝ) :
    Measurable (centredKernel d s) := by
  have hnorm : Measurable (fun y : Sandpile.Continuum.Space d => ‖y‖) :=
    continuous_norm.measurable
  unfold centredKernel
  by_cases hd2 : d = 2
  · simp only [if_pos hd2]
    exact Measurable.ite (measurableSet_lt hnorm measurable_const)
      ((Real.measurable_log.comp (measurable_const.div hnorm)).const_mul _) measurable_const
  · simp only [if_neg hd2]
    exact Measurable.ite (measurableSet_lt hnorm measurable_const)
      (((measurable_const.div hnorm).sub measurable_const).const_mul _) measurable_const
/-- In dimension two the square of the ball kernel is dominated by `C/‖y‖`. -/
theorem centredKernel_two_sq_le {s : ℝ} (hs : 0 < s) (y : Sandpile.Continuum.Space 2) :
    ‖centredKernel 2 s y ^ 2‖ ≤ (4 * s / (2 * Real.pi) ^ 2) * ‖y‖ ^ (-(1 : ℝ)) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpi2 : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  have hr0 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  have hrp : (0 : ℝ) ≤ ‖y‖ ^ (-(1 : ℝ)) := Real.rpow_nonneg hr0 _
  have hC : (0 : ℝ) ≤ 4 * s / (2 * Real.pi) ^ 2 := by positivity
  by_cases hlt : ‖y‖ < s
  · rcases eq_or_lt_of_le hr0 with hzero | hpos
    · have hk : centredKernel 2 s y = 0 := by
        unfold centredKernel
        rw [if_pos hlt, if_pos rfl, ← hzero]
        simp
      rw [hk]
      simpa using mul_nonneg hC hrp
    · have hk : centredKernel 2 s y = (1 / (2 * Real.pi)) * Real.log (s / ‖y‖) := by
        unfold centredKernel
        rw [if_pos hlt, if_pos rfl]
      have hq : (1 : ℝ) ≤ s / ‖y‖ := (one_le_div hpos).mpr hlt.le
      have hqnn : (0 : ℝ) ≤ s / ‖y‖ := le_trans zero_le_one hq
      have hlognn : 0 ≤ Real.log (s / ‖y‖) := Real.log_nonneg hq
      have hlog : Real.log (s / ‖y‖) ≤ 2 * Real.sqrt (s / ‖y‖) := by
        have h := Real.log_le_rpow_div hqnn (by norm_num : (0 : ℝ) < 1 / 2)
        rw [← Real.sqrt_eq_rpow] at h
        linarith
      have hsq : Real.sqrt (s / ‖y‖) ^ 2 = s / ‖y‖ := Real.sq_sqrt hqnn
      have hL2 : Real.log (s / ‖y‖) ^ 2 ≤ 4 * (s / ‖y‖) := by
        nlinarith [Real.sqrt_nonneg (s / ‖y‖)]
      have hpne : (2 * Real.pi) ≠ 0 := ne_of_gt hpi
      have hyne : ‖y‖ ≠ 0 := ne_of_gt hpos
      rw [hk, Real.rpow_neg_one]
      calc ‖(1 / (2 * Real.pi) * Real.log (s / ‖y‖)) ^ 2‖
          = Real.log (s / ‖y‖) ^ 2 / (2 * Real.pi) ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            field_simp
        _ ≤ (4 * (s / ‖y‖)) / (2 * Real.pi) ^ 2 := by gcongr
        _ = 4 * s / (2 * Real.pi) ^ 2 * ‖y‖⁻¹ := by field_simp
  · have hk : centredKernel 2 s y = 0 := by
      unfold centredKernel
      rw [if_neg hlt]
    rw [hk]
    simpa using mul_nonneg hC hrp

/-- In dimension three the square of the ball kernel is dominated by `C/‖y‖²`
away from the centre. -/
theorem centredKernel_three_sq_le {s : ℝ} (hs : 0 < s) {y : Sandpile.Continuum.Space 3}
    (hy : y ≠ 0) :
    ‖centredKernel 3 s y ^ 2‖ ≤ (1 / (4 * Real.pi)) ^ 2 * ‖y‖ ^ (-(2 : ℝ)) := by
  have hpi : (0 : ℝ) < 4 * Real.pi := by positivity
  have hr0 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  have hpos : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hrw : ‖y‖ ^ (-(2 : ℝ)) = (‖y‖ ^ 2)⁻¹ := by
    rw [Real.rpow_neg hr0, ← Real.rpow_natCast ‖y‖ 2]
    norm_num
  have hCnn : (0 : ℝ) ≤ (1 / (4 * Real.pi)) ^ 2 * ‖y‖ ^ (-(2 : ℝ)) := by positivity
  by_cases hlt : ‖y‖ < s
  · have hk : centredKernel 3 s y = (1 / (4 * Real.pi)) * (1 / ‖y‖ - 1 / s) := by
      unfold centredKernel
      rw [if_pos hlt]
      norm_num
    have hinv : 1 / s ≤ 1 / ‖y‖ := one_div_le_one_div_of_le hpos hlt.le
    have hspos : (0 : ℝ) < 1 / s := by positivity
    have hb0 : (0 : ℝ) ≤ 1 / ‖y‖ - 1 / s := by linarith
    have hsq : (1 / ‖y‖ - 1 / s) ^ 2 ≤ (1 / ‖y‖) ^ 2 := by nlinarith
    have h1 : (1 / ‖y‖) ^ 2 = (‖y‖ ^ 2)⁻¹ := by field_simp
    rw [hk, hrw, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (1 / (4 * Real.pi) * (1 / ‖y‖ - 1 / s)) ^ 2
        = (1 / (4 * Real.pi)) ^ 2 * (1 / ‖y‖ - 1 / s) ^ 2 := by ring
      _ ≤ (1 / (4 * Real.pi)) ^ 2 * (1 / ‖y‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (1 / (4 * Real.pi)) ^ 2 * (‖y‖ ^ 2)⁻¹ := by rw [h1]
  · have hk : centredKernel 3 s y = 0 := by
      unfold centredKernel
      rw [if_neg hlt]
    rw [hk]
    simpa using hCnn

/-- The square of the ball kernel is integrable on the ball it lives on. -/
theorem integrableOn_centredKernel_sq {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun y : Sandpile.Continuum.Space d => centredKernel d s y ^ 2)
      (Metric.ball 0 s) volume := by
  rcases hd with rfl | rfl
  · have hdim : 1 ≤ Module.finrank ℝ (Sandpile.Continuum.Space 2) := by
      rw [finrank_euclideanSpace_fin]
      norm_num
    have hα : (1 : ℝ) < (Module.finrank ℝ (Sandpile.Continuum.Space 2) : ℝ) := by
      rw [finrank_euclideanSpace_fin]
      norm_num
    refine integrableOn_ball_of_norm_le_rpow (C := 4 * s / (2 * Real.pi) ^ 2) hdim hα ?_
      ((measurable_centredKernel 2 s).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => centredKernel_two_sq_le hs x
  · have hdim : 1 ≤ Module.finrank ℝ (Sandpile.Continuum.Space 3) := by
      rw [finrank_euclideanSpace_fin]
      norm_num
    have hα : (2 : ℝ) < (Module.finrank ℝ (Sandpile.Continuum.Space 3) : ℝ) := by
      rw [finrank_euclideanSpace_fin]
      norm_num
    have hae : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : Sandpile.Continuum.Space 3) s)),
        x ≠ (0 : Sandpile.Continuum.Space 3) := by
      refine MeasureTheory.ae_restrict_of_ae ?_
      rw [MeasureTheory.ae_iff]
      simp
    refine integrableOn_ball_of_norm_le_rpow (C := (1 / (4 * Real.pi)) ^ 2) hdim hα ?_
      ((measurable_centredKernel 3 s).pow_const 2).aestronglyMeasurable
    filter_upwards [hae] with x hx
    exact centredKernel_three_sq_le hs hx


/-- Hence it is integrable on the plane: it vanishes off that ball. -/
theorem integrable_centredKernel_sq {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s) :
    Integrable (fun y : Sandpile.Continuum.Space d => centredKernel d s y ^ 2) volume := by
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (integrableOn_centredKernel_sq hd hs) ?_
  intro x hx
  have hns : ¬ ‖x‖ < s := by
    simpa [Metric.mem_ball, dist_zero_right] using hx
  simp [centredKernel, hns]

/-- The ball kernel at the origin is square integrable. -/
theorem memLp_centredKernel {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s) :
    MemLp (centredKernel d s) 2 (volume : Measure (Sandpile.Continuum.Space d)) :=
  (memLp_two_iff_integrable_sq (measurable_centredKernel d s).aestronglyMeasurable).mpr
    (integrable_centredKernel_sq hd hs)

/-- The ball kernel of `sandpile.tex:2076-2088` is square integrable, which is
what every clause of `Sandpile.Continuum.IsWhiteNoise` asks for before it says
anything about the ball field. -/
theorem memLp_ballKernel {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s)
    (u : Sandpile.Continuum.Space 2) :
    MemLp (ballKernel d s u) 2 (volume : Measure (Sandpile.Continuum.Space d)) := by
  have hmp : MeasurePreserving
      (fun z : Sandpile.Continuum.Space d => planePoint (d := d) u - z) volume volume :=
    Measure.measurePreserving_sub_left volume _
  have h := (memLp_centredKernel hd hs (d := d)).comp_measurePreserving hmp
  rw [ballKernel_eq_centredKernel]
  exact h

/-- The ball field is positively associated, with no remaining hypothesis on the
kernel: `sandpile.tex:2104` applied to `𝒳_s` for `d = 2, 3`. -/
theorem isAssociatedField_ballField_of_whiteNoise
    (hPitt : Sandpile.External.PittGaussianFKG)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : ℝ} (hs : 0 < s) :
    Sandpile.Continuum.IsAssociatedField P (ballField d W s) :=
  isAssociatedField_ballField hPitt hd hW s (fun u => memLp_ballKernel hd hs u)

end Sandpile.Frozen.FixedScaleCrossings
