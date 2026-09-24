/-
The white-noise scaling of the ball field, `eq:cont-field-scaling` at
`sandpile.tex:2093-2099`:

  "The change of variables `z = sw` and white-noise scaling give
   `{𝒳_s(su)} = {s 𝒳_1(u)}` in law for `d = 2` and `{√s 𝒳_1(u)}` for `d = 3`."

`Sandpile/Support/CrossBallScale.lean` has the kernel half: dilating the point,
the variable and the radius by `a` leaves the dimension-two kernel unchanged and
multiplies the dimension-three kernel by `1/a`.  This module takes the identity
to the field.

The covariance of the ball field is the `L²` inner product of two kernels, and
dilating the integration variable by `a` multiplies a Lebesgue integral on `ℝ^d`
by `a^d`, so the covariance of the dilated field is `a^d` times the square of the
dimensional factor times the covariance of the field: `a²` in dimension two and
`a³·a^{-2} = a` in dimension three.  Those are the squares of `a` and of `√a`,
which is the paper's `s` and `√s` once `a` is `s` and the radius is one.  Both
fields are centred Gaussian, so the covariances determine the laws, and that last
step is `Sandpile.External.GaussianLawDeterminedByCovariance`.
-/
import Sandpile.Support.CrossBallScale
import Sandpile.Support.CrossBallGauss
import Sandpile.Support.CrossBallMemLp
import Sandpile.External.GaussianLawCovariance

open MeasureTheory Set

namespace Sandpile.Frozen.FixedScaleCrossings

/-- The covariance of the ball kernels under the dilation of
`eq:cont-field-scaling`: the change of variables `y = a z` in the `L²` inner
product contributes `a^d`, and each kernel contributes the dimensional factor
of `ballKernel_smul`. -/
theorem cov_ballKernel_smul {d : ℕ} {a : ℝ} (ha : 0 < a) (s : ℝ)
    (u v : Sandpile.Continuum.Space 2) :
    ∫ y, ballKernel d (a * s) (a • u) y * ballKernel d (a * s) (a • v) y
      = a ^ d * ((if d = 2 then (1 : ℝ) else 1 / a) ^ 2 *
          ∫ z, ballKernel d s u z * ballKernel d s v z) := by
  have hapow : (0 : ℝ) < a ^ d := pow_pos ha d
  have hfr : Module.finrank ℝ (Sandpile.Continuum.Space d) = d := finrank_euclideanSpace_fin
  have h := MeasureTheory.Measure.integral_comp_smul (volume : Measure (Sandpile.Continuum.Space d))
    (fun y => ballKernel d (a * s) (a • u) y * ballKernel d (a * s) (a • v) y) a
  rw [hfr, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a ^ d)⁻¹), smul_eq_mul] at h
  have hg : ∀ z : Sandpile.Continuum.Space d,
      ballKernel d (a * s) (a • u) (a • z) * ballKernel d (a * s) (a • v) (a • z)
        = (if d = 2 then (1 : ℝ) else 1 / a) ^ 2 *
            (ballKernel d s u z * ballKernel d s v z) := by
    intro z
    rw [ballKernel_smul ha s u z, ballKernel_smul ha s v z]
    ring
  have h2 : ∫ z, ballKernel d (a * s) (a • u) (a • z) * ballKernel d (a * s) (a • v) (a • z)
      = (if d = 2 then (1 : ℝ) else 1 / a) ^ 2 *
          ∫ z, ballKernel d s u z * ballKernel d s v z := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hg), MeasureTheory.integral_const_mul]
  rw [h2] at h
  have key : a ^ d * ((a ^ d)⁻¹ *
      ∫ y, ballKernel d (a * s) (a • u) y * ballKernel d (a * s) (a • v) y)
      = ∫ y, ballKernel d (a * s) (a • u) y * ballKernel d (a * s) (a • v) y := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hapow), one_mul]
  rw [← key, ← h]

/-- The factor the dilation puts on the covariance is the square of the paper's:
`a²` in dimension two and `a` in dimension three. -/
theorem scaling_factor {d : ℕ} (hd : d = 2 ∨ d = 3) {a : ℝ} (ha : 0 < a) :
    a ^ d * (if d = 2 then (1 : ℝ) else 1 / a) ^ 2
      = (if d = 2 then a else Real.sqrt a) ^ 2 := by
  rcases hd with rfl | rfl
  · rw [if_pos rfl, if_pos rfl, one_pow, mul_one]
  · rw [if_neg (by norm_num), if_neg (by norm_num), Real.sq_sqrt ha.le, one_div, inv_pow,
      show a ^ 3 = a * a ^ 2 from by ring, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt ha)), mul_one]

/-- The covariance of the ball field under the dilation: the field at the
dilated point with the dilated radius has the covariance of the field scaled by
`a` in dimension two and by `√a` in dimension three. -/
theorem cov_ballField_smul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
    (u v : Sandpile.Continuum.Space 2) :
    ∫ ω, ballField d W (a * s) (a • u) ω * ballField d W (a * s) (a • v) ω ∂P
      = ∫ ω, ((if d = 2 then a else Real.sqrt a) * ballField d W s u ω) *
              ((if d = 2 then a else Real.sqrt a) * ballField d W s v ω) ∂P := by
  have hL : ∫ ω, ballField d W (a * s) (a • u) ω * ballField d W (a * s) (a • v) ω ∂P
      = ∫ y, ballKernel d (a * s) (a • u) y * ballKernel d (a * s) (a • v) y :=
    hW.cov _ _ (memLp_ballKernel hd (mul_pos ha hs) _) (memLp_ballKernel hd (mul_pos ha hs) _)
  have hR : ∫ ω, ballField d W s u ω * ballField d W s v ω ∂P
      = ∫ z, ballKernel d s u z * ballKernel d s v z :=
    hW.cov _ _ (memLp_ballKernel hd hs _) (memLp_ballKernel hd hs _)
  have hpt : ∀ ω, ((if d = 2 then a else Real.sqrt a) * ballField d W s u ω) *
      ((if d = 2 then a else Real.sqrt a) * ballField d W s v ω)
      = (if d = 2 then a else Real.sqrt a) ^ 2 *
          (ballField d W s u ω * ballField d W s v ω) := fun ω => by ring
  have hRHS : ∫ ω, ((if d = 2 then a else Real.sqrt a) * ballField d W s u ω) *
      ((if d = 2 then a else Real.sqrt a) * ballField d W s v ω) ∂P
      = (if d = 2 then a else Real.sqrt a) ^ 2 *
          ∫ z, ballKernel d s u z * ballKernel d s v z := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hR]
  rw [hL, hRHS, cov_ballKernel_smul ha s u v, ← scaling_factor hd ha]
  ring

/-- `eq:cont-field-scaling` (`sandpile.tex:2093-2099`) for the ball field: the
law of `u ↦ 𝒳_{as}(a u)` is the law of `u ↦ a 𝒳_s(u)` in dimension two and of
`u ↦ √a 𝒳_s(u)` in dimension three.  Both sides are centred Gaussian fields, and
their covariances agree by `cov_ballField_smul`, so the classical determination
of a centred Gaussian law by its covariance finishes it. -/
theorem fieldLaw_ballField_smul
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    Sandpile.Continuum.fieldLaw P (fun u ω => ballField d W (a * s) (a • u) ω)
      = Sandpile.Continuum.fieldLaw P
          (fun u ω => (if d = 2 then a else Real.sqrt a) * ballField d W s u ω) := by
  refine hGauss Ω P _ _
    ((isGaussianProcess_ballField hW (a * s)).comp_right
      (fun u : Sandpile.Continuum.Space 2 => a • u))
    ((isGaussianProcess_ballField hW s).smul
      (fun _ => (if d = 2 then a else Real.sqrt a)))
    (fun u => hW.meas _ (memLp_ballKernel hd (mul_pos ha hs) _))
    (fun u => (hW.meas _ (memLp_ballKernel hd hs _)).const_mul _)
    (fun u => hW.mean _ (memLp_ballKernel hd (mul_pos ha hs) _))
    (fun u => ?_)
    (fun u v => cov_ballField_smul hd hW ha hs u v)
  rw [integral_const_mul]
  show (if d = 2 then a else Real.sqrt a) * ∫ ω, W (ballKernel d s u) ω ∂P = 0
  rw [hW.mean _ (memLp_ballKernel hd hs _), mul_zero]

end Sandpile.Frozen.FixedScaleCrossings
