import Sandpile.Support.CrossBallMemLp
import Sandpile.Support.CrossBallScale
import Sandpile.Support.CrossScale

/-!
# `L¹` bounds for the ball Green kernel

Shows that the ball Green kernel `ballKernel d s u` has an integrable absolute value on
`Space d`, that this integral scales as the square of the radius `s`, and that pairing the
kernel against an essentially bounded function is therefore uniformly bounded by a constant
times `crossScale d s`, the scale that later controls a crossing probability.
-/

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open Sandpile.Continuum Sandpile.Support Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal RealInnerProductSpace

/-- The ball Green kernel `ballKernel d s u` is integrable on `Space d`, since it is
essentially bounded and vanishes outside the finite-measure ball `Metric.ball (planePoint u)
s`. -/
theorem Sandpile.Support.integrable_ballKernel {d : ℕ}
    (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s) (u : Space 2) :
    Integrable (ballKernel d s u) (volume : Measure (Space d)) := by
  let K : Set (Space d) := Metric.ball (planePoint u) s
  have hK : MeasurableSet K := measurableSet_ball
  letI : IsFiniteMeasure ((volume : Measure (Space d)).restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (show (volume : Measure (Space d)) (Metric.ball (planePoint u) s) < ⊤
        from measure_ball_lt_top)⟩
  have hf : IntegrableOn (ballKernel d s u) K volume :=
    ((memLp_ballKernel hd hs u).restrict K).integrable (by norm_num)
  have hsame : K.indicator (ballKernel d s u) = ballKernel d s u := by
    funext y
    by_cases hy : y ∈ K
    · exact Set.indicator_of_mem hy _
    · rw [Set.indicator_of_notMem hy]
      symm
      change (if ‖planePoint u - y‖ < s then _ else 0) = 0
      apply if_neg
      simpa only [K, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
  rw [← hsame]
  exact (integrable_indicator_iff hK).mpr hf

/-- Rescaling the ball, its centre and the radius by `a > 0` changes the integral of the
kernel's absolute value by the factor `a ^ d * |if d = 2 then 1 else 1 / a|`, obtained by the
change of variables `y ↦ a • y` and the scaling law `ballKernel_smul`. -/
theorem Sandpile.Support.integral_abs_ballKernel_smul {d : ℕ} {a : ℝ}
    (ha : 0 < a) (s : ℝ) (u : Space 2) :
    ∫ y, |ballKernel d (a * s) (a • u) y| =
      a ^ d * (|if d = 2 then (1 : ℝ) else 1 / a| * ∫ z, |ballKernel d s u z|) := by
  have hapow : (0 : ℝ) < a ^ d := pow_pos ha d
  have hfr : Module.finrank ℝ (Space d) = d := finrank_euclideanSpace_fin
  have h := MeasureTheory.Measure.integral_comp_smul (volume : Measure (Space d))
    (fun y => |ballKernel d (a * s) (a • u) y|) a
  rw [hfr, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a ^ d)⁻¹), smul_eq_mul] at h
  have hg : ∀ z : Space d,
      |ballKernel d (a * s) (a • u) (a • z)| =
        |if d = 2 then (1 : ℝ) else 1 / a| * |ballKernel d s u z| := by
    intro z
    rw [ballKernel_smul ha s u z, abs_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hg), integral_const_mul] at h
  calc (∫ y, |ballKernel d (a * s) (a • u) y|) =
      a ^ d * ((a ^ d)⁻¹ * ∫ y, |ballKernel d (a * s) (a • u) y|) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hapow), one_mul]
    _ = _ := by rw [← h]

/-- The integral of `|ballKernel d s ·|` does not depend on the centre `u`: rewriting through
`ballKernel_eq_centredKernel` reduces it to `integral_sub_left_eq_self` for the translation-
invariant `centredKernel`. -/
theorem Sandpile.Support.integral_abs_ballKernel_center (d : ℕ) (s : ℝ)
    (u v : Space 2) :
    ∫ y, |ballKernel d s u y| = ∫ y, |ballKernel d s v y| := by
  rw [ballKernel_eq_centredKernel, ballKernel_eq_centredKernel]
  exact (integral_sub_left_eq_self (fun z => |centredKernel d s z|)
    (volume : Measure (Space d)) (planePoint u)).trans
      (integral_sub_left_eq_self (fun z => |centredKernel d s z|)
        (volume : Measure (Space d)) (planePoint v)).symm

/-- If `f` is integrable and `g` is bounded by `M` almost everywhere, then `|∫ f * g| ≤ M *
∫ |f|`. -/
theorem Sandpile.Support.abs_integral_mul_le_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (M : ℝ)
    (hbound : ∀ᵐ x ∂μ, |g x| ≤ M) :
    |∫ x, f x * g x ∂μ| ≤ M * ∫ x, |f x| ∂μ := by
  calc
    |∫ x, f x * g x ∂μ| ≤ ∫ x, M * |f x| ∂μ := by
      have hb : ∀ᵐ x ∂μ, ‖f x * g x‖ ≤ M * ‖f x‖ := by
        filter_upwards [hbound] with x hx
        simpa only [Real.norm_eq_abs, abs_mul, mul_comm] using
          mul_le_mul_of_nonneg_left hx (abs_nonneg (f x))
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_of_norm_le (hf.norm.const_mul M) hb
    _ = M * ∫ x, |f x| ∂μ := integral_const_mul _ _

/-- For `0 < s ≤ 1`, the square `s ^ 2` is at most `crossScale d s`, which equals `s ^ 2` outright
when `d = 2` and equals `s ^ (3 / 2)` otherwise, where `s ^ 2 ≤ s ^ (3 / 2)` because `s ≤ 1` and
`3 / 2 ≤ 2`. -/
theorem Sandpile.Support.sq_le_crossScale {d : ℕ} {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) : s ^ 2 ≤ crossScale d s := by
  unfold crossScale
  split_ifs
  · rfl
  · have hr := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show (3:ℝ)/2 ≤ 2 by norm_num)
    simpa using hr

/-- A function in `MemLp f ∞ μ` has an almost-everywhere pointwise bound `M ≥ 0`, read off
from its essential supremum norm. -/
theorem Sandpile.Support.exists_ae_bound_of_memLp_top {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : MemLp f ∞ μ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂μ, |f x| ≤ M := by
  have h := hf.eLpNorm_lt_top
  rw [eLpNorm_exponent_top] at h
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp h
  refine ⟨(C : ℝ), C.coe_nonneg, ?_⟩
  filter_upwards [hC] with x hx
  exact_mod_cast hx

/-- **The integral of `|ballKernel d s ·|` scales as `s ^ 2`.** Combines centre-invariance
(`integral_abs_ballKernel_center`) with the scaling law (`integral_abs_ballKernel_smul`),
using `hd : d = 2 ∨ d = 3` to simplify the correction factor, to reduce the general case to the
reference value at radius `1` and centre `0`. -/
theorem Sandpile.Support.integral_abs_ballKernel_eq_scale_sq {d : ℕ}
    (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s) (u : Space 2) :
    ∫ y, |ballKernel d s u y| = s ^ 2 * ∫ y, |ballKernel d 1 0 y| := by
  rw [Sandpile.Support.integral_abs_ballKernel_center d s u 0]
  have h := Sandpile.Support.integral_abs_ballKernel_smul (d := d) hs 1 (0 : Space 2)
  simp only [mul_one, smul_zero] at h
  rw [h]
  rcases hd with rfl | rfl
  · simp
  · simp only [show ¬ (3 : ℕ) = 2 by decide, if_false, abs_of_pos (one_div_pos.mpr hs)]
    field_simp

/-- **Pairing the ball Green kernel with an essentially bounded function is uniformly bounded
by a constant times the crossing scale.** For any `g` in `MemLp g ∞ volume`, there is `C ≥ 0`
with `|∫ y, ballKernel d s u y * g y| ≤ C * crossScale d s` for every radius `0 < s ≤ 1` and
every planar centre `u`. -/
theorem Sandpile.Support.exists_ballKernel_pairing_bound {d : ℕ}
    (hd : d = 2 ∨ d = 3) (g : Space d → ℝ) (hg : MemLp g ∞ volume) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ u : Space 2,
      |∫ y, ballKernel d s u y * g y| ≤ C * crossScale d s := by
  obtain ⟨M, hM0, hM⟩ := Sandpile.Support.exists_ae_bound_of_memLp_top volume g hg
  let C := M * ∫ y, |ballKernel d 1 0 y|
  have hC : 0 ≤ C := mul_nonneg hM0 (integral_nonneg fun y => abs_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro s hs hs1 u
  calc |∫ y, ballKernel d s u y * g y| ≤ M * ∫ y, |ballKernel d s u y| :=
      Sandpile.Support.abs_integral_mul_le_bound volume _ g
        (Sandpile.Support.integrable_ballKernel hd hs u) M hM
    _ = C * s ^ 2 := by
      rw [Sandpile.Support.integral_abs_ballKernel_eq_scale_sq hd hs u]
      dsimp [C]
      ring
    _ ≤ C * crossScale d s :=
      mul_le_mul_of_nonneg_left (Sandpile.Support.sq_le_crossScale hs hs1) hC
