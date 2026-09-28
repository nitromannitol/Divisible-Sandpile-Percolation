import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
# Smooth cutoff function

A smooth approximation of a sublevel indicator with uniform derivative
bounds, including its shifts, rescalings and approximation margins.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace Sandpile

/-- The smooth cutoff function `1 - Real.smoothTransition x`: equal to `1` for `x ≤ 0`, `0`
for `x ≥ 1`, and smoothly interpolating in between. -/
def smoothCutoff (x : ℝ) : ℝ := 1 - Real.smoothTransition x

/-- `smoothCutoff` is `C^∞`, being `1` minus the smooth function `Real.smoothTransition`. -/
lemma contDiff_smoothCutoff : ContDiff ℝ (⊤ : ℕ∞) smoothCutoff :=
  contDiff_const.sub Real.smoothTransition.contDiff

/-- `smoothCutoff x ≥ 0`, since `Real.smoothTransition x ≤ 1`. -/
lemma smoothCutoff_nonneg (x : ℝ) : 0 ≤ smoothCutoff x :=
  sub_nonneg.mpr (Real.smoothTransition.le_one x)

/-- `smoothCutoff x ≤ 1`, since `Real.smoothTransition x ≥ 0`. -/
lemma smoothCutoff_le_one (x : ℝ) : smoothCutoff x ≤ 1 :=
  sub_le_self 1 (Real.smoothTransition.nonneg x)

/-- `smoothCutoff x = 1` for `x ≤ 0`, since `Real.smoothTransition` vanishes there. -/
lemma smoothCutoff_eq_one {x : ℝ} (hx : x ≤ 0) : smoothCutoff x = 1 := by
  simp [smoothCutoff, Real.smoothTransition.zero_of_nonpos hx]

/-- `smoothCutoff x = 0` for `x ≥ 1`, since `Real.smoothTransition x = 1` there. -/
lemma smoothCutoff_eq_zero {x : ℝ} (hx : 1 ≤ x) : smoothCutoff x = 0 := by
  simp [smoothCutoff, Real.smoothTransition.one_of_one_le hx]

/-- `deriv smoothCutoff` has compact support contained in `[0, 1]`, since `smoothCutoff` is
locally constant, equal to `1` on `(-∞, 0)` and to `0` on `(1, ∞)`. -/
lemma hasCompactSupport_deriv_smoothCutoff : HasCompactSupport (deriv smoothCutoff) := by
  have hs : Function.support (deriv smoothCutoff) ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    by_contra h
    have hd : deriv smoothCutoff x = 0 := by
      by_cases hl : x < 0
      · have he : smoothCutoff =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
          filter_upwards [isOpen_Iio.mem_nhds hl] with y hy
          exact smoothCutoff_eq_one hy.le
        simpa using he.deriv_eq
      · have hr : 1 < x := lt_of_not_ge (fun hx1 => h ⟨le_of_not_gt hl, hx1⟩)
        have he : smoothCutoff =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hr] with y hy
          exact smoothCutoff_eq_zero hy.le
        simpa using he.deriv_eq
    exact hx hd
  exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)

/-- There is a constant `C ≥ 1` uniformly bounding `|deriv smoothCutoff|`,
`|deriv (deriv smoothCutoff)|`, and `|deriv (deriv (deriv smoothCutoff))|`, obtained from
`hasCompactSupport_deriv_smoothCutoff` and continuity via `exists_bound_of_continuous`. -/
lemma exists_smoothCutoff_derivative_bounds : ∃ C ≥ (1 : ℝ),
    (∀ x, |deriv smoothCutoff x| ≤ C) ∧
    (∀ x, |deriv (deriv smoothCutoff) x| ≤ C) ∧
    (∀ x, |deriv (deriv (deriv smoothCutoff)) x| ≤ C) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (deriv smoothCutoff) :=
    (contDiff_infty_iff_deriv.mp contDiff_smoothCutoff).2
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv smoothCutoff)) := (contDiff_infty_iff_deriv.mp h1).2
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv (deriv smoothCutoff))) :=
    (contDiff_infty_iff_deriv.mp h2).2
  obtain ⟨C1, hC1⟩ := hasCompactSupport_deriv_smoothCutoff.exists_bound_of_continuous h1.continuous
  obtain ⟨C2, hC2⟩ :=
    hasCompactSupport_deriv_smoothCutoff.deriv.exists_bound_of_continuous h2.continuous
  obtain ⟨C3, hC3⟩ :=
    hasCompactSupport_deriv_smoothCutoff.deriv.deriv.exists_bound_of_continuous h3.continuous
  refine ⟨max 1 (max C1 (max C2 C3)), le_max_left _ _, ?_, ?_, ?_⟩
  · intro x
    simpa only [Real.norm_eq_abs] using (hC1 x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro x
    simpa only [Real.norm_eq_abs] using (hC2 x).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  · intro x
    simpa only [Real.norm_eq_abs] using (hC3 x).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- The shifted and rescaled cutoff `smoothCutoff ((x + shift) / width)`, equal to `1` for
`x ≤ -shift` and to `0` for `x ≥ width - shift`. -/
def shiftedCutoff (shift width : ℝ) (x : ℝ) : ℝ := smoothCutoff ((x + shift) / width)

/-- `shiftedCutoff shift width` is `C^∞`, being `smoothCutoff` composed with the smooth affine
map `x ↦ (x + shift) / width`. -/
lemma contDiff_shiftedCutoff (shift width : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (shiftedCutoff shift width) :=
  contDiff_smoothCutoff.comp ((contDiff_id.add contDiff_const).div_const width)

/-- The `n`-th iterated derivative of `shiftedCutoff shift width` at `x` equals
`width⁻¹ ^ n * iteratedDeriv n smoothCutoff ((x + shift) / width)`, via the chain rule for
composing with a shift and a constant rescaling. -/
lemma iteratedDeriv_shiftedCutoff (n : ℕ) (shift width x : ℝ) :
    iteratedDeriv n (shiftedCutoff shift width) x =
      (width⁻¹) ^ n * iteratedDeriv n smoothCutoff ((x + shift) / width) := by
  have he : shiftedCutoff shift width =
      fun x => (fun y => smoothCutoff (width⁻¹ * y)) (x + shift) := by
    funext x
    unfold shiftedCutoff
    congr 1
    ring
  rw [he, iteratedDeriv_comp_add_const (f := fun y => smoothCutoff (width⁻¹ * y)) (s := shift)]
  change iteratedDeriv n (fun y => smoothCutoff (width⁻¹ * y)) (x + shift) = _
  have hs := iteratedDeriv_comp_const_mul
    (contDiff_smoothCutoff.of_le (WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))) width⁻¹
  have ha : width⁻¹ * (x + shift) = (x + shift) / width := by ring
  simpa only [ha] using congrFun hs (x + shift)

/-- If `|iteratedDeriv n smoothCutoff x| ≤ C` for all `x`, then
`|iteratedDeriv n (shiftedCutoff shift width) x| ≤ C / width ^ n` for `width > 0`, via
`iteratedDeriv_shiftedCutoff`. -/
lemma abs_iteratedDeriv_shiftedCutoff_le {n : ℕ} {C : ℝ}
    (hC : ∀ x, |iteratedDeriv n smoothCutoff x| ≤ C)
    (shift : ℝ) {width : ℝ} (hw : 0 < width) (x : ℝ) :
    |iteratedDeriv n (shiftedCutoff shift width) x| ≤ C / width ^ n := by
  rw [iteratedDeriv_shiftedCutoff, abs_mul, abs_pow, abs_inv, abs_of_pos hw]
  calc
    _ ≤ width⁻¹ ^ n * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
    _ = _ := by rw [inv_pow]; ring

/-- `shiftedCutoff shift width x ≥ 0`, inherited from `smoothCutoff_nonneg`. -/
lemma shiftedCutoff_nonneg (shift width x : ℝ) : 0 ≤ shiftedCutoff shift width x :=
  smoothCutoff_nonneg _

/-- `shiftedCutoff shift width x ≤ 1`, inherited from `smoothCutoff_le_one`. -/
lemma shiftedCutoff_le_one (shift width x : ℝ) : shiftedCutoff shift width x ≤ 1 :=
  smoothCutoff_le_one _

/-- If `smooth` approximates `value` within `error`, the cutoff value
`shiftedCutoff shift width smooth` is sandwiched between the indicator of
`value ≤ -shift - error` (below) and the indicator of `value ≤ width - shift + error`
(above), since the approximation error shifts `smooth` into the region where `smoothCutoff` is
exactly `1` or exactly `0`. -/
lemma shiftedCutoff_indicator_bounds {value smooth error shift width : ℝ}
    (hw : 0 < width) (happrox : |smooth - value| ≤ error) :
    (if value ≤ -shift - error then (1 : ℝ) else 0) ≤ shiftedCutoff shift width smooth ∧
      shiftedCutoff shift width smooth ≤ if value ≤ width - shift + error then (1 : ℝ) else 0 := by
  constructor
  · split_ifs with h
    · have hs : (smooth + shift) / width ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by
        have hh := (abs_le.mp happrox).2
        linarith) hw.le
      exact le_of_eq (smoothCutoff_eq_one hs).symm
    · exact shiftedCutoff_nonneg _ _ _
  · split_ifs with h
    · exact shiftedCutoff_le_one _ _ _
    · have hs : 1 ≤ (smooth + shift) / width := (le_div_iff₀ hw).mpr (by
        have hh := (abs_le.mp happrox).1
        linarith)
      exact le_of_eq (smoothCutoff_eq_zero hs)

/-- There is `C ≥ 1` such that for every `shift` and `width > 0`, the first three derivatives
of `shiftedCutoff shift width` are bounded by `C / width`, `C / width ^ 2`, and
`C / width ^ 3` respectively, combining `exists_smoothCutoff_derivative_bounds` with
`abs_iteratedDeriv_shiftedCutoff_le`. -/
lemma exists_shiftedCutoff_derivative_bounds : ∃ C ≥ (1 : ℝ), ∀ shift : ℝ, ∀ width > 0,
    (∀ x, |deriv (shiftedCutoff shift width) x| ≤ C / width) ∧
    (∀ x, |deriv (deriv (shiftedCutoff shift width)) x| ≤ C / width ^ 2) ∧
    (∀ x, |deriv (deriv (deriv (shiftedCutoff shift width))) x| ≤ C / width ^ 3) := by
  obtain ⟨C, hC, h1, h2, h3⟩ := exists_smoothCutoff_derivative_bounds
  refine ⟨C, hC, fun shift width hw => ⟨?_, ?_, ?_⟩⟩
  · intro x
    have h := abs_iteratedDeriv_shiftedCutoff_le (n := 1)
      (by simpa only [iteratedDeriv_one] using h1) shift hw x
    simpa only [iteratedDeriv_one, pow_one] using h
  · intro x
    have h := abs_iteratedDeriv_shiftedCutoff_le (n := 2)
      (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h2) shift hw x
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h
  · intro x
    have h := abs_iteratedDeriv_shiftedCutoff_le (n := 3)
      (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h3) shift hw x
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h

end Sandpile
