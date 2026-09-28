import Mathlib

/-!
# Uniform tail bounds for the truncation at a level

The truncation `y ↦ 0 ∨ (y ∧ M)` at a level `M`, and the two uniform tail bounds it obeys under
an exponential moment: for a nonnegative `X`, `E[X - (X ∧ M)] ≤ M e^{-θM} E e^{θX}` when
`θM ≥ 1`, and `E[X² - (X ∧ M)²] ≤ M² e^{-θM} E e^{θX}` when `θM ≥ 2`. A uniform exponential
moment therefore makes the families `{X}` and `{X²}` uniformly integrable, with both moduli
tending to zero as `M → ∞` uniformly over any family whose exponential moments are bounded by
one constant.
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

/-- The truncation `y ↦ 0 ∨ (y ∧ M)`, as a bounded continuous function. -/
noncomputable def truncBdd (M : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => max 0 (min y M), by fun_prop⟩ |M| (by
      intro x y
      have hx0 : (0:ℝ) ≤ max 0 (min x M) := le_max_left _ _
      have hy0 : (0:ℝ) ≤ max 0 (min y M) := le_max_left _ _
      have hMa : M ≤ |M| := le_abs_self M
      have hxM : max 0 (min x M) ≤ |M| := max_le (abs_nonneg M) ((min_le_right _ _).trans hMa)
      have hyM : max 0 (min y M) ≤ |M| := max_le (abs_nonneg M) ((min_le_right _ _).trans hMa)
      simp only [ContinuousMap.coe_mk]
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith)

/-- `truncBdd M` evaluates to the truncation `max 0 (min y M)`. -/
@[simp] theorem truncBdd_apply (M : ℝ) (y : ℝ) :
    truncBdd M y = max 0 (min y M) := rfl

/-- For `θ > 0` and `1 ≤ θ * M`, every `x > M` satisfies `x ≤ M * exp (θ * (x - M))`. -/
theorem le_mul_exp_of_gt (θ M x : ℝ) (hθ : 0 < θ) (hM : 1 ≤ θ * M) (hx : M < x) :
    x ≤ M * Real.exp (θ * (x - M)) := by
  have hM0 : 0 < M := by nlinarith
  have hu : 0 < x - M := by linarith
  have hexp : 1 + θ * (x - M) ≤ Real.exp (θ * (x - M)) := by
    have := Real.add_one_le_exp (θ * (x - M))
    linarith
  have hstep : M * (1 + θ * (x - M)) ≤ M * Real.exp (θ * (x - M)) :=
    mul_le_mul_of_nonneg_left hexp (le_of_lt hM0)
  nlinarith [hstep, hu, hM]

/-- For `θ > 0` and `2 ≤ θ * M`, every `x > M` satisfies `x² ≤ M² * exp (θ * (x - M))`. -/
theorem sq_le_mul_exp_of_gt (θ M x : ℝ) (hθ : 0 < θ) (hM : 2 ≤ θ * M) (hx : M < x) :
    x ^ 2 ≤ M ^ 2 * Real.exp (θ * (x - M)) := by
  have hM0 : 0 < M := by nlinarith
  have hu : 0 < x - M := by linarith
  have hexp : 1 + θ * (x - M) + (θ * (x - M)) ^ 2 / 4 ≤ Real.exp (θ * (x - M)) := by
    have h1 : 1 + θ * (x - M) / 2 ≤ Real.exp (θ * (x - M) / 2) := by
      linarith [Real.add_one_le_exp (θ * (x - M) / 2)]
    have h2 : Real.exp (θ * (x - M)) = Real.exp (θ * (x - M) / 2) ^ 2 := by
      rw [show θ * (x - M) = θ * (x - M) / 2 + θ * (x - M) / 2 by ring]
      rw [Real.exp_add]
      ring
    have hE : 0 < Real.exp (θ * (x - M) / 2) := Real.exp_pos _
    have hpos : 0 < 1 + θ * (x - M) / 2 := by nlinarith [hθ, hu]
    have hprod : 0 ≤ (Real.exp (θ * (x - M) / 2) - (1 + θ * (x - M) / 2)) *
        (Real.exp (θ * (x - M) / 2) + (1 + θ * (x - M) / 2)) := by
      apply mul_nonneg
      · linarith
      · linarith
    nlinarith [h2, hprod]
  have hstep : M ^ 2 * (1 + θ * (x - M) + (θ * (x - M)) ^ 2 / 4)
      ≤ M ^ 2 * Real.exp (θ * (x - M)) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  have h4 : 4 ≤ θ ^ 2 * M ^ 2 := by
    have h : 0 ≤ (θ * M - 2) * (θ * M + 2) := by
      apply mul_nonneg <;> linarith
    nlinarith [h]
  have hA : 2 * M * (x - M) ≤ M ^ 2 * θ * (x - M) := by
    have h : 0 ≤ (θ * M - 2) * (M * (x - M)) := by
      apply mul_nonneg
      · linarith
      · exact mul_nonneg (le_of_lt hM0) (le_of_lt hu)
    nlinarith [h]
  have hB : (x - M) ^ 2 ≤ M ^ 2 * θ ^ 2 * (x - M) ^ 2 / 4 := by
    have h : 0 ≤ (θ ^ 2 * M ^ 2 - 4) * ((x - M) ^ 2 / 4) := by
      apply mul_nonneg
      · nlinarith [h4]
      · positivity
    nlinarith [h]
  nlinarith [hstep, hA, hB, hu, hM, sq_nonneg (x - M), sq_nonneg M]

/-- The first-moment tail bound, pointwise: for `0 ≤ y` and `1 ≤ θM`,
`y - (0 ∨ (y ∧ M)) ≤ M e^{-θM} e^{θy}`. -/
theorem sub_trunc_le (θ M y : ℝ) (hθ : 0 < θ) (hM : 1 ≤ θ * M) (hy : 0 ≤ y) :
    y - max 0 (min y M) ≤ M * Real.exp (-(θ * M)) * Real.exp (θ * y) := by
  have hM0 : 0 < M := by nlinarith
  rcases le_or_gt y M with h | h
  · have : max 0 (min y M) = y := by
      rw [min_eq_left h, max_eq_right hy]
    rw [this, sub_self]
    positivity
  · have hmin : min y M = M := min_eq_right (le_of_lt h)
    have hmax : max 0 (min y M) = M := by rw [hmin, max_eq_right (le_of_lt hM0)]
    rw [hmax]
    have hkey := le_mul_exp_of_gt θ M y hθ hM h
    have hrw : M * Real.exp (-(θ * M)) * Real.exp (θ * y) = M * Real.exp (θ * (y - M)) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
    rw [hrw]
    linarith

/-- The second-moment tail bound, pointwise: for `0 ≤ y` and `2 ≤ θM`,
`y² - (0 ∨ (y ∧ M))² ≤ M² e^{-θM} e^{θy}`. -/
theorem sq_sub_trunc_sq_le (θ M y : ℝ) (hθ : 0 < θ) (hM : 2 ≤ θ * M) (hy : 0 ≤ y) :
    y ^ 2 - (max 0 (min y M)) ^ 2 ≤ M ^ 2 * Real.exp (-(θ * M)) * Real.exp (θ * y) := by
  have hM0 : 0 < M := by nlinarith
  rcases le_or_gt y M with h | h
  · have : max 0 (min y M) = y := by
      rw [min_eq_left h, max_eq_right hy]
    rw [this, sub_self]
    positivity
  · have hmin : min y M = M := min_eq_right (le_of_lt h)
    have hmax : max 0 (min y M) = M := by rw [hmin, max_eq_right (le_of_lt hM0)]
    rw [hmax]
    have hkey := sq_le_mul_exp_of_gt θ M y hθ hM h
    have hrw : M ^ 2 * Real.exp (-(θ * M)) * Real.exp (θ * y)
        = M ^ 2 * Real.exp (θ * (y - M)) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
    rw [hrw]
    nlinarith [sq_nonneg M]

/-- The truncation never exceeds the value, on the nonnegative half-line. -/
theorem trunc_le_self (M y : ℝ) (hy : 0 ≤ y) : max 0 (min y M) ≤ y :=
  max_le hy (min_le_left _ _)

/-- The squared truncation never exceeds the square, on the nonnegative half-line. -/
theorem trunc_sq_le_sq (M y : ℝ) (hy : 0 ≤ y) :
    (max 0 (min y M)) ^ 2 ≤ y ^ 2 :=
  pow_le_pow_left₀ (le_max_left _ _) (trunc_le_self M y hy) 2


/-- The squared truncation `y ↦ (0 ∨ (y ∧ M))²`, as a bounded continuous function. -/
noncomputable def truncSqBdd (M : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => (max 0 (min y M)) ^ 2, by fun_prop⟩ (M ^ 2) (by
      intro x y
      have hx0 : (0:ℝ) ≤ max 0 (min x M) := le_max_left _ _
      have hy0 : (0:ℝ) ≤ max 0 (min y M) := le_max_left _ _
      have hMa : M ≤ |M| := le_abs_self M
      have hxM : max 0 (min x M) ≤ |M| := max_le (abs_nonneg M) ((min_le_right _ _).trans hMa)
      have hyM : max 0 (min y M) ≤ |M| := max_le (abs_nonneg M) ((min_le_right _ _).trans hMa)
      have hsq : |M| ^ 2 = M ^ 2 := sq_abs M
      simp only [ContinuousMap.coe_mk]
      rw [Real.dist_eq, abs_le]
      constructor <;> nlinarith)

/-- `truncSqBdd M` evaluates to the squared truncation `(max 0 (min y M)) ^ 2`. -/
@[simp] theorem truncSqBdd_apply (M : ℝ) (y : ℝ) :
    truncSqBdd M y = (max 0 (min y M)) ^ 2 := rfl

end Sandpile.Support
