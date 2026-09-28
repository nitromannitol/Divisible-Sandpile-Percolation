import Mathlib

/-!
# Second Moment of the Reflection Window

The second moment of the reflection window in dimension four, the second half of
Step 3 of `prop:d4-superdiffusive-limit` (`sandpile.tex:3395-3404`).

The paper splits `E S_R(0)²` at the level `A₀ log(t+2)`, bounding the part below
the level by the mean and the part above it by `lem:d4-difference-tail`. Because
that lemma is available here in exponential-moment form, the whole split is a
POINTWISE inequality and needs no layer cake: with `0 ≤ S ≤ X`, `L ≥ 0`, `c > 0`
and `Y := (X − L)_+`,

  `S² ≤ L S + (8/c² + 2L²) 1_{L < X} + (8/c²)(e^{cY} − 1)` .

Below the level `S² ≤ L S`; above it `S² ≤ X² = (Y+L)² ≤ 2Y² + 2L²`, and
`Y² ≤ (4/c²) e^{cY}` because `(cY/2 + 1)² ≤ e^{cY/2·2}`. Integrating turns the
three terms into the window mean, the probability of exceeding the level, and
the exponential moment of `lem:d4-difference-tail`.
-/

open MeasureTheory Real

namespace Sandpile

/-- **The pointwise split behind Step 3's second moment.** -/
theorem window_sq_pointwise (c : ℝ) (hc : 0 < c) (L : ℝ) (hL : 0 ≤ L) (S X : ℝ)
    (hS : 0 ≤ S) (hSX : S ≤ X) :
    S ^ 2 ≤ L * S + (8 / c ^ 2 + 2 * L ^ 2) * (if L < X then (1 : ℝ) else 0)
      + (8 / c ^ 2) * (Real.exp (c * max 0 (X - L)) - 1) := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  by_cases h : L < X
  · rw [if_pos h, mul_one]
    set Y : ℝ := max 0 (X - L) with hYdef
    have hY : (0 : ℝ) ≤ Y := le_max_left _ _
    have hYX : X = Y + L := by
      rw [hYdef, max_eq_right (by linarith : (0 : ℝ) ≤ X - L)]; ring
    have hexp1 : (1 : ℝ) ≤ Real.exp (c * Y) := Real.one_le_exp (by positivity)
    have hhalf : c * Y / 2 + 1 ≤ Real.exp (c * Y / 2) := Real.add_one_le_exp _
    have hsplit : Real.exp (c * Y) = Real.exp (c * Y / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have hsq : Y ^ 2 ≤ 4 / c ^ 2 * Real.exp (c * Y) := by
      have h1 : (c * Y / 2 + 1) ^ 2 ≤ Real.exp (c * Y / 2) ^ 2 := by
        have h0 : (0 : ℝ) ≤ c * Y / 2 + 1 := by positivity
        exact pow_le_pow_left₀ h0 hhalf 2
      rw [hsplit, show (4 : ℝ) / c ^ 2 * Real.exp (c * Y / 2) ^ 2
          = 4 * Real.exp (c * Y / 2) ^ 2 / c ^ 2 by ring, le_div_iff₀ hc2]
      nlinarith [h1, hY, hc]
    by_cases hSL : S ≤ L
    · have h8 : (0 : ℝ) ≤ 8 / c ^ 2 := by positivity
      nlinarith [hexp1, hS, hL, h8, sq_nonneg L]
    · have hSX2 : S ^ 2 ≤ X ^ 2 := by nlinarith
      have h8 : (0 : ℝ) ≤ 8 / c ^ 2 := by positivity
      have hkey : 2 * Y ^ 2 ≤ 8 / c ^ 2 * Real.exp (c * Y) := by
        rw [show (8 : ℝ) / c ^ 2 = 2 * (4 / c ^ 2) by ring]
        nlinarith [hsq]
      have hX2 : X ^ 2 ≤ 2 * Y ^ 2 + 2 * L ^ 2 := by
        rw [hYX]; nlinarith [sq_nonneg (Y - L)]
      have hLS : (0 : ℝ) ≤ L * S := mul_nonneg hL hS
      linarith [hSX2, hX2, hkey, hLS]
  · rw [if_neg h]
    have hXL : X ≤ L := not_lt.mp h
    have hmax : max 0 (X - L) = 0 := max_eq_left (by linarith)
    rw [hmax]
    simp only [mul_zero, Real.exp_zero, sub_self, mul_zero, add_zero]
    nlinarith [hS, hSX, hXL]

/-- **Step 3's second moment, integrated.**  The three terms on the right are the
window mean, the probability that `X` exceeds the level, and the exponential
moment of `lem:d4-difference-tail`. -/
theorem window_second_moment_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (c : ℝ) (hc : 0 < c) (L : ℝ) (hL : 0 ≤ L) (S X : Ω → ℝ)
    (hS : ∀ ω, 0 ≤ S ω) (hSX : ∀ ω, S ω ≤ X ω)
    (hSi : Integrable S μ) (hSsq : Integrable (fun ω => S ω ^ 2) μ)
    (hmeas : MeasurableSet {ω | L < X ω})
    (hEi : Integrable (fun ω => Real.exp (c * max 0 (X ω - L)) - 1) μ) :
    (∫ ω, S ω ^ 2 ∂μ) ≤ L * (∫ ω, S ω ∂μ)
      + (8 / c ^ 2 + 2 * L ^ 2) * μ.real {ω | L < X ω}
      + (8 / c ^ 2) * ∫ ω, (Real.exp (c * max 0 (X ω - L)) - 1) ∂μ := by
  classical
  set I : Ω → ℝ := Set.indicator {ω | L < X ω} (fun _ => (1 : ℝ)) with hIdef
  have hIi : Integrable I μ := (integrable_const (1 : ℝ)).indicator hmeas
  have hbound : ∀ ω, S ω ^ 2 ≤ L * S ω + (8 / c ^ 2 + 2 * L ^ 2) * I ω
      + (8 / c ^ 2) * (Real.exp (c * max 0 (X ω - L)) - 1) := by
    intro ω
    have h := window_sq_pointwise c hc L hL (S ω) (X ω) (hS ω) (hSX ω)
    simpa [hIdef, Set.indicator_apply, Set.mem_setOf_eq] using h
  have hLS : Integrable (fun ω => L * S ω) μ := hSi.const_mul L
  have hII : Integrable (fun ω => (8 / c ^ 2 + 2 * L ^ 2) * I ω) μ := hIi.const_mul _
  have hEE : Integrable
      (fun ω => (8 / c ^ 2) * (Real.exp (c * max 0 (X ω - L)) - 1)) μ := hEi.const_mul _
  have hsum1 : Integrable (fun ω => L * S ω + (8 / c ^ 2 + 2 * L ^ 2) * I ω) μ := hLS.add hII
  have hsum2 : Integrable (fun ω => L * S ω + (8 / c ^ 2 + 2 * L ^ 2) * I ω
      + (8 / c ^ 2) * (Real.exp (c * max 0 (X ω - L)) - 1)) μ := hsum1.add hEE
  have hmono := integral_mono hSsq hsum2 hbound
  rw [integral_add hsum1 hEE, integral_add hLS hII, integral_const_mul,
    integral_const_mul, integral_const_mul, hIdef, integral_indicator_const _ hmeas,
    smul_eq_mul, mul_one] at hmono
  exact hmono

end Sandpile
