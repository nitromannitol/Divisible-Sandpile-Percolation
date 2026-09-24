/-
**Step 3 of case (a), the pointwise comparison** (`sandpile.tex:5201-5237`).

At the conditioned level `-V_\infty(0)=a+\Sigma^2y/a` the paper reads the reflected
increment `-\zeta(0)-Pu_n(0)` off two facts already in the repository: the identity
`eq:dgt4-gaussian-reflected-expression`

  `-\zeta(0)-Pu_n(0)=(-V_\infty(0)-a)+P(V_\infty-u_n+a)(0)`

(`neg_scenery_sub_avg_odometer_eq`), and the stopping comparison
`eq:dgt4-gaussian-stopping-comparison`

  `|P(V_\infty-u_n+a)(0)+\P_0(\tau_0^+\leq k)\,(-(V_\infty(0)+a))_+|\leq P^{k+1}|V_\infty-u_{n-k}+a|(0)`

(`abs_avg_infiniteGreenField_stop_compare`), valid at every residual where the payoff
`V_\infty+a` is nonnegative on the punctured box of radius `k+1`.  Since the level fixes
`-(V_\infty(0)+a)=\Sigma^2y/a`, multiplying by `a/\Sigma^2` turns the two into

  `|\frac{a}{\Sigma^2}(-\zeta(0)-Pu_n(0))-(y-\P_0(\tau_0^+\leq k)\max(y,0))|
     \leq\frac{a}{\Sigma^2}P^{k+1}|V_\infty-u_{n-k}+a|(0)` ,

which is the whole of Step 3 in one inequality: the left term is what Step 4 integrates,
the middle term tends to `y-(1-G(0,0)^{-1})\max(y,0)` by `tendsto_avg_srwHitBy`, and the
right term tends to zero in conditional mean by Step 2.

Terminal domination (`eq:dgt4-gaussian-terminal-domination`) gives the companion one-sided
bound with no hypothesis on the payoff at all, which is what dominates the integrand of
Step 4.
-/
import Sandpile.Support.Dgt4ATerminalDom
import Sandpile.Support.Dgt4AConcBound

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The reflected increment `-\zeta(0)-Pu_t(0)` at the conditioned level, as a function of
the residual. -/
noncomputable def condReflected (d : ℕ) (hd : 5 ≤ d) (c s : ℝ) (t : ℕ)
    (r : Site d → ℝ) : ℝ :=
  -(condScenery d hd c r s) 0 - avg (odometerOf (condScenery d hd c r s) t) 0

theorem measurable_condReflected (hd : 5 ≤ d) (c s : ℝ) (t : ℕ) :
    Measurable (condReflected d hd c s t) := by
  have hcs : Measurable (fun r : Site d → ℝ => condScenery d hd c r s) :=
    measurable_condScenery hd c s
  have h1 : Measurable (fun r : Site d → ℝ => -(condScenery d hd c r s) 0) :=
    (((measurable_pi_apply (0 : Site d)).comp hcs)).neg
  have h2 : Measurable
      (fun r : Site d → ℝ => avg (odometerOf (condScenery d hd c r s) t) 0) := by
    unfold avg LatticeProb.walkOp
    exact (Finset.measurable_sum _ fun i _ =>
      (((measurable_odometerOf t _).comp hcs)).add
        (((measurable_odometerOf t _).comp hcs))).div_const _
  exact h1.sub h2

/-- **The pointwise form of Step 3** (`sandpile.tex:5196-5232`). -/
theorem abs_condReflected_sub_le (hd : 5 ≤ d) (c s a S y : ℝ) (hS : 0 < S) (ha : 0 < a)
    (k m : ℕ) (r : Site d → ℝ) (hr : r ∈ condConv d hd c s)
    (hlevel : infiniteGreenField (condScenery d hd c r s) 0 = -(a + S * y / a))
    (hgood : ∀ z : Site d, z ≠ 0 → boxDist z 0 ≤ k + 1 →
      0 ≤ infiniteGreenField (condScenery d hd c r s) z + a) :
    |a / S * condReflected d hd c s (m + k) r
        - (y - avg (LatticeProb.srwHitBy d k) 0 * max y 0)|
      ≤ a / S * condTerminal d hd c s a m (k + 1) r := by
  have hd3 : 3 ≤ d := by omega
  have hconv : ∀ w : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n (condScenery d hd c r s) w) atTop (𝓝 L) :=
    fun w => hr w
  have hane : a ≠ 0 := ne_of_gt ha
  have hSne : S ≠ 0 := ne_of_gt hS
  have haS : (0:ℝ) < a / S := div_pos ha hS
  have hSa : (0:ℝ) ≤ S / a := le_of_lt (div_pos hS ha)
  have heq := neg_scenery_sub_avg_odometer_eq hd3 (condScenery d hd c r s) hconv a (m + k)
  have hcmp := abs_avg_infiniteGreenField_stop_compare hd3 (condScenery d hd c r s) hconv a k
    hgood m
  have hmax : max (-(infiniteGreenField (condScenery d hd c r s) 0 + a)) 0 = S / a * max y 0 := by
    rw [mul_max_of_nonneg y 0 hSa, hlevel]
    congr 1
    · field_simp
      ring
    · ring
  rw [hmax] at hcmp
  have hT : (avg^[k + 1] (fun w => |infiniteGreenField (condScenery d hd c r s) w
      - odometerOf (condScenery d hd c r s) m w + a|)) 0
      = condTerminal d hd c s a m (k + 1) r := rfl
  rw [hT] at hcmp
  have hkey : |a / S * (avg (fun w => infiniteGreenField (condScenery d hd c r s) w
        - odometerOf (condScenery d hd c r s) (m + k) w + a) 0
      + avg (LatticeProb.srwHitBy d k) 0 * (S / a * max y 0))|
      ≤ a / S * condTerminal d hd c s a m (k + 1) r := by
    rw [abs_mul, abs_of_pos haS]
    exact mul_le_mul_of_nonneg_left hcmp haS.le
  have hgoalEq : a / S * condReflected d hd c s (m + k) r
      - (y - avg (LatticeProb.srwHitBy d k) 0 * max y 0)
      = a / S * (avg (fun w => infiniteGreenField (condScenery d hd c r s) w
          - odometerOf (condScenery d hd c r s) (m + k) w + a) 0
        + avg (LatticeProb.srwHitBy d k) 0 * (S / a * max y 0)) := by
    rw [condReflected, heq, hlevel]
    field_simp
    ring
  rw [hgoalEq]
  exact hkey

/-- `condTerminal` is nonnegative: it dominates `|\Theta_n|`. -/
theorem condTerminal_nonneg (hd : 5 ≤ d) (c s a : ℝ) (t j : ℕ) (r : Site d → ℝ) :
    0 ≤ condTerminal d hd c s a t j r :=
  le_trans (abs_nonneg _) (abs_condTheta_le_condTerminal hd c s a t j r)

/-- **Terminal domination in its signed form** (`eq:dgt4-gaussian-terminal-domination`,
`sandpile.tex:5236-5240`): at the conditioned level the reflected increment is at most
`\Sigma^2y/\E u_n(0)` plus `\Theta_n`. -/
theorem condReflected_le (hd : 5 ≤ d) (c s a S y : ℝ)
    (k n : ℕ) (hk : k ≤ n) (r : Site d → ℝ) (hr : r ∈ condConv d hd c s)
    (hlevel : infiniteGreenField (condScenery d hd c r s) 0 = -(a + S * y / a)) :
    condReflected d hd c s n r
      ≤ S * y / a + condTheta d hd c s a (n - k) (k + 1) r := by
  have hd3 : 3 ≤ d := by omega
  have hconv : ∀ w : Site d, ∃ L : ℝ,
      Tendsto (fun m => infiniteGreenFieldPartial m (condScenery d hd c r s) w) atTop (𝓝 L) :=
    fun w => hr w
  have hdom := neg_scenery_sub_avg_odometer_le hd3 (condScenery d hd c r s) hconv a k n hk
  have hTh : (avg^[k + 1] (fun w => infiniteGreenField (condScenery d hd c r s) w
      - odometerOf (condScenery d hd c r s) (n - k) w + a)) 0
      = condTheta d hd c s a (n - k) (k + 1) r := rfl
  rw [hTh, hlevel] at hdom
  have hstep : -(-(a + S * y / a)) - a + condTheta d hd c s a (n - k) (k + 1) r
      = S * y / a + condTheta d hd c s a (n - k) (k + 1) r := by ring
  rw [hstep] at hdom
  exact hdom

/-- **The contact event forces the terminal quantity above `|y|`** (`sandpile.tex:5273-5274`):
for a level `y<0`, `\{u_{n+1}(0)=0\}` sits inside `\{\Theta_n\geq\Sigma^2|y|/\E u_n(0)\}`. -/
theorem le_condTheta_of_condReflected_pos (hd : 5 ≤ d) (c s a S y : ℝ)
    (k n : ℕ) (hk : k ≤ n) (r : Site d → ℝ) (hr : r ∈ condConv d hd c s)
    (hlevel : infiniteGreenField (condScenery d hd c r s) 0 = -(a + S * y / a))
    (hpos : 0 < condReflected d hd c s n r) :
    S * (-y) / a ≤ condTheta d hd c s a (n - k) (k + 1) r := by
  have h := condReflected_le hd c s a S y k n hk r hr hlevel
  have hid : S * (-y) / a = -(S * y / a) := by ring
  rw [hid]
  linarith

/-- **Terminal domination at the conditioned level** (`eq:dgt4-gaussian-terminal-domination`,
`sandpile.tex:5236-5240`), scaled: the positive part of the reflected increment is at most
`|y|` plus the terminal quantity, with no hypothesis on the payoff. -/
theorem condReflected_pos_le (hd : 5 ≤ d) (c s a S y : ℝ) (hS : 0 < S) (ha : 0 < a)
    (k n : ℕ) (hk : k ≤ n) (r : Site d → ℝ) (hr : r ∈ condConv d hd c s)
    (hlevel : infiniteGreenField (condScenery d hd c r s) 0 = -(a + S * y / a)) :
    a / S * max (condReflected d hd c s n r) 0
      ≤ |y| + a / S * condTerminal d hd c s a (n - k) (k + 1) r := by
  have hd3 : 3 ≤ d := by omega
  have hconv : ∀ w : Site d, ∃ L : ℝ,
      Tendsto (fun m => infiniteGreenFieldPartial m (condScenery d hd c r s) w) atTop (𝓝 L) :=
    fun w => hr w
  have hane : a ≠ 0 := ne_of_gt ha
  have hSne : S ≠ 0 := ne_of_gt hS
  have haS : (0:ℝ) < a / S := div_pos ha hS
  have hdom := neg_scenery_sub_avg_odometer_le hd3 (condScenery d hd c r s) hconv a k n hk
  have hTh : (avg^[k + 1] (fun w => infiniteGreenField (condScenery d hd c r s) w
      - odometerOf (condScenery d hd c r s) (n - k) w + a)) 0
      = condTheta d hd c s a (n - k) (k + 1) r := rfl
  rw [hTh, hlevel] at hdom
  have habs := abs_condTheta_le_condTerminal hd c s a (n - k) (k + 1) r
  have hTnn := condTerminal_nonneg hd c s a (n - k) (k + 1) r
  have hle1 : condTheta d hd c s a (n - k) (k + 1) r
      ≤ condTerminal d hd c s a (n - k) (k + 1) r :=
    le_trans (le_abs_self _) habs
  have hX : condReflected d hd c s n r ≤ S * y / a
      + condTerminal d hd c s a (n - k) (k + 1) r := by
    have : condReflected d hd c s n r
        = -condScenery d hd c r s 0 - avg (odometerOf (condScenery d hd c r s) n) 0 := rfl
    rw [this]
    have hstep : -(-(a + S * y / a)) - a + condTheta d hd c s a (n - k) (k + 1) r
        = S * y / a + condTheta d hd c s a (n - k) (k + 1) r := by ring
    rw [hstep] at hdom
    linarith
  have hscale : a / S * condReflected d hd c s n r
      ≤ y + a / S * condTerminal d hd c s a (n - k) (k + 1) r := by
    have h := mul_le_mul_of_nonneg_left hX haS.le
    have hy : a / S * (S * y / a) = y := by field_simp
    calc a / S * condReflected d hd c s n r
        ≤ a / S * (S * y / a + condTerminal d hd c s a (n - k) (k + 1) r) := h
      _ = y + a / S * condTerminal d hd c s a (n - k) (k + 1) r := by
          rw [mul_add, hy]
  have hyle : y ≤ |y| := le_abs_self y
  have hTpos : (0:ℝ) ≤ a / S * condTerminal d hd c s a (n - k) (k + 1) r :=
    mul_nonneg haS.le hTnn
  rw [mul_max_of_nonneg _ _ haS.le, mul_zero]
  exact max_le (by linarith) (by linarith [abs_nonneg y])

end Sandpile
