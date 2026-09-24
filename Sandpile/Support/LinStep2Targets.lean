/-
The choice of targets that makes the five errors of Step 2 add to less than a prescribed
`c` (`sandpile.tex:5571-5574`).

`Sandpile.integral_abs_survival_sub_profile_le_window` bounds the mean deviation along one
path by
`\eta(1+L)+\theta+Q+\kappa\eta'+\eta\kappa(\eta'+L)` with `L=\log(1/\varepsilon)` and
`Q=16(G(0,0)\kappa)^2/(\varepsilon n_R)`.  Four of the five tend to zero for free once the
targets are fixed; the arithmetic of fixing them is here, separated from the probability.

`error_sum_le_of_targets` is the addition, and the two existence lemmas are the choices:
`\eta=\min\{1,c/(5(1+L)(1+\kappa))\}` makes the first and the last term at most `c/5`
simultaneously, and `\eta'=\min\{1,c/(5\kappa)\}` makes the fourth at most `c/5`.  The
remaining two, `\theta\leq c/5` and `Q\leq c/5`, are conditions on `R` alone.
-/
import Sandpile.Support.LinStep2Profile

open MeasureTheory Filter Topology

namespace Sandpile

/-- **The five errors add to at most `c`** once each is at most `c/5`; the last one is
controlled through `\eta'\leq1`. -/
theorem error_sum_le_of_targets (kappa L c eta theta Q eta' : ℝ)
    (hkappa : 0 < kappa) (_hL : 0 ≤ L)
    (heta0 : 0 ≤ eta) (heta'1 : eta' ≤ 1)
    (h1 : eta * (1 + L) ≤ c / 5) (h2 : theta ≤ c / 5) (h3 : Q ≤ c / 5)
    (h4 : kappa * eta' ≤ c / 5) (h5 : eta * kappa * (1 + L) ≤ c / 5) :
    eta * (1 + L) + theta + Q + (kappa * eta' + eta * kappa * (eta' + L)) ≤ c := by
  have h6 : eta * kappa * (eta' + L) ≤ eta * kappa * (1 + L) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg heta0 hkappa.le)
  linarith

/-- The window target `\eta` that makes both terms it multiplies at most `c/5`. -/
theorem exists_eta_targets (kappa L c : ℝ) (hkappa : 0 < kappa) (hL : 0 ≤ L) (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ eta * (1 + L) ≤ c / 5 ∧ eta * kappa * (1 + L) ≤ c / 5 := by
  have hden : (0 : ℝ) < 5 * (1 + L) * (1 + kappa) := by positivity
  refine ⟨min 1 (c / (5 * (1 + L) * (1 + kappa))), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_, ?_⟩
  · have hm : min 1 (c / (5 * (1 + L) * (1 + kappa))) ≤ c / (5 * (1 + L) * (1 + kappa)) :=
      min_le_right _ _
    have h1L : (0 : ℝ) < 1 + L := by linarith
    have hstep : min 1 (c / (5 * (1 + L) * (1 + kappa))) * (1 + L)
        ≤ (c / (5 * (1 + L) * (1 + kappa))) * (1 + L) :=
      mul_le_mul_of_nonneg_right hm h1L.le
    have hval : (c / (5 * (1 + L) * (1 + kappa))) * (1 + L) = c / (5 * (1 + kappa)) := by
      field_simp
    rw [hval] at hstep
    have hcmp : c / (5 * (1 + kappa)) ≤ c / 5 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 5)]
      nlinarith [hc.le, hkappa.le]
    linarith
  · have hm : min 1 (c / (5 * (1 + L) * (1 + kappa))) ≤ c / (5 * (1 + L) * (1 + kappa)) :=
      min_le_right _ _
    have h1L : (0 : ℝ) < 1 + L := by linarith
    have hstep : min 1 (c / (5 * (1 + L) * (1 + kappa))) * kappa * (1 + L)
        ≤ (c / (5 * (1 + L) * (1 + kappa))) * kappa * (1 + L) := by
      have := mul_le_mul_of_nonneg_right hm hkappa.le
      exact mul_le_mul_of_nonneg_right this h1L.le
    have hval : (c / (5 * (1 + L) * (1 + kappa))) * kappa * (1 + L)
        = c * kappa / (5 * (1 + kappa)) := by
      field_simp
    rw [hval] at hstep
    have hcmp : c * kappa / (5 * (1 + kappa)) ≤ c / 5 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 5)]
      nlinarith [hc.le, hkappa.le]
    linarith

/-- The last-visit target `\eta'` that makes `\kappa\eta'` at most `c/5`. -/
theorem exists_etaPrime_target (kappa c : ℝ) (hkappa : 0 < kappa) (hc : 0 < c) :
    ∃ eta' : ℝ, 0 < eta' ∧ eta' ≤ 1 ∧ kappa * eta' ≤ c / 5 := by
  refine ⟨min 1 (c / (5 * kappa)), lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  have hm : min 1 (c / (5 * kappa)) ≤ c / (5 * kappa) := min_le_right _ _
  have hstep : kappa * min 1 (c / (5 * kappa)) ≤ kappa * (c / (5 * kappa)) :=
    mul_le_mul_of_nonneg_left hm hkappa.le
  have hval : kappa * (c / (5 * kappa)) = c / 5 := by
    field_simp
  linarith [hstep, hval.le, hval.ge]

end Sandpile
