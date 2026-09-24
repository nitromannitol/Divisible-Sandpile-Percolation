/-
Two pieces of Step 2 of `lem:dgt4-path-survival` that sit between the product over the last
visits and the deterministic chain already proved in `Support/LinProduct.lean`.

* The paper's exponent `I_{r,j}(X)` is real valued, and
  `Sandpile.abs_prod_pow_sub_rpow_le` runs the whole deterministic chain of Step 2
  (`\prod_r(1-\pi_r)^{I_r}` to `\exp\{-\sum_rI_r\pi_r\}` to the profile `x^\kappa`) with a
  NATURAL exponent.  `cast_lastVisit_if` and `prod_pow_lastVisit_if` are the bridge: for
  `r\leq j` the natural indicator of the last-visit times casts to `I_{r,j}(X)`, and the
  product with the natural exponent is the product over the last-visit times, which is what
  `Support/LinStep2Replace.lean` produces.
* `exists_tail_window_bounds` is `sandpile.tex:5518-5519`, "`\P(J(0)>b_x)\asymp R^{-2}`
  uniformly over `x\in\Lambda`": on the window `\lceil\varepsilon n_R\rceil\leq m\leq n_R`
  the relative bound of `eq:dgt4-uniform-contact-thresholds` turns into the two-sided bound
  `1/(KR^2)\leq\pi\leq K/R^2` with a single constant `K`, which is the hypothesis Step 1
  consumes (`Support/LinStep1Factor.lean`, `level_lower_bound_window`).  The constant is
  `\max\{1,4G(0,0)\kappa/(\varepsilon T),2T/(G(0,0)\kappa)\}` and is bound before `R`.
-/
import Sandpile.Support.LinStep2
import Sandpile.Support.LinStep2Replace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### The natural form of the last-visit exponent -/

theorem lastVisitTimes_subset (j : ℕ) (X : ℕ → Site d) :
    lastVisitTimes j X ⊆ Finset.range (j + 1) := by
  classical
  rw [lastVisitTimes]
  exact Finset.filter_subset _ _

/-- The natural-number form of the last-visit indicator, for times up to `j`. -/
theorem cast_lastVisit_if (j r : ℕ) (X : ℕ → Site d) (hr : r ∈ Finset.range (j + 1)) :
    (((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) : ℝ)
      = Frozen.DGT4LastVisits.lastVisitIndicator r j X := by
  classical
  by_cases h : r ∈ lastVisitTimes j X
  · rw [if_pos h, lastVisitIndicator_eq_one_of_mem X h, Nat.cast_one]
  · rw [if_neg h, lastVisitIndicator_eq_zero_of_notMem X hr h, Nat.cast_zero]

/-- The product over `0 ≤ r ≤ j` with the natural last-visit exponent is the product over the
last-visit times. -/
theorem prod_pow_lastVisit_if (j : ℕ) (X : ℕ → Site d) (f : ℕ → ℝ) :
    ∏ r ∈ Finset.range (j + 1),
        (f r) ^ (if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)
      = ∏ r ∈ lastVisitTimes j X, f r := by
  classical
  have h1 : ∏ r ∈ Finset.range (j + 1),
      (f r) ^ (if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)
      = ∏ r ∈ Finset.range (j + 1), (if r ∈ lastVisitTimes j X then f r else 1) := by
    refine Finset.prod_congr rfl fun r _ => ?_
    by_cases h : r ∈ lastVisitTimes j X
    · rw [if_pos h, if_pos h, pow_one]
    · rw [if_neg h, if_neg h, pow_zero]
  rw [h1, Finset.prod_ite_mem,
    Finset.inter_eq_right.mpr (lastVisitTimes_subset j X)]

/-! ### The two-sided tail bound on the window -/

/-- **The two-sided tail bound of Step 1's hypothesis.**  On the window
`⌈ε n_R⌉ ≤ m ≤ n_R` the relative bound of `eq:dgt4-uniform-contact-thresholds` gives
`\P(J(0)>b_x)\asymp R^{-2}` uniformly, which is `sandpile.tex:5513-5514`. -/
theorem exists_tail_window_bounds (T Gk eta eps : ℝ) (hT : 0 < T) (hGk : 0 < Gk)
    (_heta0 : 0 ≤ eta) (heta : eta ≤ 1 / 2) (heps : 0 < eps) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ R : ℝ in atTop, ∀ m : ℕ,
      ⌈eps * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
        ∀ pi : ℝ, |(m : ℝ) * pi / Gk - 1| ≤ eta →
          1 / (K * R ^ 2) ≤ pi ∧ pi ≤ K / R ^ 2 := by
  refine ⟨max 1 (max (4 * Gk / (eps * T)) (2 * T / Gk)), le_max_left _ _, ?_⟩
  set K : ℝ := max 1 (max (4 * Gk / (eps * T)) (2 * T / Gk)) with hK
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hKu : 4 * Gk / (eps * T) ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKl : 2 * T / Gk ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK1
  have hsq : Tendsto (fun R : ℝ => R ^ 2 * T) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).atTop_mul_const hT
  have hev2 : ∀ᶠ R : ℝ in atTop, (2 : ℝ) ≤ R ^ 2 * T := hsq.eventually_ge_atTop 2
  have hev3 : ∀ᶠ R : ℝ in atTop, (2 : ℝ) / eps ≤ R ^ 2 * T := hsq.eventually_ge_atTop (2 / eps)
  filter_upwards [hev2, hev3, eventually_gt_atTop (0 : ℝ)] with R h2 h3 hR0
  intro m hm1 hm2 pi hpi
  have hRT : (0 : ℝ) < R ^ 2 * T := by linarith
  have hfl : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le hRT.le
  have hfl' : R ^ 2 * T - 1 ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := le_of_lt (Nat.sub_one_lt_floor _)
  have hmlow : eps * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ (m : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hm1)
  have hhalf : R ^ 2 * T / 2 ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by linarith
  have hmlow2 : eps * (R ^ 2 * T / 2) ≤ (m : ℝ) := by nlinarith [hmlow, hhalf, heps.le]
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have h1 : (1 : ℝ) ≤ eps * (R ^ 2 * T / 2) := by
      rw [div_le_iff₀ heps] at h3
      nlinarith [h3, heps]
    linarith
  have hmnat : 0 < m := by exact_mod_cast hmpos
  have hmup : (m : ℝ) ≤ R ^ 2 * T := by
    have : ((m : ℕ) : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by exact_mod_cast hm2
    linarith
  have habs := abs_weight_sub_le m hmnat Gk eta pi hGk hpi
  rw [abs_le] at habs
  have hGm : (0 : ℝ) < Gk / (m : ℝ) := by positivity
  constructor
  · have hlow : Gk / (m : ℝ) - eta * (Gk / (m : ℝ)) ≤ pi := by linarith [habs.1]
    have hlow2 : Gk / (2 * (R ^ 2 * T)) ≤ pi := by
      have h1 : Gk / (R ^ 2 * T) ≤ Gk / (m : ℝ) := by
        apply div_le_div_of_nonneg_left hGk.le hmpos hmup
      have heq : Gk / (2 * (R ^ 2 * T)) = (Gk / (R ^ 2 * T)) / 2 := by ring
      rw [heq]
      have hprod : eta * (Gk / (m : ℝ)) ≤ (1 / 2) * (Gk / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right heta hGm.le
      linarith
    have h2b : 1 / (K * R ^ 2) ≤ Gk / (2 * (R ^ 2 * T)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hKT : 2 * T / Gk ≤ K := hKl
      rw [div_le_iff₀ hGk] at hKT
      nlinarith [hKT, sq_nonneg R, hR0]
    linarith
  · have hup : pi ≤ Gk / (m : ℝ) + eta * (Gk / (m : ℝ)) := by linarith [habs.2]
    have hup2 : pi ≤ 2 * Gk / (eps * (R ^ 2 * T / 2)) := by
      have h1 : Gk / (m : ℝ) ≤ Gk / (eps * (R ^ 2 * T / 2)) :=
        div_le_div_of_nonneg_left hGk.le (by nlinarith [heps, hRT]) hmlow2
      have heq2 : 2 * Gk / (eps * (R ^ 2 * T / 2)) = 2 * (Gk / (eps * (R ^ 2 * T / 2))) := by
        ring
      rw [heq2]
      have hA0 : (0 : ℝ) < Gk / (eps * (R ^ 2 * T / 2)) :=
        div_pos hGk (by nlinarith [heps, hRT])
      have hprod : eta * (Gk / (m : ℝ)) ≤ (1 / 2) * (Gk / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right heta hGm.le
      linarith
    have h2b : 2 * Gk / (eps * (R ^ 2 * T / 2)) ≤ K / R ^ 2 := by
      rw [div_le_div_iff₀ (by nlinarith [heps, hRT]) (by positivity)]
      have hKT : 4 * Gk / (eps * T) ≤ K := hKu
      rw [div_le_iff₀ (by positivity)] at hKT
      nlinarith [hKT, sq_nonneg R, hR0]
    linarith

end Sandpile
