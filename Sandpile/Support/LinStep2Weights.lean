import Sandpile.Support.LinStep3Product

/-!
# The weights of Step 2 of the path-survival lemma, integrated along one path

The last-visit exponent is carried as the membership indicator of `lastVisitTimes`, which
agrees with the indicator `visitInd` that the weighted-last-visits lemma is stated through, so
the weighted last-visit sum `∑_{r≤j} I_{r,j}(X)/(n-r)` is exactly `lvSum n j X`. The weight
substitution `π_{R,r} = G(0,0)κ/(n_R-r)·(1+o_R(1))` is used in two forms: an upper bound
`π_{R,r} ≤ 2G(0,0)κ/(n_R-r)`, which gives a bound `∑_r π_{R,r}² ≤ C(ε)/n_R` on the square sum
of the weights, and a relative bound, which gives the deviation of the exact weighted sum from
`κ G(0,0) · lvSum n j X`. Combining both with a threshold-replacement error, a factorization
error, and the integral bound supplied by the weighted-last-visits lemma produces Step 2 of the
path-survival lemma along one path, integrated over the walk, with every error term named.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The membership indicator of the last-visit times is `Sandpile.visitInd`. -/
theorem cast_lastVisit_eq_visitInd (j r : ℕ) (X : ℕ → Site d)
    (hr : r ∈ Finset.range (j + 1)) :
    (((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) : ℝ) = visitInd r (j - r) X := by
  rw [cast_lastVisit_if j r X hr, Frozen.DGT4LastVisits.lastVisitIndicator_eq_visitInd]

/-- The paper's weighted last-visit sum `\sum_{r\leq j}I_{r,j}(X)/(n-r)` is
`Sandpile.lvSum`. -/
theorem sum_lastVisit_wcoef_eq_lvSum (n j : ℕ) (X : ℕ → Site d) :
    ∑ r ∈ Finset.range (j + 1),
        (((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) : ℝ) * (1 / ((n : ℝ) - (r : ℝ)))
      = lvSum n j X := by
  simp only [lvSum, wcoef]
  exact Finset.sum_congr rfl fun r hr => by rw [cast_lastVisit_eq_visitInd j r X hr]

/-- **`\sum_r I_{r,j}(X)\pi_{R,r}^2\leq C(\varepsilon)/n_R`** (`sandpile.tex:5557`), from the
uniform upper bound on the weights. -/
theorem sum_lastVisit_sq_le (n j : ℕ) (hj : j < n) (X : ℕ → Site d) (pi : ℕ → ℝ) (Gk : ℝ)
    (_hGk : 0 ≤ Gk)
    (hpi0 : ∀ r ∈ Finset.range (j + 1), 0 ≤ pi r)
    (hpiu : ∀ r ∈ Finset.range (j + 1), pi r ≤ 2 * Gk / ((n - r : ℕ) : ℝ)) :
    (∑ r ∈ Finset.range (j + 1),
        (((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) : ℝ) * pi r ^ 2)
      ≤ (2 * Gk) ^ 2 * (2 / ((n - j : ℕ) : ℝ)) := by
  classical
  have hterm : ∀ r ∈ Finset.range (j + 1),
      (((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) : ℝ) * pi r ^ 2
        ≤ (2 * Gk) ^ 2 * (((n - r : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro r hr
    have hI : (((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) : ℝ) ≤ 1 := by
      by_cases h : r ∈ lastVisitTimes j X
      · rw [if_pos h]; norm_num
      · rw [if_neg h]; norm_num
    have hI0 : 0 ≤ (((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) : ℝ) := by positivity
    have hsq : pi r ^ 2 ≤ (2 * Gk) ^ 2 * (((n - r : ℕ) : ℝ) ^ 2)⁻¹ := by
      have hnr : (0 : ℝ) < ((n - r : ℕ) : ℝ) := by
        have : 0 < n - r := by
          have := Finset.mem_range.mp hr
          omega
        exact_mod_cast this
      have h1 := hpi0 r hr
      have h2 := hpiu r hr
      have hkey : pi r ^ 2 ≤ (2 * Gk / ((n - r : ℕ) : ℝ)) ^ 2 := by nlinarith [h1, h2]
      calc pi r ^ 2 ≤ (2 * Gk / ((n - r : ℕ) : ℝ)) ^ 2 := hkey
        _ = (2 * Gk) ^ 2 * (((n - r : ℕ) : ℝ) ^ 2)⁻¹ := by
            rw [div_pow]
            field_simp
    calc (((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) : ℝ) * pi r ^ 2
        ≤ 1 * pi r ^ 2 := mul_le_mul_of_nonneg_right hI (sq_nonneg _)
      _ = pi r ^ 2 := one_mul _
      _ ≤ (2 * Gk) ^ 2 * (((n - r : ℕ) : ℝ) ^ 2)⁻¹ := hsq
  calc (∑ r ∈ Finset.range (j + 1),
        (((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) : ℝ) * pi r ^ 2)
      ≤ ∑ r ∈ Finset.range (j + 1), (2 * Gk) ^ 2 * (((n - r : ℕ) : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum hterm
    _ = (2 * Gk) ^ 2 * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (2 * Gk) ^ 2 * (2 / ((n - j : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_range_le n j hj) (by positivity)

/-- **The weighted sum against `\kappa G(0,0)S(X)`** (`sandpile.tex:5558-5560`): a relative
error `ε` in each weight is a relative error `ε` in the weighted sum. -/
theorem abs_sum_lastVisit_sub_le (n j : ℕ) (X : ℕ → Site d) (pi : ℕ → ℝ)
    (kappa G eps : ℝ)
    (hpi : ∀ r ∈ Finset.range (j + 1),
      |pi r - (kappa * G) * (1 / ((n : ℝ) - (r : ℝ)))|
        ≤ eps * ((kappa * G) * (1 / ((n : ℝ) - (r : ℝ))))) :
    |(∑ r ∈ Finset.range (j + 1),
        (((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) : ℝ) * pi r)
        - kappa * (G * lvSum n j X)|
      ≤ eps * (kappa * (G * lvSum n j X)) := by
  classical
  have hI : ∀ r ∈ Finset.range (j + 1),
      0 ≤ (((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) : ℝ) := by
    intro r _
    positivity
  have h := abs_sum_mul_sub_mul_sum_le (Finset.range (j + 1))
    (fun r => (((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) : ℝ))
    (fun r => 1 / ((n : ℝ) - (r : ℝ))) pi (kappa * G) eps hI hpi
  rw [sum_lastVisit_wcoef_eq_lvSum n j X] at h
  have hassoc : kappa * G * lvSum n j X = kappa * (G * lvSum n j X) := by ring
  rw [hassoc] at h
  exact h

/-- The weighted last-visit sum is nonnegative below the horizon. -/
theorem lvSum_nonneg {n j : ℕ} (hj : j < n) (X : ℕ → Site d) : 0 ≤ lvSum n j X := by
  refine Finset.sum_nonneg fun i hi => ?_
  have hw : 0 ≤ wcoef n i := by
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have : (i : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_le_of_lt hi' hj
    rw [wcoef]
    positivity
  have hv : 0 ≤ visitInd i (j - i) X := by
    rw [visitInd]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  exact mul_nonneg hv hw

/-- **Step 2 of `lem:dgt4-path-survival` along one path, integrated, with every error
named** (`sandpile.tex:5524-5566`).  The profile is `(1-j/n)^\kappa` and the four errors are
the threshold replacement, the factorization, the square sum of the weights, and the integral
bound on the weighted last-visit defect. -/
theorem integral_abs_survival_sub_profile_le [NeZero d]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ) (b : ℕ → ℝ) (hb : Antitone b)
    (hshift : ∀ (t : ℕ) (c : ℝ) (y : Site d),
      (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t y = 0} {σ : Site d → ℝ | c < J σ y})
        = (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t 0 = 0} {σ : Site d → ℝ | c < J σ 0}))
    (n j : ℕ) (hj : j < n) (eta theta : ℝ)
    (hthr : ∀ r, r ≤ j → ((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
        (symmDiff {σ : Site d → ℝ | odometer σ (n - r) 0 = 0}
          {σ : Site d → ℝ | b r < J σ 0}) ≤ eta)
    (hfact : ∀ X : ℕ → Site d, ∀ (m : ℕ) (ts : Fin m → ℕ),
      Function.Injective (fun i => X (ts i)) → (m : ℝ) ≤ (j : ℝ) + 1 →
      |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ i : Fin m, J σ (X (ts i)) ≤ b (ts i)}
        - ∏ i : Fin m, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b (ts i)}|
        ≤ theta)
    (pi : ℕ → ℝ)
    (hpi : ∀ r, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b r} = 1 - pi r)
    (kappa G eps eta' : ℝ)
    (hpi0 : ∀ r ∈ Finset.range (j + 1), 0 ≤ pi r)
    (hpih : ∀ r ∈ Finset.range (j + 1), pi r ≤ 1 / 2)
    (hpiu : ∀ r ∈ Finset.range (j + 1), pi r ≤ 2 * (kappa * G) / ((n - r : ℕ) : ℝ))
    (hpirel : ∀ r ∈ Finset.range (j + 1),
      |pi r - (kappa * G) * (1 / ((n : ℝ) - (r : ℝ)))|
        ≤ eps * ((kappa * G) * (1 / ((n : ℝ) - (r : ℝ)))))
    (hkappa : 0 < kappa) (hG : 0 ≤ G) (heps : 0 ≤ eps)
    (hlvint : ∫ X, |G * lvSum n j X + Real.log (1 - (j : ℝ) / (n : ℝ))| ∂(walkLaw d 0)
      ≤ eta') :
    ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
            (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - (1 - (j : ℝ) / (n : ℝ)) ^ kappa|
        ∂(walkLaw d 0)
      ≤ (eta * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ + theta)
        + 2 * ((2 * (kappa * G)) ^ 2 * (2 / ((n - j : ℕ) : ℝ)))
        + (kappa * eta' + eps * kappa * (eta' - Real.log (1 - (j : ℝ) / (n : ℝ)))) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le j) hj
    exact_mod_cast this
  have hjn : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj
  have hx : (0 : ℝ) < 1 - (j : ℝ) / (n : ℝ) := by
    have : (j : ℝ) / (n : ℝ) < 1 := (div_lt_one hn0).mpr hjn
    linarith
  have hx1 : 1 - (j : ℝ) / (n : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ (j : ℝ) / (n : ℝ) := by positivity
    linarith
  exact integral_abs_survival_sub_rpow_le ν J b hb hshift n j hj eta theta hthr hfact pi hpi
    kappa G (Real.log (1 - (j : ℝ) / (n : ℝ))) eta' eps (1 - (j : ℝ) / (n : ℝ))
    ((2 * (kappa * G)) ^ 2 * (2 / ((n - j : ℕ) : ℝ))) (lvSum n j) hpi0 hpih hkappa
    (fun X => mul_nonneg hG (lvSum_nonneg hj X)) heps hx hx1 rfl
    (fun X => sum_lastVisit_sq_le n j hj X pi (kappa * G) (mul_nonneg hkappa.le hG) hpi0 hpiu)
    (fun X => abs_sum_lastVisit_sub_le n j X pi kappa G eps hpirel)
    ((((integrable_lvSum n j).const_mul G).add (integrable_const _)).abs) hlvint

end Sandpile
