import Sandpile.Support.LinStep2Window

/-!
# Step 2 of the path-survival estimate, assembled along one path

The deterministic chain `abs_prod_pow_sub_rpow_le` bounds `∏_{r≤j} (1 - π_r) ^ I_{r,j}(X)` against
the profile `x ^ κ` for a natural-number last-visit exponent. This file supplies the remaining
pieces needed to apply it to the survival probability: `abs_survival_sub_prod_nat_le` produces the
chain's left-hand side from the survival probability using a replacement and a factorization
error, and `measureReal_threshold_le_eq` identifies `P (J(0) ≤ b_r)` with `1 - π_r` for a threshold
event that is only null measurable. Combining these, `abs_survival_sub_rpow_le` bounds the survival
probability along a single path against the profile `x ^ κ` by the sum of four errors: the
replacement error, the factorization error, the product-to-exponential error, and the error of the
weighted last-visit sum.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- `P(J(0) ≤ c) = 1 - π` with `π = P(J(0) > c)`, for a threshold event that is only null
measurable. -/
theorem measureReal_threshold_le_eq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ) (c : ℝ)
    (hnull : NullMeasurableSet {σ : Site d → ℝ | c < J σ 0} (centeredMassLaw d ν)) :
    (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ c}
      = 1 - (centeredMassLaw d ν).real {σ : Site d → ℝ | c < J σ 0} := by
  have hcompl : {σ : Site d → ℝ | J σ 0 ≤ c} = {σ : Site d → ℝ | c < J σ 0}ᶜ := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  have h1 : (centeredMassLaw d ν) {σ : Site d → ℝ | c < J σ 0}ᶜ
      = 1 - (centeredMassLaw d ν) {σ : Site d → ℝ | c < J σ 0} := by
    rw [measure_compl₀ hnull (measure_ne_top _ _), measure_univ]
  rw [hcompl, measureReal_def, h1,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one,
    measureReal_def]

/-- **Step 2 of `lem:dgt4-path-survival` in the form the deterministic chain consumes.**  The
survival probability along `X` differs from `∏_{r≤j}(1-π_r)^{I_{r,j}(X)}`, with the NATURAL
last-visit exponent of `Sandpile.abs_prod_pow_sub_rpow_le`, by the replacement error plus the
factorization error. -/
theorem abs_survival_sub_prod_nat_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ) (b : ℕ → ℝ) (hb : Antitone b)
    (hshift : ∀ (t : ℕ) (c : ℝ) (y : Site d),
      (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t y = 0} {σ : Site d → ℝ | c < J σ y})
        = (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t 0 = 0} {σ : Site d → ℝ | c < J σ 0}))
    (n j : ℕ) (hj : j < n) (X : ℕ → Site d) (eta theta : ℝ)
    (hthr : ∀ r, r ≤ j → ((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
        (symmDiff {σ : Site d → ℝ | odometer σ (n - r) 0 = 0}
          {σ : Site d → ℝ | b r < J σ 0}) ≤ eta)
    (hfact : ∀ (m : ℕ) (ts : Fin m → ℕ), Function.Injective (fun i => X (ts i)) →
      (m : ℝ) ≤ (j : ℝ) + 1 →
      |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ i : Fin m, J σ (X (ts i)) ≤ b (ts i)}
        - ∏ i : Fin m, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b (ts i)}|
        ≤ theta)
    (pi : ℕ → ℝ)
    (hpi : ∀ r, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b r} = 1 - pi r) :
    |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ r ≤ j, 0 < odometer σ (n - r) (X r)}
        - ∏ r ∈ Finset.range (j + 1),
            (1 - pi r) ^ (if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)|
      ≤ eta * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ + theta := by
  classical
  have h := abs_survival_sub_prod_le ν J b hb hshift n j hj X eta theta hthr hfact
  rw [prod_rpow_lastVisitIndicator j X
    (fun r => (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b r})] at h
  rw [prod_pow_lastVisit_if j X (fun r => 1 - pi r)]
  simpa only [hpi] using h

/-! ### The whole of Step 2 along one path -/

/-- **The whole of Step 2 of `lem:dgt4-path-survival` along one path**
(`sandpile.tex:5524-5578`): the survival probability along `X` differs from the profile
`x^κ` by the replacement error, the factorization error, the product-to-exponential error and
the error of the weighted last-visit sum. -/
theorem abs_survival_sub_rpow_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ) (b : ℕ → ℝ) (hb : Antitone b)
    (hshift : ∀ (t : ℕ) (c : ℝ) (y : Site d),
      (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t y = 0} {σ : Site d → ℝ | c < J σ y})
        = (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t 0 = 0} {σ : Site d → ℝ | c < J σ 0}))
    (n j : ℕ) (hj : j < n) (X : ℕ → Site d) (eta theta : ℝ)
    (hthr : ∀ r, r ≤ j → ((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
        (symmDiff {σ : Site d → ℝ | odometer σ (n - r) 0 = 0}
          {σ : Site d → ℝ | b r < J σ 0}) ≤ eta)
    (hfact : ∀ (m : ℕ) (ts : Fin m → ℕ), Function.Injective (fun i => X (ts i)) →
      (m : ℝ) ≤ (j : ℝ) + 1 →
      |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ i : Fin m, J σ (X (ts i)) ≤ b (ts i)}
        - ∏ i : Fin m, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b (ts i)}|
        ≤ theta)
    (pi : ℕ → ℝ)
    (hpi : ∀ r, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b r} = 1 - pi r)
    (kappa G S L eta' eps x : ℝ)
    (hpi0 : ∀ r ∈ Finset.range (j + 1), 0 ≤ pi r)
    (hpih : ∀ r ∈ Finset.range (j + 1), pi r ≤ 1 / 2)
    (hkappa : 0 < kappa) (hGS : 0 ≤ G * S) (heps : 0 ≤ eps) (hx : 0 < x) (hx1 : x ≤ 1)
    (hL : L = Real.log x) (hlv : |G * S + L| ≤ eta')
    (hPd : |(∑ r ∈ Finset.range (j + 1),
        ((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ) : ℝ) * pi r) - kappa * (G * S)|
      ≤ eps * (kappa * (G * S))) :
    |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ r ≤ j, 0 < odometer σ (n - r) (X r)}
        - x ^ kappa|
      ≤ (eta * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ + theta)
        + (2 * (∑ r ∈ Finset.range (j + 1),
            ((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ) : ℝ) * pi r ^ 2)
          + (kappa * eta' + eps * kappa * (eta' - L))) := by
  classical
  have h1 := abs_survival_sub_prod_nat_le ν J b hb hshift n j hj X eta theta hthr hfact pi hpi
  have h2 := abs_prod_pow_sub_rpow_le (Finset.range (j + 1)) pi
    (fun r => if r ∈ lastVisitTimes j X then 1 else 0) kappa G S L eta' eps x
    hpi0 hpih hkappa hGS heps hx hx1 hL hlv hPd
  have hsplit : (centeredMassLaw d ν).real
        {σ : Site d → ℝ | ∀ r ≤ j, 0 < odometer σ (n - r) (X r)} - x ^ kappa
      = ((centeredMassLaw d ν).real
          {σ : Site d → ℝ | ∀ r ≤ j, 0 < odometer σ (n - r) (X r)}
          - ∏ r ∈ Finset.range (j + 1),
            (1 - pi r) ^ (if r ∈ lastVisitTimes j X then 1 else 0 : ℕ))
        + ((∏ r ∈ Finset.range (j + 1),
            (1 - pi r) ^ (if r ∈ lastVisitTimes j X then 1 else 0 : ℕ)) - x ^ kappa) := by
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

end Sandpile
