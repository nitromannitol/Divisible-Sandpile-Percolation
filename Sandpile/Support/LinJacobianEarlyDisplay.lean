/-
The early display of Step 1 of `lem:dgt4-linearization-from-survival`
(`eq:dgt4-early-derivative-variance`, `sandpile.tex:5731-5753`) in the form the
assembly of `Support/LinJacobianStep1Limit.lean` asks for, and Step 1 itself.

The paper combines the covariance hypothesis of the lemma with the two tested
intersection moments `eq:dgt4-tested-intersection-moments` to get

  "`∑_z Var(D^{≤}_{R,z}) ≤ C(φ)ε_R(δ) + C(φ)/(δR²)`".

Here the covariance hypothesis is used at the times of the early sum, where it
applies, and the intersection count `I(X,Y)` is any real-valued majorant of the
time-restricted intersection sums with the two moment bounds.
-/
import Sandpile.Support.LinJacobianStep1Limit
import Sandpile.Support.LinJacobianLateDisplay

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ} [NeZero d] (μ : Measure (Site d → ℝ))

/-- **`eq:dgt4-early-derivative-variance` as the hypothesis `hearly`.**  The
covariance bound at the early times and the two tested intersection moments give
the early display with `C = max (C₀C₂) C₁`. -/
theorem early_display_of_moments {l : Filter ℝ} [IsProbabilityMeasure μ] (n : ℝ → ℕ)
    (s : ℝ → Finset (Site d)) (a : ℝ → Site d → ℝ) (ha : ∀ (R : ℝ) (x : Site d), 0 ≤ a R x)
    (I : (ℕ → Site d) → (ℕ → Site d) → ℝ) (hI0 : ∀ X Y, 0 ≤ I X Y)
    (hsumI : ∀ (t : Finset ℕ) (x y : Site d), ∀ᵐ p ∂(walkPairLaw d x y),
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) ≤ I p.1 p.2)
    (C₀ C₁ C₂ : ℝ) (hC₀ : 0 ≤ C₀) (_hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hI1 : ∀ R : ℝ, ∑ x ∈ s R, ∑ y ∈ s R,
      a R x * a R y * ∫ p, I p.1 p.2 ∂(walkPairLaw d x y) ≤ C₁)
    (hI2 : ∀ R : ℝ, ∑ x ∈ s R, ∑ y ∈ s R,
      a R x * a R y * ∫ p, (I p.1 p.2) ^ 2 ∂(walkPairLaw d x y) ≤ C₂)
    (hint1 : ∀ x y : Site d, Integrable (fun p => I p.1 p.2) (walkPairLaw d x y))
    (hint2 : ∀ x y : Site d, Integrable (fun p => (I p.1 p.2) ^ 2) (walkPairLaw d x y))
    (hint3 : ∀ (N : ℕ) (t : Finset ℕ) (x y : Site d), Integrable (fun p =>
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) * covSurvival μ N i j p.1 p.2)
      (walkPairLaw d x y))
    (δ₀ : ℝ)
    (hcov : ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ eps : ℝ → ℝ, (∀ R : ℝ, 0 ≤ eps R) ∧
      Tendsto eps l (𝓝 0) ∧
      ∀ (R : ℝ) (i j : ℕ), (i : ℝ) ≤ ((n R : ℝ)) - δ * R ^ 2 →
        (j : ℝ) ≤ ((n R : ℝ)) - δ * R ^ 2 → ∀ x y : Site d,
          ∀ᵐ p ∂(walkPairLaw d x y),
            |covSurvival μ (n R) i j p.1 p.2| ≤ C₀ / (δ * R ^ 2) * I p.1 p.2 + eps R)
    (δ : ℝ) (hδ : 0 < δ) (hδlt : δ < δ₀)
    (hl : l ≤ atTop := by exact le_rfl) :
    ∃ eps : ℝ → ℝ, (∀ R : ℝ, 0 ≤ eps R) ∧ Tendsto eps l (𝓝 0) ∧
      ∀ᶠ R : ℝ in l, (∑' z : Site d, variance
          (fun σ => ∑ x ∈ s R, a R x *
            jacobianTimes (scenery d σ) (n R) (earlyTimes (n R) δ R) x z) μ)
        ≤ max (C₀ * C₂) C₁ * eps R + max (C₀ * C₂) C₁ / (δ * R ^ 2) := by
  classical
  obtain ⟨eps, heps0, hepstend, hepsbd⟩ := hcov δ hδ hδlt
  refine ⟨eps, heps0, hepstend, ?_⟩
  filter_upwards [(eventually_gt_atTop (0 : ℝ)).filter_mono hl] with R hR
  have hδR : (0 : ℝ) < δ * R ^ 2 := by positivity
  have hCd : (0 : ℝ) ≤ C₀ / (δ * R ^ 2) := by positivity
  have hcovae : ∀ x y : Site d, ∀ᵐ p ∂(walkPairLaw d x y),
      ∀ i ∈ earlyTimes (n R) δ R, ∀ j ∈ earlyTimes (n R) δ R,
        |covSurvival μ (n R) i j p.1 p.2| ≤ C₀ / (δ * R ^ 2) * I p.1 p.2 + eps R := by
    intro x y
    rw [Filter.eventually_all_finset]
    intro i hi
    rw [Filter.eventually_all_finset]
    intro j hj
    exact hepsbd R i j (mem_earlyTimes (n R) δ R hi) (mem_earlyTimes (n R) δ R hj) x y
  have hmain := tsum_variance_sum_jacobianTimes_le μ (n R) (s R) (a R)
    (earlyTimes (n R) δ R) (ha R) I (C₀ / (δ * R ^ 2)) (eps R) C₁ C₂ hCd (heps0 R) hI0
    (fun x y => hsumI (earlyTimes (n R) δ R) x y) hcovae
    (hI1 R) (hI2 R) hint1 hint2 (fun x y => hint3 (n R) (earlyTimes (n R) δ R) x y)
  refine hmain.trans ?_
  have h1 : C₀ / (δ * R ^ 2) * C₂ ≤ max (C₀ * C₂) C₁ / (δ * R ^ 2) := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδR]
    exact le_max_left _ _
  have h2 : eps R * C₁ ≤ max (C₀ * C₂) C₁ * eps R := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (heps0 R)
  linarith

/-- **Step 1 of `lem:dgt4-linearization-from-survival`**
(`eq:dgt4-derivative-variance-limit`, `sandpile.tex:5705-5778`) from the
covariance hypothesis of the lemma, the two tested intersection moments and
`eq:dgt4-tested-cell-l2`. -/
theorem tendsto_tsum_variance_of_moments {l : Filter ℝ} [IsProbabilityMeasure μ] (hd : 1 ≤ d) (n : ℝ → ℕ)
    (s : ℝ → Finset (Site d)) (a : ℝ → Site d → ℝ) (ha : ∀ (R : ℝ) (x : Site d), 0 ≤ a R x)
    (hsupp : ∀ R : ℝ, ∀ x ∉ s R, a R x = 0)
    (hsq : ∀ R : ℝ, Summable fun z : Site d => (a R z) ^ 2)
    (I : (ℕ → Site d) → (ℕ → Site d) → ℝ) (hI0 : ∀ X Y, 0 ≤ I X Y)
    (hsumI : ∀ (t : Finset ℕ) (x y : Site d), ∀ᵐ p ∂(walkPairLaw d x y),
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) ≤ I p.1 p.2)
    (C₀ C₁ C₂ Cphi : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCphi : 0 ≤ Cphi)
    (hI1 : ∀ R : ℝ, ∑ x ∈ s R, ∑ y ∈ s R,
      a R x * a R y * ∫ p, I p.1 p.2 ∂(walkPairLaw d x y) ≤ C₁)
    (hI2 : ∀ R : ℝ, ∑ x ∈ s R, ∑ y ∈ s R,
      a R x * a R y * ∫ p, (I p.1 p.2) ^ 2 ∂(walkPairLaw d x y) ≤ C₂)
    (hint1 : ∀ x y : Site d, Integrable (fun p => I p.1 p.2) (walkPairLaw d x y))
    (hint2 : ∀ x y : Site d, Integrable (fun p => (I p.1 p.2) ^ 2) (walkPairLaw d x y))
    (hint3 : ∀ (N : ℕ) (t : Finset ℕ) (x y : Site d), Integrable (fun p =>
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) * covSurvival μ N i j p.1 p.2)
      (walkPairLaw d x y))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hcov : ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ eps : ℝ → ℝ, (∀ R : ℝ, 0 ≤ eps R) ∧
      Tendsto eps l (𝓝 0) ∧
      ∀ (R : ℝ) (i j : ℕ), (i : ℝ) ≤ ((n R : ℝ)) - δ * R ^ 2 →
        (j : ℝ) ≤ ((n R : ℝ)) - δ * R ^ 2 → ∀ x y : Site d,
          ∀ᵐ p ∂(walkPairLaw d x y),
            |covSurvival μ (n R) i j p.1 p.2| ≤ C₀ / (δ * R ^ 2) * I p.1 p.2 + eps R)
    (hcell : ∀ᶠ R : ℝ in l,
      (∑' z : Site d, (a R z) ^ 2) ≤ Cphi * (R ^ 4)⁻¹)
    (hl : l ≤ atTop := by exact le_rfl) :
    Tendsto (fun R : ℝ => ∑' z : Site d,
        variance (fun σ => ∑ x ∈ s R, a R x * odometerJacobian (scenery d σ) (n R) x z) μ)
      l (𝓝 0) := by
  classical
  set C : ℝ := max (max (C₀ * C₂) C₁) Cphi with hCdef
  have hC : 0 ≤ C := le_trans hCphi (le_max_right _ _)
  refine tendsto_tsum_variance_odometerJacobian (hl := hl) μ hd n s a ha hsupp hsq C hC δ₀ hδ₀ ?_ ?_
  · intro δ hδ hδlt
    obtain ⟨eps, heps0, hepstend, hepsbd⟩ := early_display_of_moments (hl := hl) μ n s a ha I hI0 hsumI
      C₀ C₁ C₂ hC₀ hC₁ hC₂ hI1 hI2 hint1 hint2 hint3 δ₀ hcov δ hδ hδlt
    refine ⟨eps, hepstend, ?_⟩
    filter_upwards [hepsbd, (eventually_gt_atTop (0 : ℝ)).filter_mono hl] with R hR hRpos
    have hδR : (0 : ℝ) < δ * R ^ 2 := by positivity
    have hle : max (C₀ * C₂) C₁ ≤ C := le_max_left _ _
    refine hR.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_right hle (heps0 R)
    · exact (div_le_div_iff_of_pos_right hδR).2 hle
  · intro δ hδ _
    obtain ⟨o, hotend, hobd⟩ := late_display_of_cell_l2 (hl := hl) Cphi hCphi n
      (fun R => ∑' z : Site d, (a R z) ^ 2) hcell δ hδ
    refine ⟨o, hotend, ?_⟩
    filter_upwards [hobd] with R hR
    have hCp : Cphi ≤ C := le_max_right _ _
    have hmul : Cphi * δ ^ 2 ≤ C * δ ^ 2 := mul_le_mul_of_nonneg_right hCp (sq_nonneg δ)
    linarith

end Sandpile
