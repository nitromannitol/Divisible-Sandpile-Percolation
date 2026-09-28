import Sandpile.Support.ContMeshIntegral

/-!
# Parity-restricted double sums with a varying integrand

The parity-restricted double time sums of `sandpile.tex:1157-1161` with an
`R`-dependent integrand. The limit theorems of `Sandpile.Support.ContMeshIntegral` take a
fixed bounded continuous integrand, while the integrand produced by the local central
limit theorem of `sandpile.tex:1145-1161` depends on `R`, both through the accuracy of the
local limit theorem itself and through the mesh points at which the Brownian kernel is
read. This file removes that dependence: a double Riemann sum over any set of index pairs
moves by at most the number of pairs times the mesh area times the uniform distance
between the two integrands (`abs_sum2_filter_sub_le`), so an `R`-dependent integrand
converging uniformly to a fixed one has the same limit as the fixed integrand
(`tendsto_sum2_parity_of_family`, and its eventual-closeness form
`tendsto_sum2_parity_of_family'`).

The parity class of the time pairs is also `R`-dependent, since it is fixed by the parity
of the coordinate sum of the two lattice sites, which moves with `R`. Both classes have
the same limit, half the double time integral, so the limit does not see which class is
taken (`tendsto_of_eq_or_eq`).
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

/-- A double Riemann sum over an arbitrary set of index pairs is stable under a
uniform perturbation of its integrand. -/
theorem abs_sum2_filter_sub_le {H η : ℝ} (hH : 0 ≤ H) (A : Finset (ℕ × ℕ))
    (F G : ℕ → ℕ → ℝ) (h : ∀ p ∈ A, |F p.1 p.2 - G p.1 p.2| ≤ η) :
    |(∑ p ∈ A, F p.1 p.2 * H * H) - ∑ p ∈ A, G p.1 p.2 * H * H|
      ≤ (A.card : ℝ) * (H * H) * η := by
  have hid : (∑ p ∈ A, F p.1 p.2 * H * H) - ∑ p ∈ A, G p.1 p.2 * H * H
      = ∑ p ∈ A, (F p.1 p.2 - G p.1 p.2) * H * H := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hid]
  calc |∑ p ∈ A, (F p.1 p.2 - G p.1 p.2) * H * H|
      ≤ ∑ p ∈ A, |(F p.1 p.2 - G p.1 p.2) * H * H| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ A, η * H * H := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hH]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h p hp) hH) hH
    _ = (A.card : ℝ) * (H * H) * η := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- A family each of whose values agrees with one of two convergent families
converges to their common limit. -/
theorem tendsto_of_eq_or_eq {s s₁ s₂ : ℝ → ℝ} {L : ℝ} (h₁ : Tendsto s₁ atTop (𝓝 L))
    (h₂ : Tendsto s₂ atTop (𝓝 L)) (hs : ∀ R : ℝ, s R = s₁ R ∨ s R = s₂ R) :
    Tendsto s atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at h₁ h₂ ⊢
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := h₁ ε hε
  obtain ⟨N₂, hN₂⟩ := h₂ ε hε
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  rcases hs n with h | h
  · rw [h]; exact hN₁ n (le_trans (le_max_left N₁ N₂) hn)
  · rw [h]; exact hN₂ n (le_trans (le_max_right N₁ N₂) hn)

/-- **The parity-restricted double time sums of an `R`-dependent integrand
converging uniformly to a fixed bounded continuous one converge to half the
double time integral.**  Neither the accuracy of the local central limit theorem
nor the mesh at which the Brownian kernel is read survives in the limit. -/
theorem tendsto_sum2_parity_of_family {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u v, |f u v| ≤ M)
    (A : ℝ → Finset (ℕ × ℕ))
    (hA : ∀ R : ℝ, A R = ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
        (fun p : ℕ × ℕ => Even (p.1 + p.2))
      ∨ A R = ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
        (fun p : ℕ × ℕ => ¬ Even (p.1 + p.2)))
    (F : ℝ → ℕ → ℕ → ℝ) (η : ℝ → ℝ) (hη0 : ∀ R, 0 ≤ η R) (hη : Tendsto η atTop (𝓝 0))
    (hFf : ∀ R : ℝ, ∀ p ∈ A R,
      |F R p.1 p.2 - f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹)| ≤ η R) :
    Tendsto (fun R : ℝ => ∑ p ∈ A R, F R p.1 p.2 * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      atTop (𝓝 ((∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v) / 2)) := by
  classical
  have hbase : Tendsto (fun R : ℝ => ∑ p ∈ A R,
      f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      atTop (𝓝 ((∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v) / 2)) := by
    refine tendsto_of_eq_or_eq (tendsto_sum2_even_parity hT f hf M hM0 hM)
      (tendsto_sum2_odd_parity hT f hf M hM0 hM) (fun R => ?_)
    rcases hA R with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  have hcard : ∀ R : ℝ,
      ((A R).card : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by
    intro R
    have hsub : (A R).card ≤ ⌊R ^ 2 * T⌋₊ * ⌊R ^ 2 * T⌋₊ := by
      rcases hA R with h | h <;>
        · rw [h]
          refine le_trans (Finset.card_filter_le _ _) ?_
          simp [Finset.card_product]
    exact_mod_cast hsub
  have hdiff : Tendsto (fun R : ℝ => (∑ p ∈ A R, F R p.1 p.2 * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      - ∑ p ∈ A R, f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun R : ℝ => T * T * η R) atTop (𝓝 0) := by
      simpa using hη.const_mul (T * T)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hR2 : (0 : ℝ) < R ^ 2 := by positivity
    have hHnn : (0 : ℝ) ≤ (R ^ 2)⁻¹ := by positivity
    have hfl : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * (R ^ 2)⁻¹ ≤ T := by
      have h1 : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le (by positivity)
      calc ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * (R ^ 2)⁻¹ ≤ (R ^ 2 * T) * (R ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 hHnn
        _ = T := by field_simp
    have hfl0 : (0 : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * (R ^ 2)⁻¹ := by positivity
    have hb := abs_sum2_filter_sub_le hHnn (A R) (F R)
      (fun a b => f ((a : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹)) (fun p hp => hFf R p hp)
    rw [Real.norm_eq_abs]
    refine le_trans hb ?_
    have hstep : ((A R).card : ℝ) * ((R ^ 2)⁻¹ * (R ^ 2)⁻¹) ≤ T * T := by
      refine le_trans (mul_le_mul_of_nonneg_right (hcard R) (by positivity)) ?_
      have heq : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * ((R ^ 2)⁻¹ * (R ^ 2)⁻¹)
          = (((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * (R ^ 2)⁻¹) * (((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * (R ^ 2)⁻¹) := by
        ring
      rw [heq]
      exact mul_le_mul hfl hfl hfl0 (le_trans hfl0 hfl)
    calc ((A R).card : ℝ) * ((R ^ 2)⁻¹ * (R ^ 2)⁻¹) * η R
        ≤ (T * T) * η R := mul_le_mul_of_nonneg_right hstep (hη0 R)
      _ = T * T * η R := by ring
  have hsum := hdiff.add hbase
  simpa using hsum

/-- The same with the uniform closeness of the two integrands in its eventual
form: for every accuracy the integrands are that close at every large scale.
This is the shape in which the local central limit theorem supplies it, since
that theorem is an `ε`-`R₀` statement. -/
theorem tendsto_sum2_parity_of_family' {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ → ℝ)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u v, |f u v| ≤ M)
    (A : ℝ → Finset (ℕ × ℕ))
    (hA : ∀ R : ℝ, A R = ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
        (fun p : ℕ × ℕ => Even (p.1 + p.2))
      ∨ A R = ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
        (fun p : ℕ × ℕ => ¬ Even (p.1 + p.2)))
    (F : ℝ → ℕ → ℕ → ℝ)
    (hFf : ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop, ∀ p ∈ A R,
      |F R p.1 p.2 - f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹)| ≤ ε) :
    Tendsto (fun R : ℝ => ∑ p ∈ A R, F R p.1 p.2 * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      atTop (𝓝 ((∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v) / 2)) := by
  classical
  have hbase : Tendsto (fun R : ℝ => ∑ p ∈ A R,
      f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      atTop (𝓝 ((∫ u in Set.Ico (0 : ℝ) T, ∫ v in Set.Ico (0 : ℝ) T, f u v) / 2)) := by
    refine tendsto_of_eq_or_eq (tendsto_sum2_even_parity hT f hf M hM0 hM)
      (tendsto_sum2_odd_parity hT f hf M hM0 hM) (fun R => ?_)
    rcases hA R with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  have hcard : ∀ R : ℝ,
      ((A R).card : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by
    intro R
    have hsub : (A R).card ≤ ⌊R ^ 2 * T⌋₊ * ⌊R ^ 2 * T⌋₊ := by
      rcases hA R with h | h <;>
        · rw [h]
          refine le_trans (Finset.card_filter_le _ _) ?_
          simp [Finset.card_product]
    exact_mod_cast hsub
  have hdiff : Tendsto (fun R : ℝ => (∑ p ∈ A R, F R p.1 p.2 * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      - ∑ p ∈ A R, f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
      atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hκ : (0 : ℝ) < ε / (2 * (T * T + 1)) := by positivity
    filter_upwards [hFf (ε / (2 * (T * T + 1))) hκ, eventually_gt_atTop (0 : ℝ)]
      with R hRF hR
    have hR2 : (0 : ℝ) < R ^ 2 := by positivity
    have hHnn : (0 : ℝ) ≤ (R ^ 2)⁻¹ := by positivity
    have hfl : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * (R ^ 2)⁻¹ ≤ T := by
      have h1 : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le (by positivity)
      calc ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * (R ^ 2)⁻¹ ≤ (R ^ 2 * T) * (R ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 hHnn
        _ = T := by field_simp
    have hfl0 : (0 : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * (R ^ 2)⁻¹ := by positivity
    have hb := abs_sum2_filter_sub_le hHnn (A R) (F R)
      (fun a b => f ((a : ℝ) * (R ^ 2)⁻¹) ((b : ℝ) * (R ^ 2)⁻¹)) (fun p hp => hRF p hp)
    have hstep : ((A R).card : ℝ) * ((R ^ 2)⁻¹ * (R ^ 2)⁻¹) ≤ T * T := by
      refine le_trans (mul_le_mul_of_nonneg_right (hcard R) (by positivity)) ?_
      have heq : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * ((R ^ 2)⁻¹ * (R ^ 2)⁻¹)
          = (((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * (R ^ 2)⁻¹) * (((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * (R ^ 2)⁻¹) := by
        ring
      rw [heq]
      exact mul_le_mul hfl hfl hfl0 (le_trans hfl0 hfl)
    rw [Real.norm_eq_abs]
    have hT2 : (0 : ℝ) ≤ T * T := by positivity
    have hpos : (0 : ℝ) < 2 * (T * T + 1) := by positivity
    have h2 : (T * T) * (ε / (2 * (T * T + 1))) < ε := by
      rw [mul_div_assoc'] at *
      rw [div_lt_iff₀ hpos]
      nlinarith
    have h1 : ((A R).card : ℝ) * ((R ^ 2)⁻¹ * (R ^ 2)⁻¹) * (ε / (2 * (T * T + 1)))
        ≤ (T * T) * (ε / (2 * (T * T + 1))) :=
      mul_le_mul_of_nonneg_right hstep (le_of_lt hκ)
    calc |(∑ p ∈ A R, F R p.1 p.2 * (R ^ 2)⁻¹ * (R ^ 2)⁻¹)
            - ∑ p ∈ A R, f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹)
                * (R ^ 2)⁻¹ * (R ^ 2)⁻¹|
        ≤ ((A R).card : ℝ) * ((R ^ 2)⁻¹ * (R ^ 2)⁻¹) * (ε / (2 * (T * T + 1))) := hb
      _ < ε := lt_of_le_of_lt h1 h2
  have hsum := hdiff.add hbase
  simpa using hsum

end Sandpile.Support
