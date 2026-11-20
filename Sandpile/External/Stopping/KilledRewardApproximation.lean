import Sandpile.External.Stopping.KilledGridReward

/-!
# Approximation of killed stopping rewards

Uniform approximation of bounded rewards controls killed lattice values even
when the approximating reward is not measurable or continuous. Combined with
grid-time rounding, this compares the step-walk value of a measurable reward
with the lattice value of its approximation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Uniformly close bounded rewards have uniformly close killed lattice
values. The approximating reward need not be measurable. -/
theorem abs_killedGridReward_sub_le_of_uniform {d : ℕ} [NeZero d]
    {R : ℝ} (hR : 0 < R) (D : Set (Site d)) (x : Site d)
    (T M ε : ℝ) (hT : 0 ≤ T) (G H : ℝ → Continuum.Space d → ℝ)
    (hG : ∀ s z, |G s z| ≤ M) (hH : ∀ s z, |H s z| ≤ M)
    (hGH : ∀ s ∈ Icc (0 : ℝ) T, ∀ z, |G s z - H s z| ≤ ε) :
    |killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
        G (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Lclt.scaledSite R (X k))) -
      killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
        H (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Lclt.scaledSite R (X k)))| ≤ ε := by
  let N := ⌊R ^ 2 * T⌋₊
  let A : ℝ := (N : ℝ) / R ^ 2
  let F : ℕ → (ℕ → Site d) → ℝ := fun k X =>
    G (A - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k))
  let J : ℕ → (ℕ → Site d) → ℝ := fun k X =>
    H (A - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k))
  have hpos : 0 < R ^ 2 := sq_pos_of_pos hR
  have hAT : A ≤ T := by
    apply (div_le_iff₀ hpos).2
    have hf := Nat.floor_le (mul_nonneg hpos.le hT)
    change (N : ℝ) ≤ R ^ 2 * T at hf
    nlinarith
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hb := abs_killedStoppingSup_sub_le_of_reward hd D N x F J ε
    (bddAbove_killedSet_shiftedReward R D x N A M G hG)
    (bddAbove_killedSet_shiftedReward R D x N A M H hH)
    (fun τ hτ hτN => integrable_stopped_shiftedReward R x N A M G hG hτ hτN)
    (fun τ hτ hτN => integrable_stopped_shiftedReward R x N A M H hH hτ hτN) (by
      intro k hk X
      have hkA : (k : ℝ) / R ^ 2 ≤ A :=
        div_le_div_of_nonneg_right (by exact_mod_cast hk) hpos.le
      have hk0 : 0 ≤ (k : ℝ) / R ^ 2 := div_nonneg (Nat.cast_nonneg _) hpos.le
      exact hGH _ ⟨by linarith, by linarith⟩ _)
  simpa only [F, J, A, ← sub_div] using hb

/-- A uniform reward approximation and a temporal modulus control the
comparison between killed step-walk and lattice values. -/
theorem abs_sSup_killedStepTimePayoffs_sub_killedGridReward_approx_le
    {d : ℕ} [NeZero d] {R : ℝ} (hR : 0 < R) (D : Set (Site d)) (x : Site d)
    (T M ε η : ℝ) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (G H : ℝ → Continuum.Space d → ℝ)
    (hGm : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hG : ∀ s z, |G s z| ≤ M) (hH : ∀ s z, |H s z| ≤ M)
    (hmod : ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < 1 / R ^ 2 → |G s z - G u z| ≤ ε)
    (happrox : ∀ s ∈ Icc (0 : ℝ) T, ∀ z, |G s z - H s z| ≤ η) :
    |sSup (killedStepTimePayoffs R D x T G) -
      killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
        H (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Lclt.scaledSite R (X k)))| ≤ 2 * ε + η := by
  let middle := killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
    G (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
      (Lclt.scaledSite R (X k)))
  have h₁ : |sSup (killedStepTimePayoffs R D x T G) - middle| ≤ 2 * ε :=
    abs_sSup_killedStepTimePayoffs_sub_killedGridReward_le hR D x T M ε hT hε G hGm hG hmod
  have h₂ : |middle - killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
      H (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
        (Lclt.scaledSite R (X k)))| ≤ η :=
    abs_killedGridReward_sub_le_of_uniform hR D x T M η hT G H hG hH happrox
  exact (abs_sub_le _ _ _).trans (add_le_add h₁ h₂)

end Sandpile.External.Stopping
