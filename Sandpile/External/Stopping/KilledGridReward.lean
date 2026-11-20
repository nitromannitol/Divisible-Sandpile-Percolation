import Sandpile.External.Stopping.KilledStepHorizon
import Sandpile.Support.KillRadius

/-!
# Grid-horizon rewards

The lattice reward uses the rounded horizon rather than the real horizon.
Their time arguments differ by less than one diffusive lattice step.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- A bounded time-shifted lattice reward is integrable at every bounded walk
stopping time. -/
theorem integrable_stopped_shiftedReward {d : ℕ} [NeZero d] (R : ℝ) (x : Site d)
    (N : ℕ) (A M : ℝ) (G : ℝ → Continuum.Space d → ℝ)
    (hM : ∀ s z, |G s z| ≤ M) {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) (hτN : ∀ X, τ X ≤ N) :
    Integrable (fun X => G (A - (τ X : ℝ) / R ^ 2)
      (Lclt.scaledSite R (X (τ X)))) (walkLaw d x) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  let H : ℝ → Continuum.Space d → ℝ := fun s z => G (s + (A - (N : ℝ) / R ^ 2)) z
  have h := integrable_stopped_scaledReward hd x N R H M (fun s z => hM _ _) hτ hτN
  convert h using 1
  funext X
  congr 2
  ring

/-- Bounded rewards give a bounded killed payoff set after an arbitrary
shift of the horizon. -/
theorem bddAbove_killedSet_shiftedReward {d : ℕ} [NeZero d] (R : ℝ) (D : Set (Site d))
    (x : Site d) (N : ℕ) (A M : ℝ) (G : ℝ → Continuum.Space d → ℝ)
    (hM : ∀ s z, |G s z| ≤ M) :
    BddAbove (killedSet D N x (fun k X => G (A - (k : ℝ) / R ^ 2)
      (Lclt.scaledSite R (X k)))) := by
  let : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  refine ⟨M, ?_⟩
  rintro a ⟨τ, _, _, _, rfl⟩
  have h := norm_integral_le_of_norm_le_const (μ := walkLaw d x)
    (f := fun X => G (A - (τ X : ℝ) / R ^ 2) (Lclt.scaledSite R (X (τ X))))
    (C := M) (Filter.Eventually.of_forall fun X => by
      simpa only [Real.norm_eq_abs] using hM (A - (τ X : ℝ) / R ^ 2) _)
  exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using h)

/-- Replacing the real horizon in a lattice reward by its grid approximation
changes the killed value by at most the temporal modulus. -/
theorem abs_killedStoppingSup_sub_gridReward_le {d : ℕ} [NeZero d] {R : ℝ} (hR : 0 < R)
    (D : Set (Site d)) (x : Site d) (T M ε : ℝ) (hT : 0 ≤ T)
    (G : ℝ → Continuum.Space d → ℝ) (hM : ∀ s z, |G s z| ≤ M)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < 1 / R ^ 2 → |G s z - G u z| ≤ ε) :
    |killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
        G (T - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k))) -
      killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
        G (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Lclt.scaledSite R (X k)))| ≤ ε := by
  let N := ⌊R ^ 2 * T⌋₊
  let A : ℝ := (N : ℝ) / R ^ 2
  let F : ℕ → (ℕ → Site d) → ℝ := fun k X =>
    G (T - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k))
  let H : ℕ → (ℕ → Site d) → ℝ := fun k X =>
    G (A - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k))
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hpos : 0 < R ^ 2 := sq_pos_of_pos hR
  have hA0 : 0 ≤ A := div_nonneg (Nat.cast_nonneg _) hpos.le
  have hAT : A ≤ T := by
    apply (div_le_iff₀ hpos).2
    have hf := Nat.floor_le (mul_nonneg hpos.le hT)
    change (N : ℝ) ≤ R ^ 2 * T at hf
    nlinarith
  have hdiff : T - A < 1 / R ^ 2 := by
    have hf := Nat.lt_floor_add_one (R ^ 2 * T)
    change R ^ 2 * T < (N : ℝ) + 1 at hf
    dsimp [A]
    apply (sub_lt_iff_lt_add).2
    rw [← add_div]
    apply (lt_div_iff₀ hpos).2
    nlinarith
  have hbound := abs_killedStoppingSup_sub_le_of_reward hd D N x F H ε
    (bddAbove_killedSet_shiftedReward R D x N T M G hM)
    (bddAbove_killedSet_shiftedReward R D x N A M G hM)
    (fun τ hτ hτN => integrable_stopped_shiftedReward R x N T M G hM hτ hτN)
    (fun τ hτ hτN => integrable_stopped_shiftedReward R x N A M G hM hτ hτN) (by
      intro k hk X
      have hkA : (k : ℝ) / R ^ 2 ≤ A := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hk) hpos.le
      have hk0 : 0 ≤ (k : ℝ) / R ^ 2 := div_nonneg (Nat.cast_nonneg _) hpos.le
      have hs : T - (k : ℝ) / R ^ 2 ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
      have hu : A - (k : ℝ) / R ^ 2 ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
      have habs : |(T - (k : ℝ) / R ^ 2) - (A - (k : ℝ) / R ^ 2)| < 1 / R ^ 2 := by
        rw [show (T - (k : ℝ) / R ^ 2) - (A - (k : ℝ) / R ^ 2) = T - A by ring,
          abs_of_nonneg (sub_nonneg.mpr hAT)]
        exact hdiff
      exact hG _ hs _ hu _ habs)
  have heq : H = (fun (k : ℕ) (X : ℕ → Site d) => G (((N : ℝ) - (k : ℝ)) / R ^ 2)
      (Lclt.scaledSite R (X k))) := by
    funext k X
    dsimp [H, A]
    congr 1
    ring
  rw [heq] at hbound
  exact hbound

/-- The killed step-walk value at the real horizon and the killed lattice
value with its grid-horizon reward differ by at most twice the temporal
modulus at one diffusive lattice step. -/
theorem abs_sSup_killedStepTimePayoffs_sub_killedGridReward_le {d : ℕ} [NeZero d]
    {R : ℝ} (hR : 0 < R) (D : Set (Site d)) (x : Site d)
    (T M ε : ℝ) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGm : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hM : ∀ s z, |G s z| ≤ M)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < 1 / R ^ 2 → |G s z - G u z| ≤ ε) :
    |sSup (killedStepTimePayoffs R D x T G) -
      killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
        G (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Lclt.scaledSite R (X k)))| ≤ 2 * ε := by
  let middle := killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
    G (T - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k)))
  have h₁ : |sSup (killedStepTimePayoffs R D x T G) - middle| ≤ ε :=
    abs_sSup_killedStepTimePayoffs_sub_killedStoppingSup_le hR D x T M ε hT hε G hGm hM hG
  have h₂ : |middle - killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
      G (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
        (Lclt.scaledSite R (X k)))| ≤ ε :=
    abs_killedStoppingSup_sub_gridReward_le hR D x T M ε hT G hM hG
  calc
    _ ≤ |sSup (killedStepTimePayoffs R D x T G) - middle| +
        |middle - killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
          G (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
            (Lclt.scaledSite R (X k)))| := abs_sub_le _ _ _
    _ ≤ 2 * ε := by linarith

end Sandpile.External.Stopping
