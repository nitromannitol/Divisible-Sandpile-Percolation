import Sandpile.External.Stopping.CompactRewardCutoff
import Sandpile.Support.KillBox

/-!
# Localization of killed stopping rewards

A walk killed on leaving a lattice box can stop at most one lattice step
outside it. Consequently killed rewards can be modified away from this
one-step enlargement without changing their payoff sets.
-/

open MeasureTheory Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Two rewards agreeing at all possible stopped lattice-box positions give
the same killed lattice payoff set. -/
theorem killedSet_eq_of_eq_on_box_stopped {d : ℕ} [NeZero d]
    (R L : ℝ) (q : Site d) (hL : 0 ≤ ⌊L⌋) (N : ℕ)
    (G H : ℝ → Continuum.Space d → ℝ) (A : ℝ)
    (hGH : ∀ s y, (∀ i, |y i - q i| ≤ ⌊L⌋ + 1) →
      G s (Lclt.scaledSite R y) = H s (Lclt.scaledSite R y)) :
    killedSet (supBox q L) N q (fun k X => G (A - (k : ℝ) / R ^ 2)
        (Lclt.scaledSite R (X k))) =
      killedSet (supBox q L) N q (fun k X => H (A - (k : ℝ) / R ^ 2)
        (Lclt.scaledSite R (X k))) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have key : ∀ τ : (ℕ → Site d) → ℕ, (∀ X j, j < τ X → X j ∈ supBox q L) →
      (∫ X, G (A - (τ X : ℝ) / R ^ 2) (Lclt.scaledSite R (X (τ X))) ∂(walkLaw d q)) =
      ∫ X, H (A - (τ X : ℝ) / R ^ 2) (Lclt.scaledSite R (X (τ X))) ∂(walkLaw d q) := by
    intro τ hkill
    apply integral_congr_ae
    filter_upwards [ae_walk_start q, ae_step_walk hd q] with X h0 hstep
    exact hGH _ _ (killed_position_box hL h0 hstep (τ X) (hkill X))
  ext a
  constructor
  · rintro ⟨τ, hτ, hτN, hkill, rfl⟩
    exact ⟨τ, hτ, hτN, hkill, key τ hkill⟩
  · rintro ⟨τ, hτ, hτN, hkill, rfl⟩
    exact ⟨τ, hτ, hτN, hkill, (key τ hkill).symm⟩

/-- The same one-step localization applies to killed diffusive step-walk
payoffs at arbitrary real horizons. -/
theorem killedStepTimePayoffs_eq_of_eq_on_box_stopped {d : ℕ} [NeZero d]
    (R L : ℝ) (q : Site d) (hL : 0 ≤ ⌊L⌋) (T : ℝ)
    (G H : ℝ → Continuum.Space d → ℝ)
    (hGH : ∀ s y, (∀ i, |y i - q i| ≤ ⌊L⌋ + 1) →
      G s (Lclt.scaledSite R y) = H s (Lclt.scaledSite R y)) :
    killedStepTimePayoffs R (supBox q L) q T G =
      killedStepTimePayoffs R (supBox q L) q T H := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have key : ∀ θ : (ℕ → Site d) → ℝ≥0,
      (∀ᵐ X ∂(walkLaw d q), ∀ j : ℕ, (j : ℝ) < R ^ 2 * (θ X : ℝ) →
        X j ∈ supBox q L) →
      (∫ X, G (T - θ X) (diffusiveStepWalk R (θ X) X) ∂(walkLaw d q)) =
      ∫ X, H (T - θ X) (diffusiveStepWalk R (θ X) X) ∂(walkLaw d q) := by
    intro θ hkill
    apply integral_congr_ae
    filter_upwards [ae_walk_start q, ae_step_walk hd q, hkill] with X h0 hstep hk
    rw [diffusiveStepWalk_eq_at_index]
    apply hGH
    apply killed_position_box hL h0 hstep
    intro j hj
    apply hk j
    have hf : (diffusiveTimeIndex R (θ X) : ℝ) ≤ R ^ 2 * (θ X : ℝ) :=
      Nat.floor_le (by positivity)
    have hj' : (j : ℝ) < (diffusiveTimeIndex R (θ X) : ℝ) := by exact_mod_cast hj
    exact hj'.trans_le hf
  ext a
  constructor
  · rintro ⟨θ, hθ, hθT, hkill, rfl⟩
    exact ⟨θ, hθ, hθT, hkill, key θ hkill⟩
  · rintro ⟨θ, hθ, hθT, hkill, rfl⟩
    exact ⟨θ, hθ, hθT, hkill, (key θ hkill).symm⟩

end Sandpile.External.Stopping
