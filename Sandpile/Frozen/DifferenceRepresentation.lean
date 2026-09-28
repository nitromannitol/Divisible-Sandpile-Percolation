import Sandpile.External.BPSHProved
import Sandpile.Support.Stopped

/-!
# The odometer minus the membrane as an optimal-stopping value

This file proves the frozen statement of `lem:difference-representation` (`sandpile.tex:928-936`):
for every fixed scenery `ζ`, dimension `d ≥ 1`, time `t`, and site `x`, the difference
`u_t(x) - V_t(x)` between the odometer and the membrane field equals the supremum over stopping
times `τ ≤ t` of the walk of `E_x[-V_{t-τ}(X_τ)]`, written here as `Sandpile.stoppingSup t x` for
the payoff `(k, X) ↦ -V_{t-k}(X_k)`. The proof rewrites both sides through the optimal-stopping
representation of the odometer itself, `Sandpile.External.optimalStopping`, which this repository
proves unconditionally rather than carrying as a cited hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.difference_representation
    (d : ℕ) (hd : 1 ≤ d) (ζ : Sandpile.Site d → ℝ) (t : ℕ) (x : Sandpile.Site d) :
    Sandpile.odometerOf ζ t x - Sandpile.membrane ζ t x =
      Sandpile.stoppingSup t x (fun k X => -(Sandpile.membrane ζ (t - k) (X k)))
-- FROZEN-STATEMENT-END
:= by
  rw [(Sandpile.External.optimalStopping d hd ζ t x).1]
  show sSup {a : ℝ | ∃ τ : (ℕ → Sandpile.Site d) → ℕ, Sandpile.IsWalkStopping τ ∧
      (∀ X, τ X ≤ t) ∧ a = ∫ X, Sandpile.sceneryPartialSum ζ (τ X) X
        ∂(Sandpile.walkLaw d x)} - Sandpile.membrane ζ t x = _
  set A : Set ℝ := {a : ℝ | ∃ τ : (ℕ → Sandpile.Site d) → ℕ, Sandpile.IsWalkStopping τ ∧
      (∀ X, τ X ≤ t) ∧ a = ∫ X, Sandpile.sceneryPartialSum ζ (τ X) X
        ∂(Sandpile.walkLaw d x)} with hAdef
  have hAne : A.Nonempty :=
    ⟨_, ⟨fun _ => 0, Sandpile.isWalkStopping_zero, fun _ => Nat.zero_le t, rfl⟩⟩
  have hAbdd : BddAbove A := by
    refine ⟨t * Sandpile.sceneryBound x t ζ, ?_⟩
    rintro a ⟨τ, hτ, hτt, rfl⟩
    exact le_trans (le_abs_self _)
      (Sandpile.abs_integral_stoppedScenery_le hd x ζ t hτ hτt)
  have hB : {a : ℝ | ∃ τ : (ℕ → Sandpile.Site d) → ℕ, Sandpile.IsWalkStopping τ ∧
      (∀ X, τ X ≤ t) ∧ a = ∫ X, -(Sandpile.membrane ζ (t - τ X) (X (τ X)))
        ∂(Sandpile.walkLaw d x)} = (fun a => a - Sandpile.membrane ζ t x) '' A := by
    ext a
    constructor
    · rintro ⟨τ, hτ, hτt, rfl⟩
      exact ⟨_, ⟨τ, hτ, hτt, rfl⟩,
        (Sandpile.integral_neg_stoppedMembrane hd x ζ t hτ hτt).symm⟩
    · rintro ⟨b, ⟨τ, hτ, hτt, rfl⟩, rfl⟩
      exact ⟨τ, hτ, hτt, (Sandpile.integral_neg_stoppedMembrane hd x ζ t hτ hτt).symm⟩
  show _ = sSup {a : ℝ | ∃ τ : (ℕ → Sandpile.Site d) → ℕ, Sandpile.IsWalkStopping τ ∧
      (∀ X, τ X ≤ t) ∧ a = ∫ X, -(Sandpile.membrane ζ (t - τ X) (X (τ X)))
        ∂(Sandpile.walkLaw d x)}
  rw [hB, Sandpile.sSup_image_sub A hAne hAbdd]
