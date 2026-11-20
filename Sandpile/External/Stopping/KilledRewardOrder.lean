import Sandpile.External.Stopping.LatticeHorizonComparison

/-!
# Order bounds for killed stopping values

Pointwise order of integrable rewards gives the same order of their stopping
values, with constants preserved under the probability law.
-/

open MeasureTheory Set

namespace Sandpile.External.Stopping

/-- A pointwise upper bound by a reward plus a constant gives the corresponding
bound on the killed stopping values. -/
theorem killedStoppingSup_le_of_reward_le_add {d : ℕ} (hd : 1 ≤ d)
    (D : Set (Site d)) (n : ℕ) (x : Site d)
    (F G : ℕ → (ℕ → Site d) → ℝ) (C : ℝ)
    (hbddG : BddAbove (killedSet D n x G))
    (hF : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      Integrable (fun X => F (τ X) X) (walkLaw d x))
    (hG : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      Integrable (fun X => G (τ X) X) (walkLaw d x))
    (hFG : ∀ k ≤ n, ∀ X, F k X ≤ G k X + C) :
    killedStoppingSup D n x F ≤ killedStoppingSup D n x G + C := by
  let : NeZero d := ⟨by omega⟩
  let : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  apply csSup_le (killedSet_nonempty D n x F)
  rintro a ⟨τ, hτ, hτn, hkill, rfl⟩
  have hi := integral_mono_ae (hF τ hτ hτn) ((hG τ hτ hτn).add (integrable_const C))
    (Filter.Eventually.of_forall fun X => hFG (τ X) (hτn X) X)
  have hv : (∫ X, G (τ X) X ∂(walkLaw d x)) ≤ killedStoppingSup D n x G :=
    le_csSup hbddG ⟨τ, hτ, hτn, hkill, rfl⟩
  change (∫ X, F (τ X) X ∂(walkLaw d x)) ≤
    ∫ X, G (τ X) X + C ∂(walkLaw d x) at hi
  rw [integral_add (hG τ hτ hτn) (integrable_const C)] at hi
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hi
  linarith

/-- The corresponding comparison for unrestricted walk stopping values. -/
theorem stoppingSup_le_of_reward_le_add {d : ℕ} (hd : 1 ≤ d)
    (n : ℕ) (x : Site d) (F G : ℕ → (ℕ → Site d) → ℝ) (C : ℝ)
    (hbddG : BddAbove (killedSet Set.univ n x G))
    (hF : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      Integrable (fun X => F (τ X) X) (walkLaw d x))
    (hG : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      Integrable (fun X => G (τ X) X) (walkLaw d x))
    (hFG : ∀ k ≤ n, ∀ X, F k X ≤ G k X + C) :
    stoppingSup n x F ≤ stoppingSup n x G + C := by
  simpa only [killedStoppingSup_univ] using
    killedStoppingSup_le_of_reward_le_add hd Set.univ n x F G C hbddG hF hG hFG

end Sandpile.External.Stopping
