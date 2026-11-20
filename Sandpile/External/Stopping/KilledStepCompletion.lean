import Sandpile.External.Stopping.KilledStepReward
import Sandpile.Support.ExplBallExit

/-!
# Almost-sure killing for diffusive step walks

A step-walk stopping time that respects a lattice domain almost surely can be
stopped at the lattice exit. The resulting stopping time respects the domain
on every path and agrees with the original stopping time almost surely.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The lattice exit, truncated at the horizon, is a step-walk stopping time
when expressed in diffusive time. -/
theorem isBrownianStopping_diffusiveExit {d : ℕ} {R : ℝ} (hR : 0 < R)
    (D : Set (Site d)) (N : ℕ) :
    Continuum.IsBrownianStopping (diffusiveStepWalk R)
      (walkStopToDiffusiveTime R hR (stopBeforeExit D N (fun _ => N))) := by
  apply isBrownianStopping_diffusiveStepWalk_of_walkStopping hR
  exact isWalkStopping_stopBeforeExit (by intro k X Y hXY hk; exact hk)
    (fun _ => le_rfl)

/-- Truncating a step-walk stop at the lattice exit gives a pointwise killed
stop without changing it on paths that already respect the domain. -/
theorem exists_pointwise_killed_stepStop {d : ℕ} [NeZero d] {R : ℝ} (hR : 0 < R)
    (D : Set (Site d)) (N : ℕ) (x : Site d) (T : ℝ)
    (θ : (ℕ → Site d) → ℝ≥0)
    (hθ : Continuum.IsBrownianStopping (diffusiveStepWalk R) θ)
    (hθT : ∀ X, (θ X : ℝ) ≤ T)
    (hθN : ∀ X, θ X ≤ (N : ℝ≥0) / ⟨R ^ 2, sq_nonneg R⟩)
    (hkill : ∀ᵐ X ∂(walkLaw d x), ∀ j : ℕ,
      (j : ℝ) < R ^ 2 * (θ X : ℝ) → X j ∈ D) :
    ∃ σ : (ℕ → Site d) → ℝ≥0,
      Continuum.IsBrownianStopping (diffusiveStepWalk R) σ ∧
      (∀ X, (σ X : ℝ) ≤ T) ∧
      (∀ X, σ X ≤ (N : ℝ≥0) / ⟨R ^ 2, sq_nonneg R⟩) ∧
      (∀ X (j : ℕ), (j : ℝ) < R ^ 2 * (σ X : ℝ) → X j ∈ D) ∧
      σ =ᵐ[walkLaw d x] θ := by
  let κ : (ℕ → Site d) → ℕ := stopBeforeExit D N (fun _ => N)
  let ξ := walkStopToDiffusiveTime R hR κ
  let σ : (ℕ → Site d) → ℝ≥0 := fun X => min (θ X) (ξ X)
  have hκN : ∀ X, κ X ≤ N := stopBeforeExit_le (fun _ => le_rfl)
  have hκkill : ∀ X j, j < κ X → X j ∈ D := stopBeforeExit_kill (fun _ => le_rfl)
  have hξ : ∀ X, R ^ 2 * (ξ X : ℝ) = (κ X : ℝ) := by
    intro X
    change R ^ 2 * ((κ X : ℝ) / R ^ 2) = (κ X : ℝ)
    exact mul_div_cancel₀ _ (pow_ne_zero 2 hR.ne')
  have hσ : Continuum.IsBrownianStopping (diffusiveStepWalk R) σ :=
    Continuum.isBrownianStopping_min hθ (isBrownianStopping_diffusiveExit hR D N)
  refine ⟨σ, hσ, ?_, ?_, ?_, ?_⟩
  · intro X
    have hs : (σ X : ℝ) ≤ θ X := by exact_mod_cast min_le_left (θ X) (ξ X)
    exact hs.trans (hθT X)
  · intro X
    exact (min_le_left (θ X) (ξ X)).trans (hθN X)
  · intro X j hj
    apply hκkill X j
    have hs : (σ X : ℝ) ≤ ξ X := by exact_mod_cast min_le_right (θ X) (ξ X)
    have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg R)
    rw [hξ X] at hm
    exact_mod_cast hj.trans_le hm
  · filter_upwards [hkill] with X hX
    have hs : θ X ≤ ξ X := by
      by_contra hn
      have hlt : (ξ X : ℝ) < θ X := by exact_mod_cast (lt_of_not_ge hn)
      have hmul : (κ X : ℝ) < R ^ 2 * (θ X : ℝ) := by
        rw [← hξ X]
        exact mul_lt_mul_of_pos_left hlt (sq_pos_of_pos hR)
      have hin := hX (κ X) hmul
      have hθN' : (θ X : ℝ) ≤ (N : ℝ) / R ^ 2 := by exact_mod_cast hθN X
      have hltN : κ X < N := by
        have hn : (κ X : ℝ) < N := by
          have hmulN := mul_le_mul_of_nonneg_left hθN' (sq_nonneg R)
          have heq : R ^ 2 * ((N : ℝ) / R ^ 2) = N :=
            mul_div_cancel₀ _ (pow_ne_zero 2 hR.ne')
          rw [heq] at hmulN
          linarith
        exact_mod_cast hn
      have hexit : exitNat D N X = κ X := by
        change min N (exitNat D N X) < N at hltN
        change exitNat D N X = min N (exitNat D N X)
        exact (min_eq_right (by omega)).symm
      have hout : X (κ X) ∉ D := by
        rw [← hexit]
        exact notMem_exitNat (by rw [hexit]; omega)
      exact hout hin
    exact min_eq_left hs

/-- Expected rewards of step-walk stops which respect the lattice domain
almost surely before stopping. -/
def killedStepPayoffsAE {d : ℕ} (R : ℝ) (D : Set (Site d)) (N : ℕ) (x : Site d)
    (T : ℝ) (G : ℝ → Continuum.Space d → ℝ) : Set ℝ :=
  {a | ∃ θ : (ℕ → Site d) → ℝ≥0,
    Continuum.IsBrownianStopping (diffusiveStepWalk R) θ ∧
    (∀ X, (θ X : ℝ) ≤ T) ∧
    (∀ X, θ X ≤ (N : ℝ≥0) / ⟨R ^ 2, sq_nonneg R⟩) ∧
    (∀ᵐ X ∂(walkLaw d x), ∀ j : ℕ, (j : ℝ) < R ^ 2 * (θ X : ℝ) → X j ∈ D) ∧
    a = ∫ X, G (T - θ X) (diffusiveStepWalk R (θ X) X) ∂(walkLaw d x)}

/-- Pointwise and almost-sure killing give the same set of step-walk
payoffs. -/
theorem killedStepPayoffsAE_eq_killedStepPayoffs {d : ℕ} [NeZero d]
    {R : ℝ} (hR : 0 < R) (D : Set (Site d)) (N : ℕ) (x : Site d)
    (T : ℝ) (G : ℝ → Continuum.Space d → ℝ) :
    killedStepPayoffsAE R D N x T G = killedStepPayoffs R D N x T G := by
  ext a
  constructor
  · rintro ⟨θ, hθ, hθT, hθN, hkill, rfl⟩
    obtain ⟨σ, hσ, hσT, hσN, hσkill, hσeq⟩ :=
      exists_pointwise_killed_stepStop hR D N x T θ hθ hθT hθN hkill
    refine ⟨σ, hσ, hσT, hσN, hσkill, ?_⟩
    apply integral_congr_ae
    filter_upwards [hσeq] with X hX
    rw [hX]
  · rintro ⟨θ, hθ, hθT, hθN, hkill, rfl⟩
    refine ⟨θ, hθ, hθT, hθN, ?_, rfl⟩
    exact Filter.Eventually.of_forall hkill

end Sandpile.External.Stopping
