import Sandpile.External.Stopping.BoundedRoundedReward
import Sandpile.External.Stopping.DiffusiveWalkStopping
import Sandpile.Support.KillRep

/-!
# Killed stopping values for the diffusive step walk

Rounding a step-walk stopping time down to the preceding lattice time preserves
admissibility before exit and changes a bounded reward by at most its temporal
modulus. Conversely, lattice stopping times embed at their exact grid times.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Expected rewards of diffusive step-walk stops which do not continue after
leaving the lattice domain. -/
def killedStepPayoffs {d : ℕ} (R : ℝ) (D : Set (Site d)) (N : ℕ) (x : Site d)
    (T : ℝ) (G : ℝ → Continuum.Space d → ℝ) : Set ℝ :=
  {a | ∃ θ : (ℕ → Site d) → ℝ≥0,
    Continuum.IsBrownianStopping (diffusiveStepWalk R) θ ∧
    (∀ X, (θ X : ℝ) ≤ T) ∧
    (∀ X, θ X ≤ (N : ℝ≥0) / ⟨R ^ 2, sq_nonneg R⟩) ∧
    (∀ X (j : ℕ), (j : ℝ) < R ^ 2 * (θ X : ℝ) → X j ∈ D) ∧
    a = ∫ X, G (T - θ X) (diffusiveStepWalk R (θ X) X) ∂(walkLaw d x)}

/-- Bounded rewards give a bounded set of killed step-walk payoffs. -/
theorem bddAbove_killedStepPayoffs {d : ℕ} [NeZero d] (R : ℝ) (D : Set (Site d))
    (N : ℕ) (x : Site d) (T M : ℝ) (G : ℝ → Continuum.Space d → ℝ)
    (hM : ∀ s z, |G s z| ≤ M) : BddAbove (killedStepPayoffs R D N x T G) := by
  let : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  refine ⟨M, ?_⟩
  rintro a ⟨θ, _, _, _, _, rfl⟩
  have h := norm_integral_le_of_norm_le_const (μ := walkLaw d x)
    (f := fun X => G (T - θ X) (diffusiveStepWalk R (θ X) X))
    (C := M) (Filter.Eventually.of_forall fun X => by
      simpa only [Real.norm_eq_abs] using hM (T - θ X) (diffusiveStepWalk R (θ X) X))
  exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using h)

/-- Zero is an admissible killed step-walk stopping time. -/
theorem killedStepPayoffs_nonempty {d : ℕ} (R : ℝ) (D : Set (Site d))
    (N : ℕ) (x : Site d) (T : ℝ) (hT : 0 ≤ T)
    (G : ℝ → Continuum.Space d → ℝ) : (killedStepPayoffs R D N x T G).Nonempty := by
  refine ⟨_, fun _ => 0, Continuum.isBrownianStopping_const _ 0, ?_, ?_, ?_, rfl⟩
  · intro X
    simpa using hT
  · intro X
    exact zero_le
  · intro X j hj
    simp only [NNReal.coe_zero, mul_zero] at hj
    exact (not_lt_of_ge (Nat.cast_nonneg j) hj).elim

/-- A killed step-walk stop rounds to a killed lattice stop. Its expected
reward changes by at most the temporal modulus. -/
theorem killedStepPayoff_le_killedStoppingSup {d : ℕ} [NeZero d] {R : ℝ} (hR : 0 < R)
    (D : Set (Site d)) (N : ℕ) (x : Site d) (T M ε : ℝ)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGm : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hM : ∀ s z, |G s z| ≤ M)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < 1 / R ^ 2 → |G s z - G u z| ≤ ε)
    (hbdd : BddAbove (killedSet D N x (fun k X =>
      G (T - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k)))))
    (a : ℝ) (ha : a ∈ killedStepPayoffs R D N x T G) :
    a ≤ killedStoppingSup D N x (fun k X =>
      G (T - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k))) + ε := by
  obtain ⟨θ, hθ, hθT, hθN, hkill, rfl⟩ := ha
  let κ : (ℕ → Site d) → ℕ := fun X => diffusiveTimeIndex R (θ X)
  have hκ : IsWalkStopping κ := isWalkStopping_floor_of_diffusiveStepWalk hR θ hθ
  have hκN : ∀ X, κ X ≤ N := fun X => diffusiveTimeIndex_le_of_le_grid hR (θ X) N (hθN X)
  have hκkill : ∀ X j, j < κ X → X j ∈ D := by
    intro X j hj
    apply hkill X j
    have hf : (κ X : ℝ) ≤ R ^ 2 * (θ X : ℝ) := Nat.floor_le (by positivity)
    have hj' : (j : ℝ) < (κ X : ℝ) := by exact_mod_cast hj
    linarith
  have hI₁ := integrable_diffusiveStepWalk_stopped_reward R x T M G hGm hM θ hθ
  have hI₂ := integrable_diffusiveStepWalk_rounded_reward hR x T M G hGm hM θ hθ
  have hpoint : ∀ᵐ X ∂(walkLaw d x),
      ‖G (T - θ X) (diffusiveStepWalk R (θ X) X) -
        G (T - roundDiffusiveTime R hR (θ X))
          (Lclt.scaledSite R (X (κ X)))‖ ≤ ε := by
    filter_upwards with X
    simpa only [Real.norm_eq_abs, κ] using
      abs_stepWalk_reward_sub_rounded_le hR T ε G (θ X) (hθT X) X hG
  let : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  have hgap := norm_integral_le_of_norm_le_const hpoint
  rw [integral_sub hI₁ hI₂, Real.norm_eq_abs] at hgap
  have heq : (∫ X, G (T - roundDiffusiveTime R hR (θ X))
        (Lclt.scaledSite R (X (κ X))) ∂(walkLaw d x)) =
      ∫ X, G (T - (κ X : ℝ) / R ^ 2) (Lclt.scaledSite R (X (κ X))) ∂(walkLaw d x) := by
    rfl
  rw [heq] at hgap
  have hgap' : |(∫ X, G (T - θ X) (diffusiveStepWalk R (θ X) X) ∂(walkLaw d x)) -
      ∫ X, G (T - (κ X : ℝ) / R ^ 2) (Lclt.scaledSite R (X (κ X))) ∂(walkLaw d x)| ≤ ε := by
    simpa using hgap
  have hle := le_csSup hbdd ⟨κ, hκ, hκN, hκkill, rfl⟩
  change (∫ X, G (T - (κ X : ℝ) / R ^ 2) (Lclt.scaledSite R (X (κ X)))
    ∂(walkLaw d x)) ≤ killedStoppingSup D N x _ at hle
  linarith [(abs_le.mp hgap').2]

/-- A killed lattice stop is a killed step-walk stop at its diffusive grid
time, with the same expected reward. -/
theorem killedSet_subset_killedStepPayoffs {d : ℕ} {R : ℝ} (hR : 0 < R)
    (D : Set (Site d)) (N : ℕ) (x : Site d) (T : ℝ)
    (hT : (N : ℝ) / R ^ 2 ≤ T) (G : ℝ → Continuum.Space d → ℝ) :
    killedSet D N x (fun k X => G (T - (k : ℝ) / R ^ 2)
      (Lclt.scaledSite R (X k))) ⊆ killedStepPayoffs R D N x T G := by
  rintro a ⟨τ, hτ, hτN, hkill, rfl⟩
  refine ⟨walkStopToDiffusiveTime R hR τ,
    isBrownianStopping_diffusiveStepWalk_of_walkStopping hR τ hτ, ?_, ?_, ?_, ?_⟩
  · intro X
    have hdiv : (τ X : ℝ) / R ^ 2 ≤ (N : ℝ) / R ^ 2 :=
      div_le_div_of_nonneg_right (by exact_mod_cast hτN X) (sq_nonneg R)
    exact hdiv.trans hT
  · intro X
    exact div_le_div_of_nonneg_right (by exact_mod_cast hτN X) (zero_le)
  · intro X j hj
    have heq : R ^ 2 * (walkStopToDiffusiveTime R hR τ X : ℝ) = τ X := by
      change R ^ 2 * ((τ X : ℝ) / R ^ 2) = (τ X : ℝ)
      exact mul_div_cancel₀ _ (pow_ne_zero 2 hR.ne')
    rw [heq] at hj
    apply hkill X j
    exact_mod_cast hj
  · apply integral_congr_ae
    filter_upwards with X
    rw [diffusiveStepWalk_walkStopToDiffusiveTime hR]
    rfl

/-- The killed step-walk value lies within the temporal modulus of the killed
lattice value, when the lattice horizon is contained in the time horizon. -/
theorem abs_sSup_killedStepPayoffs_sub_killedStoppingSup_le {d : ℕ} [NeZero d]
    {R : ℝ} (hR : 0 < R) (D : Set (Site d)) (N : ℕ) (x : Site d)
    (T M ε : ℝ) (hT : (N : ℝ) / R ^ 2 ≤ T) (hε : 0 ≤ ε)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGm : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hM : ∀ s z, |G s z| ≤ M)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < 1 / R ^ 2 → |G s z - G u z| ≤ ε) :
    |sSup (killedStepPayoffs R D N x T G) -
      killedStoppingSup D N x (fun k X => G (T - (k : ℝ) / R ^ 2)
        (Lclt.scaledSite R (X k)))| ≤ ε := by
  let F : ℕ → (ℕ → Site d) → ℝ := fun k X =>
    G (T - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k))
  have hsub : killedSet D N x F ⊆ killedStepPayoffs R D N x T G :=
    killedSet_subset_killedStepPayoffs hR D N x T hT G
  have hstep := bddAbove_killedStepPayoffs R D N x T M G hM
  have hlattice : BddAbove (killedSet D N x F) := hstep.mono hsub
  have hT0 : 0 ≤ T := (div_nonneg (Nat.cast_nonneg N) (sq_nonneg R)).trans hT
  have hupper : sSup (killedStepPayoffs R D N x T G) ≤ killedStoppingSup D N x F + ε := by
    refine csSup_le (killedStepPayoffs_nonempty R D N x T hT0 G) ?_
    intro a ha
    exact killedStepPayoff_le_killedStoppingSup hR D N x T M ε G hGm hM hG hlattice a ha
  have hlower : killedStoppingSup D N x F ≤ sSup (killedStepPayoffs R D N x T G) := by
    apply csSup_le (killedSet_nonempty D N x F)
    intro a ha
    exact le_csSup hstep (hsub ha)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Sandpile.External.Stopping
