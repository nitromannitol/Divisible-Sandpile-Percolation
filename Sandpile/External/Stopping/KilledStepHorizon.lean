import Sandpile.External.Stopping.KilledStepCompletion

/-!
# Killed step-walk values at arbitrary horizons

The last holding interval of a step walk can extend beyond the final lattice
grid point. Rounding a stop in this interval preserves its position and changes
a continuous-time reward only by its temporal modulus.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Expected rewards of step-walk stopping times bounded by a real horizon and
killed almost surely upon leaving the lattice domain. -/
def killedStepTimePayoffs {d : ℕ} (R : ℝ) (D : Set (Site d)) (x : Site d)
    (T : ℝ) (G : ℝ → Continuum.Space d → ℝ) : Set ℝ :=
  {a | ∃ θ : (ℕ → Site d) → ℝ≥0,
    Continuum.IsBrownianStopping (diffusiveStepWalk R) θ ∧
    (∀ X, (θ X : ℝ) ≤ T) ∧
    (∀ᵐ X ∂(walkLaw d x), ∀ j : ℕ, (j : ℝ) < R ^ 2 * (θ X : ℝ) → X j ∈ D) ∧
    a = ∫ X, G (T - θ X) (diffusiveStepWalk R (θ X) X) ∂(walkLaw d x)}

/-- Bounded rewards give a bounded set of killed step-walk payoffs. -/
theorem bddAbove_killedStepTimePayoffs {d : ℕ} [NeZero d] (R : ℝ) (D : Set (Site d))
    (x : Site d) (T M : ℝ) (G : ℝ → Continuum.Space d → ℝ)
    (hM : ∀ s z, |G s z| ≤ M) : BddAbove (killedStepTimePayoffs R D x T G) := by
  let : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  refine ⟨M, ?_⟩
  rintro a ⟨θ, _, _, _, rfl⟩
  have h := norm_integral_le_of_norm_le_const (μ := walkLaw d x)
    (f := fun X => G (T - θ X) (diffusiveStepWalk R (θ X) X))
    (C := M) (Filter.Eventually.of_forall fun X => by
      simpa only [Real.norm_eq_abs] using hM (T - θ X) (diffusiveStepWalk R (θ X) X))
  exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using h)

/-- Zero is admissible at a nonnegative time horizon. -/
theorem killedStepTimePayoffs_nonempty {d : ℕ} (R : ℝ) (D : Set (Site d))
    (x : Site d) (T : ℝ) (hT : 0 ≤ T) (G : ℝ → Continuum.Space d → ℝ) :
    (killedStepTimePayoffs R D x T G).Nonempty := by
  refine ⟨_, fun _ => 0, Continuum.isBrownianStopping_const _ 0, ?_, ?_, rfl⟩
  · intro X
    simpa using hT
  · filter_upwards with X
    intro j hj
    simp only [NNReal.coe_zero, mul_zero] at hj
    exact (not_lt_of_ge (Nat.cast_nonneg j) hj).elim

/-- A killed lattice payoff is an admissible step-walk payoff when the lattice
horizon is no later than the real horizon. -/
theorem killedSet_subset_killedStepTimePayoffs {d : ℕ} {R : ℝ} (hR : 0 < R)
    (D : Set (Site d)) (N : ℕ) (x : Site d) (T : ℝ)
    (hT : (N : ℝ) / R ^ 2 ≤ T) (G : ℝ → Continuum.Space d → ℝ) :
    killedSet D N x (fun k X => G (T - (k : ℝ) / R ^ 2)
      (Lclt.scaledSite R (X k))) ⊆ killedStepTimePayoffs R D x T G := by
  intro a ha
  have h := killedSet_subset_killedStepPayoffs hR D N x T hT G ha
  obtain ⟨θ, hθ, hθT, _, hkill, ha⟩ := h
  exact ⟨θ, hθ, hθT, Filter.Eventually.of_forall hkill, ha⟩

/-- Rounding a step-walk stop at an arbitrary horizon and truncating the
resulting lattice rule at the first exit does not change its reward by more
than the temporal modulus. -/
theorem killedStepTimePayoff_le_killedStoppingSup {d : ℕ} [NeZero d] {R : ℝ}
    (hR : 0 < R) (D : Set (Site d)) (x : Site d) (T M ε : ℝ)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGm : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hM : ∀ s z, |G s z| ≤ M)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < 1 / R ^ 2 → |G s z - G u z| ≤ ε)
    (hbdd : BddAbove (killedSet D ⌊R ^ 2 * T⌋₊ x (fun k X =>
      G (T - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k)))))
    (a : ℝ) (ha : a ∈ killedStepTimePayoffs R D x T G) :
    a ≤ killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
      G (T - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k))) + ε := by
  obtain ⟨θ, hθ, hθT, hkill, rfl⟩ := ha
  let N := ⌊R ^ 2 * T⌋₊
  let κ : (ℕ → Site d) → ℕ := fun X => diffusiveTimeIndex R (θ X)
  have hκ : IsWalkStopping κ := isWalkStopping_floor_of_diffusiveStepWalk hR θ hθ
  have hκN : ∀ X, κ X ≤ N := by
    intro X
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left (hθT X) (sq_nonneg R))
  let ρ := stopBeforeExit D N κ
  have hρ : IsWalkStopping ρ := isWalkStopping_stopBeforeExit hκ hκN
  have hρN : ∀ X, ρ X ≤ N := stopBeforeExit_le hκN
  have hρkill : ∀ X j, j < ρ X → X j ∈ D := stopBeforeExit_kill hκN
  have hρeq : ρ =ᵐ[walkLaw d x] κ := by
    filter_upwards [hkill] with X hX
    change min (κ X) (exitNat D N X) = κ X
    apply min_eq_left
    by_contra hn
    have hlt : exitNat D N X < κ X := lt_of_not_ge hn
    have hle : exitNat D N X ≤ N := (Nat.le_of_lt hlt).trans (hκN X)
    have hf : (κ X : ℝ) ≤ R ^ 2 * (θ X : ℝ) := Nat.floor_le (by positivity)
    have hj : (exitNat D N X : ℝ) < (κ X : ℝ) := by exact_mod_cast hlt
    exact (notMem_exitNat hle) (hX _ (hj.trans_le hf))
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
      ∫ X, G (T - (ρ X : ℝ) / R ^ 2) (Lclt.scaledSite R (X (ρ X))) ∂(walkLaw d x) := by
    apply integral_congr_ae
    filter_upwards [hρeq] with X hX
    rw [hX]
    rfl
  rw [heq] at hgap
  have hgap' : |(∫ X, G (T - θ X) (diffusiveStepWalk R (θ X) X) ∂(walkLaw d x)) -
      ∫ X, G (T - (ρ X : ℝ) / R ^ 2) (Lclt.scaledSite R (X (ρ X))) ∂(walkLaw d x)| ≤ ε := by
    simpa using hgap
  have hle := le_csSup hbdd ⟨ρ, hρ, hρN, hρkill, rfl⟩
  change (∫ X, G (T - (ρ X : ℝ) / R ^ 2) (Lclt.scaledSite R (X (ρ X)))
    ∂(walkLaw d x)) ≤ killedStoppingSup D N x _ at hle
  linarith [(abs_le.mp hgap').2]

/-- At a real horizon, the killed step-walk value differs from the killed
lattice value by at most the temporal modulus at one grid step. -/
theorem abs_sSup_killedStepTimePayoffs_sub_killedStoppingSup_le {d : ℕ} [NeZero d]
    {R : ℝ} (hR : 0 < R) (D : Set (Site d)) (x : Site d)
    (T M ε : ℝ) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGm : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hM : ∀ s z, |G s z| ≤ M)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < 1 / R ^ 2 → |G s z - G u z| ≤ ε) :
    |sSup (killedStepTimePayoffs R D x T G) -
      killedStoppingSup D ⌊R ^ 2 * T⌋₊ x (fun k X =>
        G (T - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k)))| ≤ ε := by
  let N := ⌊R ^ 2 * T⌋₊
  let F : ℕ → (ℕ → Site d) → ℝ := fun k X =>
    G (T - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k))
  have hgrid : (N : ℝ) / R ^ 2 ≤ T := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).2
    have hfloor := Nat.floor_le (mul_nonneg (sq_nonneg R) hT)
    change (N : ℝ) ≤ R ^ 2 * T at hfloor
    nlinarith
  have hsub : killedSet D N x F ⊆ killedStepTimePayoffs R D x T G :=
    killedSet_subset_killedStepTimePayoffs hR D N x T hgrid G
  have hstep := bddAbove_killedStepTimePayoffs R D x T M G hM
  have hlattice : BddAbove (killedSet D N x F) := hstep.mono hsub
  have hupper : sSup (killedStepTimePayoffs R D x T G) ≤ killedStoppingSup D N x F + ε := by
    refine csSup_le (killedStepTimePayoffs_nonempty R D x T hT G) ?_
    intro a ha
    exact killedStepTimePayoff_le_killedStoppingSup hR D x T M ε G hGm hM hG hlattice a ha
  have hlower : killedStoppingSup D N x F ≤ sSup (killedStepTimePayoffs R D x T G) := by
    apply csSup_le (killedSet_nonempty D N x F)
    intro a ha
    exact le_csSup hstep (hsub ha)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Sandpile.External.Stopping
