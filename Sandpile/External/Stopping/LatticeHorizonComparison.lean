import Sandpile.External.Stopping.KilledGridReward
import Sandpile.External.Stopping.UnkilledStepValue

/-!
# Lattice stopping values at different horizons

Increasing the horizon enlarges the admissible set of stopping times. A
uniform reward error then compares values with different horizons and rewards,
both with and without killing.
-/

open MeasureTheory Set

namespace Sandpile.External.Stopping

/-- A larger horizon gives a larger killed value for the same reward, provided
the larger payoff set is bounded above. -/
theorem killedStoppingSup_mono_horizon {d : ℕ} (D : Set (Site d))
    {m n : ℕ} (hmn : m ≤ n) (x : Site d) (F : ℕ → (ℕ → Site d) → ℝ)
    (hbdd : BddAbove (killedSet D n x F)) :
    killedStoppingSup D m x F ≤ killedStoppingSup D n x F := by
  apply csSup_le (killedSet_nonempty D m x F)
  rintro a ⟨τ, hτ, hτm, hkill, rfl⟩
  apply le_csSup hbdd
  exact ⟨τ, hτ, fun X => (hτm X).trans hmn, hkill, rfl⟩

/-- If the reward is uniformly close at times allowed by the smaller horizon,
the corresponding killed values differ by at most that error in the monotone
direction. -/
theorem killedStoppingSup_le_of_horizon_reward {d : ℕ} (hd : 1 ≤ d)
    (D : Set (Site d)) {m n : ℕ} (hmn : m ≤ n) (x : Site d)
    (F G : ℕ → (ℕ → Site d) → ℝ) (ε : ℝ)
    (hbddF : BddAbove (killedSet D m x F))
    (hbddG : BddAbove (killedSet D n x G))
    (hF : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ m) →
      Integrable (fun X => F (τ X) X) (walkLaw d x))
    (hG : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ m) →
      Integrable (fun X => G (τ X) X) (walkLaw d x))
    (hFG : ∀ k ≤ m, ∀ X, |F k X - G k X| ≤ ε) :
    killedStoppingSup D m x F ≤ killedStoppingSup D n x G + ε := by
  have hbddGm : BddAbove (killedSet D m x G) := by
    obtain ⟨C, hC⟩ := hbddG
    refine ⟨C, ?_⟩
    rintro a ⟨τ, hτ, hτm, hkill, rfl⟩
    exact hC ⟨τ, hτ, fun X => (hτm X).trans hmn, hkill, rfl⟩
  have hclose := abs_killedStoppingSup_sub_le_of_reward hd D m x F G ε
    hbddF hbddGm hF hG hFG
  have hmono := killedStoppingSup_mono_horizon D hmn x G hbddG
  linarith [(abs_le.mp hclose).2]

/-- The corresponding comparison for unrestricted lattice stopping. -/
theorem stoppingSup_le_of_horizon_reward {d : ℕ} (hd : 1 ≤ d)
    {m n : ℕ} (hmn : m ≤ n) (x : Site d)
    (F G : ℕ → (ℕ → Site d) → ℝ) (ε : ℝ)
    (hbddF : BddAbove (killedSet Set.univ m x F))
    (hbddG : BddAbove (killedSet Set.univ n x G))
    (hF : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ m) →
      Integrable (fun X => F (τ X) X) (walkLaw d x))
    (hG : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ m) →
      Integrable (fun X => G (τ X) X) (walkLaw d x))
    (hFG : ∀ k ≤ m, ∀ X, |F k X - G k X| ≤ ε) :
    stoppingSup m x F ≤ stoppingSup n x G + ε := by
  simpa only [killedStoppingSup_univ] using
    killedStoppingSup_le_of_horizon_reward hd Set.univ hmn x F G ε
      hbddF hbddG hF hG hFG

/-- For bounded rewards, a uniform temporal modulus controls the increase in
the grid-horizon reward when the admissible horizon is enlarged. -/
theorem killedGridReward_le_of_horizon {d : ℕ} [NeZero d]
    {R : ℝ} (hR : 0 < R) (D : Set (Site d)) {m n : ℕ} (hmn : m ≤ n)
    (x : Site d) (G : ℝ → Continuum.Space d → ℝ) (M ε : ℝ)
    (hG : ∀ s z, |G s z| ≤ M)
    (hmod : ∀ s ∈ Icc (0 : ℝ) ((n : ℝ) / R ^ 2),
      ∀ u ∈ Icc (0 : ℝ) ((n : ℝ) / R ^ 2), ∀ z,
        |s - u| ≤ ((n : ℝ) - m) / R ^ 2 → |G s z - G u z| ≤ ε) :
    killedStoppingSup D m x (fun k X =>
        G (((m : ℝ) - k) / R ^ 2) (Lclt.scaledSite R (X k))) ≤
      killedStoppingSup D n x (fun k X =>
        G (((n : ℝ) - k) / R ^ 2) (Lclt.scaledSite R (X k))) + ε := by
  let A : ℝ := (m : ℝ) / R ^ 2
  let B : ℝ := (n : ℝ) / R ^ 2
  let F : ℕ → (ℕ → Site d) → ℝ := fun k X =>
    G (A - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k))
  let H : ℕ → (ℕ → Site d) → ℝ := fun k X =>
    G (B - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k))
  have hpos : 0 < R ^ 2 := sq_pos_of_pos hR
  have hAB : A ≤ B := div_le_div_of_nonneg_right (by exact_mod_cast hmn) hpos.le
  have hb := killedStoppingSup_le_of_horizon_reward
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)) D hmn x F H ε
    (bddAbove_killedSet_shiftedReward R D x m A M G hG)
    (bddAbove_killedSet_shiftedReward R D x n B M G hG)
    (fun τ hτ hτm => integrable_stopped_shiftedReward R x m A M G hG hτ hτm)
    (fun τ hτ hτm => integrable_stopped_shiftedReward R x m B M G hG hτ hτm) (by
      intro k hk X
      have hkA : (k : ℝ) / R ^ 2 ≤ A :=
        div_le_div_of_nonneg_right (by exact_mod_cast hk) hpos.le
      have hk0 : 0 ≤ (k : ℝ) / R ^ 2 := div_nonneg (Nat.cast_nonneg _) hpos.le
      have hA : A - (k : ℝ) / R ^ 2 ∈ Icc (0 : ℝ) B := ⟨by linarith, by linarith⟩
      have hB : B - (k : ℝ) / R ^ 2 ∈ Icc (0 : ℝ) B := ⟨by linarith, by linarith⟩
      have hdiff : |(A - (k : ℝ) / R ^ 2) - (B - (k : ℝ) / R ^ 2)| ≤
          ((n : ℝ) - m) / R ^ 2 := by
        rw [show (A - (k : ℝ) / R ^ 2) - (B - (k : ℝ) / R ^ 2) = A - B by ring,
          abs_of_nonpos (sub_nonpos.mpr hAB)]
        dsimp [A, B]
        rw [sub_div]
        linarith
      exact hmod _ hA _ hB _ hdiff)
  simpa only [F, H, A, B, ← sub_div] using hb

/-- The grid-horizon comparison also holds without killing. -/
theorem gridReward_le_of_horizon {d : ℕ} [NeZero d]
    {R : ℝ} (hR : 0 < R) {m n : ℕ} (hmn : m ≤ n)
    (x : Site d) (G : ℝ → Continuum.Space d → ℝ) (M ε : ℝ)
    (hG : ∀ s z, |G s z| ≤ M)
    (hmod : ∀ s ∈ Icc (0 : ℝ) ((n : ℝ) / R ^ 2),
      ∀ u ∈ Icc (0 : ℝ) ((n : ℝ) / R ^ 2), ∀ z,
        |s - u| ≤ ((n : ℝ) - m) / R ^ 2 → |G s z - G u z| ≤ ε) :
    stoppingSup m x (fun k X =>
        G (((m : ℝ) - k) / R ^ 2) (Lclt.scaledSite R (X k))) ≤
      stoppingSup n x (fun k X =>
        G (((n : ℝ) - k) / R ^ 2) (Lclt.scaledSite R (X k))) + ε := by
  simpa only [killedStoppingSup_univ] using
    killedGridReward_le_of_horizon hR Set.univ hmn x G M ε hG hmod

end Sandpile.External.Stopping
