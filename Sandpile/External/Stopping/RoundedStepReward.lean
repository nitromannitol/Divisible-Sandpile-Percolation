import Sandpile.External.Stopping.DiffusiveRounding

/-!
# Time-dependent rewards at rounded step-walk stops

Rounding a diffusive step-walk time down leaves its spatial position unchanged.
A uniform temporal modulus therefore bounds the change in a reward by the
modulus at one diffusive lattice step.
-/

open Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- If a diffusive time is no later than the `N`th lattice time, its floor
index is at most `N`. -/
theorem diffusiveTimeIndex_le_of_le_grid {R : ℝ} (hR : 0 < R) (t : ℝ≥0) (N : ℕ)
    (ht : t ≤ (N : ℝ≥0) / ⟨R ^ 2, sq_nonneg R⟩) : diffusiveTimeIndex R t ≤ N := by
  have hc : 0 < R ^ 2 := sq_pos_of_pos hR
  have ht' : (t : ℝ) ≤ (N : ℝ) / R ^ 2 := by
    have h := NNReal.coe_le_coe.mpr ht
    change (t : ℝ) ≤ (N : ℝ) / R ^ 2 at h
    exact h
  have hm : R ^ 2 * (t : ℝ) ≤ (N : ℝ) := by
    have h := (le_div_iff₀ hc).1 ht'
    nlinarith
  have hf := Nat.floor_mono hm
  simpa only [diffusiveTimeIndex, Nat.floor_natCast] using hf

/-- A uniform temporal modulus controls the reward change caused by rounding a
step-walk time down to its preceding lattice time. -/
theorem abs_stepWalk_reward_sub_rounded_le {d : ℕ} {R : ℝ} (hR : 0 < R)
    (T ε : ℝ) (G : ℝ → Continuum.Space d → ℝ) (t : ℝ≥0) (ht : (t : ℝ) ≤ T)
    (X : ℕ → Site d)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < 1 / R ^ 2 → |G s z - G u z| ≤ ε) :
    |G (T - t) (diffusiveStepWalk R t X) -
      G (T - roundDiffusiveTime R hR t)
        (Lclt.scaledSite R (X (diffusiveTimeIndex R t)))| ≤ ε := by
  have hround := roundDiffusiveTime_bounds hR t
  have hround0 : 0 ≤ (roundDiffusiveTime R hR t : ℝ) := (roundDiffusiveTime R hR t).property
  have hs : T - (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [t.property]⟩
  have hu : T - (roundDiffusiveTime R hR t : ℝ) ∈ Icc (0 : ℝ) T :=
    ⟨by linarith [hround.1], by linarith⟩
  have habs : |(T - (t : ℝ)) - (T - (roundDiffusiveTime R hR t : ℝ))| < 1 / R ^ 2 := by
    rw [abs_of_nonpos (by linarith [hround.1])]
    linarith [hround.2]
  rw [diffusiveStepWalk_eq_at_index]
  exact hG _ hs _ hu _ habs

end Sandpile.External.Stopping
