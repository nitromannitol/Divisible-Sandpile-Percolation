import Sandpile.External.LocalCLT
import Sandpile.External.Stopping.GridStopping

/-!
# Linear interpolation of the lattice walk

The rescaled walk is linearly interpolated between successive lattice times.
At each grid time its history is determined by the walk positions up to that
time, as needed for stopping-time arguments.
-/

open scoped NNReal

namespace Sandpile.External.Stopping

/-- Linear interpolation of a rescaled walk, in units of one lattice step. -/
noncomputable def linearWalk {d : ℕ} (R : ℝ) (s : ℝ≥0) (X : ℕ → Site d) :
    Continuum.Space d :=
  let n := ⌊(s : ℝ)⌋₊
  let a := (s : ℝ) - n
  (1 - a) • Lclt.scaledSite R (X n) + a • Lclt.scaledSite R (X (n + 1))

/-- At a lattice time the interpolation equals the scaled walk position. -/
@[simp] theorem linearWalk_nat {d : ℕ} (R : ℝ) (k : ℕ) (X : ℕ → Site d) :
    linearWalk R k X = Lclt.scaledSite R (X k) := by
  simp [linearWalk]

/-- The interpolated walk through a lattice time is determined by the discrete
walk through that time. -/
theorem linearWalk_grid_causal {d : ℕ} (R : ℝ) (k : ℕ) (X Y : ℕ → Site d)
    (hXY : ∀ j ≤ k, X j = Y j) (s : ℝ≥0) (hs : s ≤ k) :
    linearWalk R s X = linearWalk R s Y := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · simpa only [linearWalk_nat] using congrArg (Lclt.scaledSite R) (hXY k le_rfl)
  · have hs' : (s : ℝ) < k := by exact_mod_cast hs
    have hn : ⌊(s : ℝ)⌋₊ < k := (Nat.floor_lt s.property).2 hs'
    simp only [linearWalk, hXY _ (Nat.le_of_lt hn), hXY _ hn]

/-- The interpolation is at most one scaled walk increment from the next
lattice position. -/
theorem norm_linearWalk_sub_next_le {d : ℕ} (R : ℝ) (s : ℝ≥0) (X : ℕ → Site d) :
    ‖linearWalk R s X - Lclt.scaledSite R (X (⌊(s : ℝ)⌋₊ + 1))‖ ≤
      ‖Lclt.scaledSite R (X ⌊(s : ℝ)⌋₊) -
        Lclt.scaledSite R (X (⌊(s : ℝ)⌋₊ + 1))‖ := by
  let n := ⌊(s : ℝ)⌋₊
  let a : ℝ := (s : ℝ) - n
  have ha0 : 0 ≤ a := by
    dsimp [a, n]
    exact sub_nonneg.mpr (Nat.floor_le s.property)
  have ha1 : a ≤ 1 := by dsimp [a, n]; linarith [Nat.lt_floor_add_one (s : ℝ)]
  have heq : linearWalk R s X - Lclt.scaledSite R (X (n + 1)) =
      (1 - a) • (Lclt.scaledSite R (X n) - Lclt.scaledSite R (X (n + 1))) := by
    change (1 - a) • Lclt.scaledSite R (X n) +
      a • Lclt.scaledSite R (X (n + 1)) - Lclt.scaledSite R (X (n + 1)) = _
    simp only [smul_sub, sub_smul, one_smul]
    abel
  change ‖linearWalk R s X - Lclt.scaledSite R (X (n + 1))‖ ≤
    ‖Lclt.scaledSite R (X n) - Lclt.scaledSite R (X (n + 1))‖
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha1)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

end Sandpile.External.Stopping
