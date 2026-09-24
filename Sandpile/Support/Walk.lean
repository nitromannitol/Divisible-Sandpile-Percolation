/-
Elementary facts about the walk vocabulary of `Sandpile/Walk.lean`.

The optimal-stopping values are suprema over a set of reals, so the first thing
to know is that the set is not empty: the stopping time that stops at once is
admissible for every bound.  Without this the `sSup` could be its junk value.
-/
import Sandpile.Walk

namespace Sandpile

variable {d : ℕ}

/-- Stopping at once is a stopping time. -/
theorem isWalkStopping_zero : IsWalkStopping (fun _ : (ℕ → Site d) => 0) :=
  fun _ _ _ _ h => h

/-- The value of stopping at once belongs to the set the supremum is taken over. -/
theorem stoppingSup_mem (n : ℕ) (x : Site d) (F : ℕ → (ℕ → Site d) → ℝ) :
    (∫ X, F 0 X ∂(walkLaw d x)) ∈
      {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
        a = ∫ X, F (τ X) X ∂(walkLaw d x)} :=
  ⟨fun _ => 0, isWalkStopping_zero, fun _ => Nat.zero_le n, rfl⟩

/-- `p_0(x, y)` is the Kronecker delta. -/
theorem heatKernel_zero (x y : Site d) :
    heatKernel d 0 x y = if x = y then 1 else 0 := rfl

/-- `g_0 = 0`. -/
theorem greenTime_zero (x y : Site d) : greenTime d 0 x y = 0 := rfl

/-- `g_{t+1} = g_t + p_t`. -/
theorem greenTime_succ (t : ℕ) (x y : Site d) :
    greenTime d (t + 1) x y = greenTime d t x y + heatKernel d t x y :=
  Finset.sum_range_succ _ _

/-- `V_0 = 0`. -/
theorem membrane_zero (ζ : Site d → ℝ) (x : Site d) : membrane ζ 0 x = 0 := rfl

/-- `V_{n+1} = ζ + P V_n`. -/
theorem membrane_succ (ζ : Site d → ℝ) (n : ℕ) (x : Site d) :
    membrane ζ (n + 1) x = ζ x + avg (membrane ζ n) x := rfl

/-- The odometer in the scenery variable agrees with the odometer driven by the
mass field `σ = 1 + 2dζ`. -/
theorem odometerOf_eq_odometer (σ : Site d → ℝ) (t : ℕ) (x : Site d) :
    odometerOf (scenery d σ) t x = odometer σ t x := by
  induction t generalizing x with
  | zero => rfl
  | succ n ih =>
      show max 0 (scenery d σ x + avg (odometerOf (scenery d σ) n) x) = relax σ _ x
      unfold relax avg LatticeProb.walkOp scenery
      congr 2
      · rw [add_div]
        congr 1
        exact congrArg (fun u => nbrSum u x / (2 * (d : ℝ))) (funext fun y => ih y)

end Sandpile
