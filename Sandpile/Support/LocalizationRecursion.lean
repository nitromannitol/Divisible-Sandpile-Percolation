/-
The one-step recursion for the localized odometer.

`Sandpile/Support/Localization.lean` defines the localized odometer as the
supremum of the stopped scenery sums of the walk killed off `D`.  The shared
library carries the same object in its own vocabulary together with the dynamic
programming principle for it, so the recursion

  `w_{n+1}(x) = (zeta(x) + avg w_n (x))^+`,  `x` in `D`,

follows by identifying the two.  This is the induction step of the first clause
of the origin-frozen lemma.
-/
import Sandpile.Support.Localization
import LatticeProb.Graph.ZdKilled

open MeasureTheory

namespace Sandpile

open scoped Classical

variable {d : ℕ}

theorem localizedOdometer_eq_zdKilled (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (t : ℕ) (x : Site d) :
    localizedOdometer D ζ t x = LatticeProb.Graph.Zd.zdKilledOdometer D ζ t x := by
  classical
  by_cases hx : x ∈ D
  · rw [localizedOdometer, Set.indicator_of_mem hx]
    exact LatticeProb.Graph.Zd.sSup_zdKilledStopValues d hd D ζ t x
  · rw [localizedOdometer, Set.indicator_of_notMem hx,
      LatticeProb.Graph.Zd.zdKilledOdometer_of_notMem D ζ hx]

/-- **The one-step recursion for the localized odometer**, in the form the
localized odometer itself takes: it already vanishes off `D`. -/
theorem localizedOdometer_succ' (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (n : ℕ) (x : Site d) (hx : x ∈ D) :
    localizedOdometer D ζ (n + 1) x
      = max 0 (ζ x + Sandpile.avg (localizedOdometer D ζ n) x) := by
  have hfun : localizedOdometer D ζ n = LatticeProb.Graph.Zd.zdKilledOdometer D ζ n :=
    funext fun y => localizedOdometer_eq_zdKilled hd D ζ n y
  rw [localizedOdometer_eq_zdKilled hd D ζ (n + 1) x, hfun, Sandpile.avg]
  exact LatticeProb.Graph.Zd.zdKilledOdometer_succ_of_mem D ζ hx n

theorem localizedOdometer_succ (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (n : ℕ) (x : Site d) (hx : x ∈ D) :
    localizedOdometer D ζ (n + 1) x
      = max 0 (ζ x + Sandpile.avg
          (fun y => if y ∈ D then localizedOdometer D ζ n y else 0) x) := by
  classical
  have hfun : (fun y => if y ∈ D then localizedOdometer D ζ n y else 0)
      = LatticeProb.Graph.Zd.zdKilledOdometer D ζ n := by
    funext y
    by_cases hy : y ∈ D
    · rw [if_pos hy, localizedOdometer_eq_zdKilled hd D ζ n y]
    · rw [if_neg hy, LatticeProb.Graph.Zd.zdKilledOdometer_of_notMem D ζ hy]
  rw [localizedOdometer_eq_zdKilled hd D ζ (n + 1) x, hfun, Sandpile.avg]
  exact LatticeProb.Graph.Zd.zdKilledOdometer_succ_of_mem D ζ hx n

end Sandpile
