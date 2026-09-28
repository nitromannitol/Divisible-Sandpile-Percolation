import Sandpile.Support.LinJacobianCovBridge
import Sandpile.External.IntersectionSecondMoment

/-!
# The real-valued intersection count, and its majorization of finite double sums

This module defines the intersection count of two paths as a real number, and proves the
majorization of the time-restricted intersection sums of Step 1 of
`lem:dgt4-linearization-from-survival` by it.

`Sandpile.External.interCount` is the paper's `I(X,Y) = ∑_{i,j≥0}1_{X_i=Y_j}`, valued in `ℝ≥0∞` so
that an infinite count is not rounded to a junk value. Step 1 uses a real-valued majorant of the
finite double sums, and `sum_indicator_le_interCountReal` shows every finite double sum of
intersection indicators is below `interCountReal X Y`, the real part of `I(X,Y)`, so it serves
wherever `I(X,Y)` is finite. Under the two-walk law in `d ≥ 5` that is almost every pair of paths,
which is the form in which `Support/LinJacobianEarly.lean` asks for the majorization.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- The intersection count as a real number. -/
noncomputable def interCountReal (X Y : ℕ → Site d) : ℝ :=
  (Sandpile.External.interCount X Y).toReal

/-- `interCountReal X Y` is nonnegative, being the `toReal` of an `ℝ≥0∞`-valued quantity. -/
theorem interCountReal_nonneg (X Y : ℕ → Site d) : 0 ≤ interCountReal X Y :=
  ENNReal.toReal_nonneg

/-- Every finite double sum of intersection indicators is below the real
intersection count, wherever that count is finite. -/
theorem sum_indicator_le_interCountReal (s t : Finset ℕ) (X Y : ℕ → Site d)
    (hfin : Sandpile.External.interCount X Y ≠ ⊤) :
    ∑ r ∈ s, ∑ h ∈ t, (if X r = Y h then (1 : ℝ) else 0) ≤ interCountReal X Y := by
  classical
  have hle : ∑ p ∈ s ×ˢ t, Set.indicator {q : ℕ × ℕ | X q.1 = Y q.2} (fun _ => (1 : ℝ≥0∞)) p
      ≤ Sandpile.External.interCount X Y := ENNReal.sum_le_tsum _
  have hne : ∀ p ∈ s ×ˢ t,
      Set.indicator {q : ℕ × ℕ | X q.1 = Y q.2} (fun _ => (1 : ℝ≥0∞)) p ≠ ⊤ := by
    intro p _
    by_cases hp : X p.1 = Y p.2 <;> simp [hp]
  have hrw : ∑ r ∈ s, ∑ h ∈ t, (if X r = Y h then (1 : ℝ) else 0)
      = (∑ p ∈ s ×ˢ t,
          Set.indicator {q : ℕ × ℕ | X q.1 = Y q.2} (fun _ => (1 : ℝ≥0∞)) p).toReal := by
    rw [ENNReal.toReal_sum hne, Finset.sum_product]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun h _ => ?_
    by_cases hp : X r = Y h <;> simp [hp]
  rw [hrw]
  exact ENNReal.toReal_mono hfin hle

end Sandpile
