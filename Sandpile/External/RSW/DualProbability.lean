import Sandpile.External.RSW.DualLaw
import Sandpile.External.RSW.BondCrossingMeasurable

/-!
# Dual crossing probabilities

For every probability law, a primal horizontal crossing and the shifted dual vertical
crossing have complementary probabilities.
-/

open MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- The dual crossing event for a Boolean primal bond configuration. -/
def shiftedDualCrossingEvent (w h : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  openPlaneBonds ⁻¹' dualTBCrossing w h

/-- The shifted dual crossing event is the complement of the primal crossing event. -/
theorem shiftedDualCrossingEvent_eq_compl (w h : ℕ) :
    shiftedDualCrossingEvent w h = (bondCrossingEvent w h)ᶜ := by
  ext ω
  simp only [shiftedDualCrossingEvent, mem_preimage, mem_compl_iff,
    bondCrossingEvent_iff_not_dualTBCrossing, not_not]

/-- The shifted dual crossing event is measurable. -/
theorem measurableSet_shiftedDualCrossingEvent (w h : ℕ) :
    MeasurableSet (shiftedDualCrossingEvent w h) := by
  rw [shiftedDualCrossingEvent_eq_compl]
  exact (measurableSet_bondCrossingEvent w h).compl

/-- The primal and shifted dual crossing probabilities sum to one. -/
theorem measureReal_bondCrossing_add_shiftedDual (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ] (w h : ℕ) :
    μ.real (bondCrossingEvent w h) + μ.real (shiftedDualCrossingEvent w h) = 1 := by
  rw [shiftedDualCrossingEvent_eq_compl,
    probReal_compl_eq_one_sub (measurableSet_bondCrossingEvent w h)]
  ring

/-- The dual crossing is an open vertical crossing of the shifted dual rectangle under the
complemented dual bond configuration. -/
theorem mem_shiftedDualCrossingEvent_iff (w h : ℕ) (ω : Sym2 (Site 2) → Bool) :
    ω ∈ shiftedDualCrossingEvent w h ↔
      openPlaneBonds (dualBondConfig ω) ∈
        openCrossing (↑(dualRectangle w h)) (↑(dualTopSide w h)) (↑(dualBottomSide w h)) := by
  change openPlaneBonds ω ∈ dualTBCrossing w h ↔ _
  rw [openPlaneBonds_dualBondConfig]
  rfl

end Sandpile.External.RSW
