import Sandpile.External.RSW.CenteredBridgeDecomposition
import Sandpile.External.RSW.EdgeCarrier

/-!
# Centered bridges on lattice edges

A bridge depends only on nearest-neighbor bond states, so its probability is
preserved by restriction to the lattice-edge carrier.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The bridge event on nearest-neighbor edge configurations. -/
def planeEdgeCenteredBridgeEvent (m d : ℕ) : Set (PlaneEdge → Bool) :=
  extendPlaneEdges ⁻¹' centeredBridgeEvent m d

/-- The nearest-neighbor bridge event is measurable. -/
theorem measurableSet_planeEdgeCenteredBridgeEvent (m d : ℕ) :
    MeasurableSet (planeEdgeCenteredBridgeEvent m d) :=
  (measurableSet_centeredBridgeEvent m d).preimage measurable_extendPlaneEdges

/-- Bridge occurrence depends only on lattice-edge states. -/
theorem preimage_planeEdgeCenteredBridgeEvent (m d : ℕ) :
    restrictToPlaneEdges ⁻¹' planeEdgeCenteredBridgeEvent m d = centeredBridgeEvent m d := by
  ext ω
  simp only [planeEdgeCenteredBridgeEvent, mem_preimage, centeredBridgeEvent, bondConnectionEvent,
    mem_ofPred_eq, isBondOpenWalk_extend_restrict]

/-- Restricting a bond law to lattice edges preserves bridge probabilities. -/
theorem restrictToPlaneEdges_centeredBridge (μ : Measure (Sym2 (Site 2) → Bool)) (m d : ℕ) :
    (μ.map restrictToPlaneEdges).real (planeEdgeCenteredBridgeEvent m d) = μ.real (centeredBridgeEvent m d) := by
  rw [Measure.real, Measure.map_apply measurable_restrictToPlaneEdges
    (measurableSet_planeEdgeCenteredBridgeEvent m d), preimage_planeEdgeCenteredBridgeEvent m d]
  rfl

end Sandpile.External.RSW
