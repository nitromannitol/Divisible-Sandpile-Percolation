import Sandpile.External.RSW.ArmBridge
import Sandpile.External.RSW.EdgeCarrier
import Sandpile.External.RSW.QuasiCascadeCover

/-!
# KST events on lattice edges

The arm, bridge, and quasi-crossing events depend only on nearest-neighbor bond states,
so their probabilities are preserved by restriction to the lattice-edge carrier.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The arm event on nearest-neighbor edge configurations. -/
def planeEdgeKSTArmEvent (m : ℕ) : Set (PlaneEdge → Bool) :=
  extendPlaneEdges ⁻¹' kstArmEvent m

/-- The bridge event on nearest-neighbor edge configurations. -/
def planeEdgeKSTBridgeEvent (m : ℕ) : Set (PlaneEdge → Bool) :=
  extendPlaneEdges ⁻¹' kstBridgeEvent m

/-- The nearest-neighbor arm event is measurable. -/
theorem measurableSet_planeEdgeKSTArmEvent (m : ℕ) : MeasurableSet (planeEdgeKSTArmEvent m) :=
  (measurableSet_kstArmEvent m).preimage measurable_extendPlaneEdges

/-- The nearest-neighbor bridge event is measurable. -/
theorem measurableSet_planeEdgeKSTBridgeEvent (m : ℕ) :
    MeasurableSet (planeEdgeKSTBridgeEvent m) :=
  (measurableSet_kstBridgeEvent m).preimage measurable_extendPlaneEdges

/-- Arm occurrence depends only on lattice-edge states. -/
theorem preimage_planeEdgeKSTArmEvent (m : ℕ) :
    restrictToPlaneEdges ⁻¹' planeEdgeKSTArmEvent m = kstArmEvent m := by
  ext ω
  simp only [planeEdgeKSTArmEvent, mem_preimage, kstArmEvent, bondConnectionEvent,
    mem_ofPred_eq, isBondOpenWalk_extend_restrict]

/-- Bridge occurrence depends only on lattice-edge states. -/
theorem preimage_planeEdgeKSTBridgeEvent (m : ℕ) :
    restrictToPlaneEdges ⁻¹' planeEdgeKSTBridgeEvent m = kstBridgeEvent m := by
  ext ω
  simp only [planeEdgeKSTBridgeEvent, mem_preimage, kstBridgeEvent, bondConnectionEvent,
    mem_ofPred_eq, isBondOpenWalk_extend_restrict]

/-- Restricting a bond law to lattice edges preserves arm probabilities. -/
theorem restrictToPlaneEdges_kstArm (μ : Measure (Sym2 (Site 2) → Bool)) (m : ℕ) :
    (μ.map restrictToPlaneEdges).real (planeEdgeKSTArmEvent m) = μ.real (kstArmEvent m) := by
  rw [Measure.real, Measure.map_apply measurable_restrictToPlaneEdges
    (measurableSet_planeEdgeKSTArmEvent m), preimage_planeEdgeKSTArmEvent]
  rfl

/-- Restricting a bond law to lattice edges preserves bridge probabilities. -/
theorem restrictToPlaneEdges_kstBridge (μ : Measure (Sym2 (Site 2) → Bool)) (m : ℕ) :
    (μ.map restrictToPlaneEdges).real (planeEdgeKSTBridgeEvent m) = μ.real (kstBridgeEvent m) := by
  rw [Measure.real, Measure.map_apply measurable_restrictToPlaneEdges
    (measurableSet_planeEdgeKSTBridgeEvent m), preimage_planeEdgeKSTBridgeEvent]
  rfl

/-- The quasi-crossing event on nearest-neighbor edge configurations. -/
def planeEdgeKSTQuasiCrossingEvent (n m : ℕ) : Set (PlaneEdge → Bool) :=
  extendPlaneEdges ⁻¹' kstQuasiCrossingEvent n m

/-- The exceptional path event on nearest-neighbor edge configurations. -/
def planeEdgeKSTExceptionalPathEvent (n m k : ℕ) : Set (PlaneEdge → Bool) :=
  extendPlaneEdges ⁻¹' kstExceptionalPathEvent n m k

/-- The nearest-neighbor quasi-crossing event is measurable. -/
theorem measurableSet_planeEdgeKSTQuasiCrossingEvent (n m : ℕ) :
    MeasurableSet (planeEdgeKSTQuasiCrossingEvent n m) :=
  (measurableSet_kstQuasiCrossingEvent n m).preimage measurable_extendPlaneEdges

/-- The nearest-neighbor exceptional path event is measurable. -/
theorem measurableSet_planeEdgeKSTExceptionalPathEvent (n m k : ℕ) :
    MeasurableSet (planeEdgeKSTExceptionalPathEvent n m k) :=
  (measurableSet_kstExceptionalPathEvent n m k).preimage measurable_extendPlaneEdges

/-- Quasi-crossing occurrence depends only on lattice-edge states. -/
theorem preimage_planeEdgeKSTQuasiCrossingEvent (n m : ℕ) :
    restrictToPlaneEdges ⁻¹' planeEdgeKSTQuasiCrossingEvent n m = kstQuasiCrossingEvent n m := by
  ext ω
  simp only [planeEdgeKSTQuasiCrossingEvent, mem_preimage, kstQuasiCrossingEvent,
    mem_inter_iff, kstWallEvent, mem_ofPred_eq, isBondOpenWalk_extend_restrict]

/-- Exceptional path occurrence depends only on lattice-edge states. -/
theorem preimage_planeEdgeKSTExceptionalPathEvent (n m k : ℕ) :
    restrictToPlaneEdges ⁻¹' planeEdgeKSTExceptionalPathEvent n m k =
      kstExceptionalPathEvent n m k := by
  ext ω
  simp only [planeEdgeKSTExceptionalPathEvent, mem_preimage, kstExceptionalPathEvent,
    mem_ofPred_eq, isBondOpenWalk_extend_restrict]

/-- Restricting a bond law to lattice edges preserves quasi-crossing probabilities. -/
theorem restrictToPlaneEdges_kstQuasiCrossing (μ : Measure (Sym2 (Site 2) → Bool)) (n m : ℕ) :
    (μ.map restrictToPlaneEdges).real (planeEdgeKSTQuasiCrossingEvent n m) =
      μ.real (kstQuasiCrossingEvent n m) := by
  rw [Measure.real, Measure.map_apply measurable_restrictToPlaneEdges
    (measurableSet_planeEdgeKSTQuasiCrossingEvent n m), preimage_planeEdgeKSTQuasiCrossingEvent]
  rfl

/-- Restricting a bond law to lattice edges preserves exceptional path probabilities. -/
theorem restrictToPlaneEdges_kstExceptionalPath (μ : Measure (Sym2 (Site 2) → Bool)) (n m k : ℕ) :
    (μ.map restrictToPlaneEdges).real (planeEdgeKSTExceptionalPathEvent n m k) =
      μ.real (kstExceptionalPathEvent n m k) := by
  rw [Measure.real, Measure.map_apply measurable_restrictToPlaneEdges
    (measurableSet_planeEdgeKSTExceptionalPathEvent n m k), preimage_planeEdgeKSTExceptionalPathEvent]
  rfl

end Sandpile.External.RSW
