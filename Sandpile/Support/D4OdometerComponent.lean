/-
The last step of the dimension-four percolation proof
(`sandpile.tex:4079-4083`): the finite-range field is dominated by the odometer
at the block horizon, so an infinite nearest-neighbour component of its
superlevel set inside the coordinate plane is an infinite component of the
superlevel set of the odometer at the later time `t`.
-/
import Sandpile.Support.D4PlaneEmbed
import Sandpile.Support.SceneryBridge
import Sandpile.Support.Barrier

open MeasureTheory

noncomputable section
namespace Sandpile


/-- Last step of the dimension-four percolation proof: an infinite
nearest-neighbour component of a superlevel set of a field dominated by the
odometer at an earlier time is an infinite component of the superlevel set of
the odometer at time `t`, in the coordinate plane. -/
theorem infinite_odometer_component_of_field
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (G : (Site 4 → ℝ) → Site 4 → ℝ) (c ℓ : ℝ) (t s : ℕ) (hst : s ≤ t)
    (hG : ∀ ζ y, G ζ y ≤ odometerOf ζ s y)
    (hlevel : c * Real.log t < ℓ)
    (h : ∀ᵐ ζ ∂(LatticeProb.iidLaw 4 ν),
        HasInfiniteComponent {u : Site 2 | ℓ ≤ G ζ (planeEmbed u)}) :
    ∀ᵐ σ ∂(Sandpile.centeredMassLaw 4 ν),
      HasInfiniteComponent
        {z : Site 2 | c * Real.log t < Sandpile.odometer σ t (Sandpile.planeEmbed z)} := by
  have hmp : MeasurePreserving (scenery 4) (Sandpile.centeredMassLaw 4 ν)
      (LatticeProb.iidLaw 4 ν) :=
    ⟨measurable_scenery 4, map_scenery_centeredMassLaw 4 ν (by norm_num)⟩
  have h' := hmp.quasiMeasurePreserving.ae h
  filter_upwards [h'] with σ hσ
  refine hasInfiniteComponent_mono ?_ hσ
  intro u hu
  have h1 : ℓ ≤ G (scenery 4 σ) (planeEmbed u) := hu
  have h2 := hG (scenery 4 σ) (planeEmbed u)
  have h3 := odometerOf_mono_time (scenery 4 σ) (planeEmbed u) hst
  have h4 : odometerOf (scenery 4 σ) t (planeEmbed u) = odometer σ t (planeEmbed u) :=
    (congrFun (odometer_eq_odometerOf σ t) (planeEmbed u)).symm
  show c * Real.log t < odometer σ t (planeEmbed u)
  linarith

end Sandpile
