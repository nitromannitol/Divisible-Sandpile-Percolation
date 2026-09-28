import Sandpile.Support.D23Field
import Sandpile.Support.SceneryBridge
import Sandpile.Support.Barrier
import Sandpile.Support.Crit23Scale

/-!
# From localized-field components to odometer components

This file carries out the last step of the dimension-two and dimension-three percolation proof
(`sandpile.tex:2606-2612`). Because the localized odometer field at the block horizon `s` is
dominated by the odometer at any later time `t`, an infinite nearest-neighbour component of a
superlevel set of the localized field inside the coordinate plane is also an infinite component
of the superlevel set of the odometer itself at time `t`
(`infinite_odometer_component_of_d23Field`). `hasInfiniteComponent_criticalScale_of_plane` then
restates this at the critical scale `h(t) = t ^ ((4 - d) / 4)` of Theorem 1.2, transporting an
infinite component of the plane's level set to one of the full lattice's level set.
-/

open MeasureTheory

noncomputable section
namespace Sandpile

variable {d : ℕ}

/-- An infinite nearest-neighbour component of a superlevel set of the localized
odometer field at the earlier time `s` is an infinite component of the
superlevel set of the odometer at time `t`, in the coordinate plane. -/
theorem infinite_odometer_component_of_d23Field (hd : 1 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (R s t : ℕ) (hst : s ≤ t) (lev ℓ : ℝ) (hlevel : lev < ℓ)
    (h : ∀ᵐ ζ ∂(LatticeProb.iidLaw d ν),
        LatticeProb.HasInfiniteComponent {u : Site 2 | ℓ ≤ d23Field d R s ζ u}) :
    ∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
      LatticeProb.HasInfiniteComponent
        {z : Site 2 | lev < Sandpile.odometer σ t (Sandpile.planeSite z)} := by
  have hmp : MeasurePreserving (scenery d) (Sandpile.centeredMassLaw d ν)
      (LatticeProb.iidLaw d ν) :=
    ⟨measurable_scenery d, map_scenery_centeredMassLaw d ν hd⟩
  have h' := hmp.quasiMeasurePreserving.ae h
  filter_upwards [h'] with σ hσ
  refine hasInfiniteComponent_mono ?_ hσ
  intro u hu
  have h1 : ℓ ≤ d23Field d R s (scenery d σ) u := hu
  have h2 := d23Field_le_odometerOf hd R s (scenery d σ) u
  have h3 := odometerOf_mono_time (scenery d σ) (planeSite (d := d) u) hst
  have h4 : odometerOf (scenery d σ) t (planeSite (d := d) u)
      = odometer σ t (planeSite (d := d) u) :=
    (congrFun (odometer_eq_odometerOf σ t) (planeSite (d := d) u)).symm
  show lev < odometer σ t (planeSite (d := d) u)
  linarith

/-- The plane component of the theorem's level set is a component of the lattice
level set, at the critical scale `h(t) = t^{(4-d)/4}` of Theorem 1.2. -/
theorem hasInfiniteComponent_criticalScale_of_plane (hd2 : 2 ≤ d) (hd3 : d ≤ 3)
    (c : ℝ) (t : ℕ) (σ : Site d → ℝ)
    (h : LatticeProb.HasInfiniteComponent
      {z : Site 2 | c * (t : ℝ) ^ ((4 - (d : ℝ)) / 4) <
        Sandpile.odometer σ t (Sandpile.planeSite z)}) :
    LatticeProb.HasInfiniteComponent
      {x : Site d | c * Sandpile.criticalScale d t < Sandpile.odometer σ t x} := by
  have hscale : Sandpile.criticalScale d t = (t : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
    unfold Sandpile.criticalScale
    rw [if_pos hd3]
  rw [hscale]
  exact hasInfiniteComponent_planeSite hd2 h

end Sandpile
