import Sandpile.Support.CrossFieldSym
import Sandpile.Support.CrossSymmetry

/-!
# Crossing events depend on the field only through its law

The chain events of `Sandpile/Support/CrossUnion.lean` depend on the field only
through its law.

`crossApprox` is a countable union of countable intersections of events about
single values of the field, so it is the pullback along `ω ↦ (u ↦ X u ω)` of one
measurable subset of the space of planar functions, namely the same union built
from the evaluations (`crossApprox_eq_preimage`).  Two fields with the same law,
that is with the same finite-dimensional distributions, therefore give the chain
events the same probability (`measure_crossApprox_eq_of_fieldLaw`), whatever
probability spaces they live on.

This is what a symmetry of a field gives for crossings, and it is all it gives.
The crossing event itself is not measurable, and equality in law says nothing
about the outer measures of sets that are not measurable; what the estimates of
`Sandpile/Support/CrossUnion.lean` add is that the crossing probability is
bracketed by chain probabilities at two levels a distance `ε` apart, and those
two numbers are determined by the law.  The square estimate of
`Sandpile/Support/CrossDuality.lean` is proved exactly through that bracket.
-/

open MeasureTheory Set

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A plane symmetry is continuous. -/
theorem continuous_planeSymmetry (T : Sandpile.Continuum.PlaneSymmetry) :
    Continuous T.toFun := by
  unfold Sandpile.Continuum.PlaneSymmetry.toFun
  fun_prop

/-- `crossApprox X a b i l` is the preimage, under the evaluation map
`ω ↦ (u ↦ X u ω)` from `Ω` into the space of planar functions, of the same `crossApprox`
event built from the coordinate evaluations `u ↦ (g ↦ g u)`. -/
theorem crossApprox_eq_preimage {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    crossApprox X a b i l
      = (fun ω => (fun u => X u ω) : Ω → (Sandpile.Continuum.Space 2 → ℝ)) ⁻¹'
          crossApprox (fun (u : Sandpile.Continuum.Space 2)
            (g : Sandpile.Continuum.Space 2 → ℝ) => g u) a b i l := by
  unfold crossApprox
  rw [Set.preimage_iUnion]
  rfl

/-- The underlying function of `PlaneSymmetry.transpose` agrees pointwise with `swapPoint`,
checked coordinate by coordinate via `fin_cases` on `Fin 2`. -/
theorem transpose_toFun_eq_swapPoint (u : Sandpile.Continuum.Space 2) :
    (Sandpile.Continuum.PlaneSymmetry.transpose).toFun u = swapPoint u := by
  ext k
  rw [Sandpile.Continuum.PlaneSymmetry.toFun_apply, swapPoint_apply]
  fin_cases k <;>
    simp [Sandpile.Continuum.PlaneSymmetry.transpose, swapIdx, Equiv.swap_apply_left,
      Equiv.swap_apply_right]

/-- If `X` and `Y` have the same field law (`fieldLaw P X = fieldLaw P' Y`), then the
`crossApprox` event has the same probability under `X` as under `Y`, since both events are
preimages of the same measurable subset of the function space along the pushforward maps. -/
theorem measure_crossApprox_eq_of_fieldLaw {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (Y : Sandpile.Continuum.Space 2 → Ω' → ℝ)
    (hX : ∀ u, Measurable (X u)) (hY : ∀ u, Measurable (Y u))
    (hlaw : fieldLaw P X = fieldLaw P' Y) (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    P (crossApprox X a b i l) = P' (crossApprox Y a b i l) := by
  have hev : ∀ u : Sandpile.Continuum.Space 2,
      Measurable (fun g : Sandpile.Continuum.Space 2 → ℝ => g u) := fun u => measurable_pi_apply u
  have hmeasSet := measurableSet_crossApprox hev a b i l
  rw [crossApprox_eq_preimage X a b i l, crossApprox_eq_preimage Y a b i l,
    measure_preimage_fieldLaw P X hX hmeasSet, measure_preimage_fieldLaw P' Y hY hmeasSet, hlaw]

end Sandpile.Support
