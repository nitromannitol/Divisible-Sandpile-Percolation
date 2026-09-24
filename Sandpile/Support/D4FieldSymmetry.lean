/-
Invariance of the ball Green field under a permutation of the coordinates:
the killed Green function of the cube is permutation invariant, so permuting
the scenery permutes the field.  This is what makes the two bottom-top
crossing clauses of the good-block event have the same law as the two
left-right clauses.
-/
import Sandpile.Support.BallCrossingDefinitions
import Sandpile.Support.KernelPermutation
import Sandpile.Law

open MeasureTheory

noncomputable section
namespace Sandpile


lemma ballCube_preimage_permute (e : Fin 4 ≃ Fin 4) (r : ℝ) :
    (permuteSite e) ⁻¹' (ballCube 0 r) = ballCube 0 r := by
  ext x
  change (∀ i : Fin 4, |((x (e i) : ℤ) : ℝ) - ((0 : Site 4) i : ℝ)| ≤ r) ↔
    ∀ i : Fin 4, |((x i : ℤ) : ℝ) - ((0 : Site 4) i : ℝ)| ≤ r
  constructor
  · intro h i
    simpa using h (e.symm i)
  · intro h i
    exact h (e i)


lemma ballGreenField_permute (e : Fin 4 ≃ Fin 4) (r : ℕ) (ζ : Site 4 → ℝ) (z : Site 4) :
    ballGreenField r (fun y => ζ (permuteSite e y)) z
      = ballGreenField r ζ (permuteSite e z) := by
  have hker : ∀ u : Site 4, killedGreen (ballCube 0 (r : ℝ)) 0 (permuteSite e u)
      = killedGreen (ballCube 0 (r : ℝ)) 0 u := by
    intro u
    have hh := killedGreen_permute e (ballCube 0 (r : ℝ)) 0 u
    rw [ballCube_preimage_permute, map_zero] at hh
    exact hh.symm
  have hstep : ∀ u : Site 4,
      killedGreen (ballCube 0 (r : ℝ)) 0 u * ζ (permuteSite e (z + u))
        = (fun v : Site 4 => killedGreen (ballCube 0 (r : ℝ)) 0 v *
            ζ (permuteSite e z + v)) (permuteSite e u) := by
    intro u
    simp only [map_add]
    rw [hker u]
  unfold ballGreenField
  rw [tsum_congr hstep]
  exact (permuteSite e).toEquiv.tsum_eq
    (fun v : Site 4 => killedGreen (ballCube 0 (r : ℝ)) 0 v * ζ (permuteSite e z + v))



theorem iidLaw_map_permuteSite {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (e : Fin 4 ≃ Fin 4) :
    (LatticeProb.iidLaw 4 ν).map (fun η : Site 4 → α => fun x => η (permuteSite e x))
      = LatticeProb.iidLaw 4 ν := by
  exact (LatticeProb.measurePreserving_coordShift (fun _ : Site 4 => ν)
    (g := fun x : Site 4 => permuteSite e x)
    (fun _ _ h => (permuteSite e).injective h) fun _ => rfl).map_eq

end Sandpile
