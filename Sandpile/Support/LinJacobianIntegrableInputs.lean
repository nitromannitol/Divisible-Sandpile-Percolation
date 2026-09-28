import Sandpile.Support.LinJacobianCoefInput
import Sandpile.Support.Concentration

/-! # Jacobian Integrable Inputs

The three square-integrability hypotheses of Step 2 of
`lem:dgt4-linearization-from-survival`.

Every one of the three functionals whose square Step 2 integrates is a
difference of the tested field, a constant and a finite linear functional of the
scenery, so all three are in `L²` as soon as the tested field and the
coordinates are.  The tested field is a finite nonnegative combination of
odometers, which are square integrable whenever the one-site law is
(`Support/Concentration.lean`), and each coordinate of the i.i.d. field has the
one-site law itself as its image measure.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- A coordinate of the i.i.d. field is square integrable when the one-site law
is. -/
theorem memLp_two_eval (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (v : Site d) :
    MemLp (fun ω : Site d → ℝ => ω v) 2 (LatticeProb.iidLaw d ν) := by
  have hmap : (LatticeProb.iidLaw d ν).map (fun ω : Site d → ℝ => ω v) = ν :=
    Measure.infinitePi_map_eval (μ := fun _ : Site d => ν) v
  have hid : MemLp (id : ℝ → ℝ) 2 ((LatticeProb.iidLaw d ν).map (fun ω : Site d → ℝ => ω v)) := by
    rw [hmap]
    exact (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq
  have h := (memLp_map_measure_iff (g := (id : ℝ → ℝ))
    (f := fun ω : Site d → ℝ => ω v) (μ := LatticeProb.iidLaw d ν) (p := 2)
    (by rw [hmap]; exact aestronglyMeasurable_id) (measurable_pi_apply v).aemeasurable).mp hid
  exact h

/-- A finite linear functional of the i.i.d. field is square integrable. -/
theorem memLp_two_linearField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (S : Finset (Site d)) (c : Site d → ℝ) :
    MemLp (fun ω : Site d → ℝ => ∑ v ∈ S, c v * ω v) 2 (LatticeProb.iidLaw d ν) := by
  classical
  refine memLp_finsetSum S fun v _ => ?_
  exact (memLp_two_eval ν hsq v).const_mul (c v)

/-- The tested field is square integrable. -/
theorem memLp_two_testedField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ) :
    MemLp (testedField s a n) 2 (LatticeProb.iidLaw d ν) := by
  classical
  have : (testedField s a n) = fun ζ : Site d → ℝ => ∑ x ∈ s, a x * odometerOf ζ n x := rfl
  rw [this]
  exact memLp_finsetSum s fun x _ => (memLp_two_odometerOf ν hsq n x).const_mul (a x)

/-- **The hypotheses `hI1`, `hI2` and `hI3` of Step 2.**  Each functional is a
difference of the tested field, a constant and a finite linear functional, so
each is square integrable. -/
theorem integrable_sq_testedField_sub_linear (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ)
    (S : Finset (Site d)) (c : Site d → ℝ) (m : ℝ) :
    Integrable (fun ζ : Site d → ℝ =>
      (testedField s a n ζ - m - ∑ v ∈ S, c v * ζ v) ^ 2) (LatticeProb.iidLaw d ν) :=
  (((memLp_two_testedField ν hsq s a n).sub (memLp_const m)).sub
    (memLp_two_linearField ν hsq S c)).integrable_sq

/-- The difference of two finite linear functionals of the field is square
integrable, which is the hypothesis `hI2`. -/
theorem integrable_sq_linear_sub_linear (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (S : Finset (Site d)) (c c' : Site d → ℝ) :
    Integrable (fun ζ : Site d → ℝ =>
      (∑ v ∈ S, c v * ζ v - ∑ v ∈ S, c' v * ζ v) ^ 2) (LatticeProb.iidLaw d ν) :=
  ((memLp_two_linearField ν hsq S c).sub (memLp_two_linearField ν hsq S c')).integrable_sq

end Sandpile
