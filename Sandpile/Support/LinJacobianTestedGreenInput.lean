import Sandpile.Support.LinJacobianTestedStep1
import Sandpile.Support.LinTestedGreen
import Sandpile.Support.LinTestedStep2

/-! # Jacobian Tested Green Input

`eq:dgt4-tested-green-bound` (`sandpile.tex:5791-5795`) at the tested weight: the
uniform `ℓ²` bound on the coefficients `b_R(z)=∑_x a_R(x)g_{n_R}(x,z)` that Step
2 of `lem:dgt4-linearization-from-survival` consumes as `hB₀`.

`Support/LinTestedGreen.lean` bounds the time-`n_R` weights by the Green weights,
and `Support/LinTested.lean` bounds the `ℓ²` norm of the Green weights by a
constant of the test function, uniformly in the scale.  What is added here is the
summability the passage to the full site sum needs, which the Green bound of
`ssec:green-estimates` supplies pair by pair, and the scale cut-off of
`Support/LinJacobianTestedStep1.lean`.
-/

open MeasureTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- The square of a finite Green combination is summable over the lattice: the
double sum expands into products `G(x,·)G(y,·)`, each summable in `d ≥ 5`. -/
theorem summable_sq_sum_green_weight (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (s : Finset (Site d)) (a : Site d → ℝ) :
    Summable fun z : Site d => (∑ x ∈ s, a x * green d x z) ^ 2 := by
  classical
  obtain ⟨-, -, -, ⟨C₁, hC₁, hgreen⟩, -⟩ := hGreen d hd
  have hsq : ∀ z : Site d, (∑ x ∈ s, a x * green d x z) ^ 2
      = ∑ x ∈ s, ∑ y ∈ s, (a x * a y) * (green d x z * green d y z) := by
    intro z
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  refine Summable.congr ?_ fun z => (hsq z).symm
  exact summable_sum fun x _ => summable_sum fun y _ => ((hgreen x y).1).mul_left (a x * a y)

/-- **The hypothesis `hB₀` of Step 2 at the tested weight.** -/
theorem exists_sum_testedGreenWeight_sq_le [NeZero d] (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (φ : Space d → ℝ) (hφ : ∀ z, 0 ≤ φ z) (Cφ L : ℝ) (hCφ : 0 ≤ Cφ) (hL : 0 ≤ L)
    (hb : ∀ z, |φ z| ≤ Cφ) (hint : Integrable φ) (n : ℝ → ℕ) :
    ∃ B₀ : ℝ, ∀ R : ℝ,
      ∑ v ∈ testedSites (Sandpile.Support.supportBox d R L) (n R),
        testedGreenWeight (Sandpile.Support.supportBox d R L)
          (testedWeightCut d R L φ) (n R) v ^ 2 ≤ B₀ := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_sum_tested_green_le hd hGreen φ Cφ L hCφ hL hb hint
  refine ⟨C, fun R => ?_⟩
  by_cases hR : 1 ≤ R
  · refine le_trans (sum_testedGreenWeight_sq_le hGreen hd _ _
      (fun x => testedWeightCut_nonneg R L hφ x) (n R) _
      (summable_sq_sum_green_weight hd hGreen _ _)) ?_
    refine le_trans (le_of_eq ?_) (hC R hR)
    refine tsum_congr fun z => ?_
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [testedWeightCut_eq_scaled hR L hφ hx,
      abs_of_nonneg (by rw [Sandpile.Support.cellMass]; exact integral_nonneg fun w => hφ w)]
  · have hzero : ∀ v : Site d,
        testedGreenWeight (Sandpile.Support.supportBox d R L)
          (testedWeightCut d R L φ) (n R) v = 0 := by
      intro v
      refine Finset.sum_eq_zero fun x _ => ?_
      simp only [testedWeightCut, if_neg hR, zero_mul]
    have : ∑ v ∈ testedSites (Sandpile.Support.supportBox d R L) (n R),
        testedGreenWeight (Sandpile.Support.supportBox d R L)
          (testedWeightCut d R L φ) (n R) v ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun v _ => ?_
      rw [hzero v]
      norm_num
    rw [this]
    exact hC0

end Sandpile
