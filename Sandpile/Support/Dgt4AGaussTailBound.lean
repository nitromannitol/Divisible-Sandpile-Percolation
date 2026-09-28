import Sandpile.Support.Dgt4ADeviationLip
import Sandpile.Support.Dgt4ACoeffBound
import Mathlib.Probability.Moments.SubGaussian

/-!
# Gaussian tail bound for the centred deviation

The two-sided Gaussian tail of the centred deviation `D_n` of `sandpile.tex:5059-5061`:
`\P(|D_n|>t)\leq 2e^{-ct^2}`. The sub-Gaussian moment generating function of the centred
deviation is the input the paper's "Gaussian concentration" supplies; the tail bound is the
union bound over the two one-sided tails of Mathlib's `HasSubgaussianMGF.measure_ge_le`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- **The two-sided Gaussian tail of the centred deviation** from its sub-Gaussian
moment generating function (`sandpile.tex:5054-5056`). -/
theorem measure_abs_centeredDeviation_ge_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (c : ℝ≥0)
    (hmgf : HasSubgaussianMGF
      (fun ζ : Site d → ℝ => centeredDeviation d ζ n -
        ∫ η, centeredDeviation d η n ∂(LatticeProb.iidLaw d ν)) c (LatticeProb.iidLaw d ν))
    (t : ℝ) (ht : 0 ≤ t) :
    ((LatticeProb.iidLaw d ν).real
        {ζ | t ≤ |centeredDeviation d ζ n -
          ∫ η, centeredDeviation d η n ∂(LatticeProb.iidLaw d ν)|}) ≤
      2 * Real.exp (-t ^ 2 / (2 * (c : ℝ))) := by
  have h1 := hmgf.measure_ge_le ht
  have h2 := hmgf.neg.measure_ge_le ht
  have hset : {ζ : Site d → ℝ | t ≤ |centeredDeviation d ζ n
        - ∫ η, centeredDeviation d η n ∂(LatticeProb.iidLaw d ν)|}
      = {ζ : Site d → ℝ | t ≤ centeredDeviation d ζ n
          - ∫ η, centeredDeviation d η n ∂(LatticeProb.iidLaw d ν)}
        ∪ {ζ : Site d → ℝ | t ≤ -(centeredDeviation d ζ n
            - ∫ η, centeredDeviation d η n ∂(LatticeProb.iidLaw d ν))} := by
    ext ζ
    simp only [Set.mem_setOf_eq, Set.mem_union]
    rw [le_abs]
  rw [hset]
  calc ((LatticeProb.iidLaw d ν).real
        ({ζ : Site d → ℝ | t ≤ centeredDeviation d ζ n
              - ∫ η, centeredDeviation d η n ∂(LatticeProb.iidLaw d ν)}
          ∪ {ζ : Site d → ℝ | t ≤ -(centeredDeviation d ζ n
                - ∫ η, centeredDeviation d η n ∂(LatticeProb.iidLaw d ν))}))
      ≤ (LatticeProb.iidLaw d ν).real
          {ζ : Site d → ℝ | t ≤ centeredDeviation d ζ n
              - ∫ η, centeredDeviation d η n ∂(LatticeProb.iidLaw d ν)}
        + (LatticeProb.iidLaw d ν).real
            {ζ : Site d → ℝ | t ≤ -(centeredDeviation d ζ n
                - ∫ η, centeredDeviation d η n ∂(LatticeProb.iidLaw d ν))} :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * (c : ℝ))) + Real.exp (-t ^ 2 / (2 * (c : ℝ))) := add_le_add h1 h2
    _ = 2 * Real.exp (-t ^ 2 / (2 * (c : ℝ))) := by ring

end Sandpile
