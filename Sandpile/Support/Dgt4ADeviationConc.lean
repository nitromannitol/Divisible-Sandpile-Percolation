/-
The Gaussian concentration of the centred deviation `D_n` of `sandpile.tex:5059-5061`:
`\P(|D_n|>t)\leq2e^{-ct^2}`, from the cited Gaussian concentration for a Lipschitz
functional (`Sandpile.External.GaussianLipschitzConcentration`) at the `\ell^2` Lipschitz
constant `2\|G(0,\cdot)\|` of `abs_centeredDeviation_sub_le_of_hasSum_sq`.  The two-sided
bound is the union bound over the two one-sided tails.
-/
import Sandpile.Support.Dgt4ADeviationL2Lip
import Sandpile.Support.Dgt4ATwoSided
import Sandpile.Support.Dgt4ACondition
import Sandpile.External.GaussianLipschitzConcentration

open MeasureTheory ProbabilityTheory Filter Topology Set

open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- **The two-sided Gaussian tail of `D_n`** (`sandpile.tex:5054-5056`). -/
theorem measure_abs_centeredDeviation_ge_le_of_conc
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration) (hd : 5 ≤ d)
    (n : ℕ)
    (hmeas : Measurable fun ζ : Site d → ℝ => centeredDeviation d ζ n)
    (hint : Integrable (fun ζ : Site d → ℝ => centeredDeviation d ζ n)
      (LatticeProb.gaussLaw (Site d)))
    (hξ : ∀ ζ : Site d → ℝ, ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m => infiniteGreenFieldPartial m ζ y) atTop (𝓝 L))
    (t : ℝ) (ht : 0 ≤ t) :
    (LatticeProb.gaussLaw (Site d))
        {ζ | t ≤ |centeredDeviation d ζ n
          - ∫ η, centeredDeviation d η n ∂(LatticeProb.gaussLaw (Site d))|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) /
          (2 * (2 * ‖greenLp d hd (0 : Site d)‖) ^ 2))) := by
  set L : ℝ := 2 * ‖greenLp d hd (0 : Site d)‖ with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    have := norm_greenLp_pos hd
    positivity
  have hlip : ∀ (ω η : Site d → ℝ) (M : ℝ), HasSum (fun z => (ω z - η z) ^ 2) M →
      |centeredDeviation d ω n - centeredDeviation d η n| ≤ L * Real.sqrt M := by
    intro ω η M hM
    rw [hLdef]
    exact abs_centeredDeviation_sub_le_of_hasSum_sq hd ω η M hM (hξ ω) n
  have hup := hGaussConc (Site d) (fun ζ => centeredDeviation d ζ n) L hLpos hmeas hint hlip
  have hneg : Integrable (fun ζ : Site d → ℝ => -centeredDeviation d ζ n)
      (LatticeProb.gaussLaw (Site d)) := hint.neg
  have hlipneg : ∀ (ω η : Site d → ℝ) (M : ℝ), HasSum (fun z => (ω z - η z) ^ 2) M →
      |(-centeredDeviation d ω n) - (-centeredDeviation d η n)| ≤ L * Real.sqrt M := by
    intro ω η M hM
    rw [neg_sub_neg, abs_sub_comm]
    exact hlip ω η M hM
  have hupneg := hGaussConc (Site d) (fun ζ => -centeredDeviation d ζ n) L hLpos
    hmeas.neg hneg hlipneg
  have hmeanneg : ∫ η, -centeredDeviation d η n ∂(LatticeProb.gaussLaw (Site d))
      = -(∫ η, centeredDeviation d η n ∂(LatticeProb.gaussLaw (Site d))) := integral_neg _
  rw [hmeanneg] at hupneg
  have hlo : ∀ s : ℝ, 0 ≤ s →
      (LatticeProb.gaussLaw (Site d))
        {ζ | centeredDeviation d ζ n + s
          ≤ ∫ η, centeredDeviation d η n ∂(LatticeProb.gaussLaw (Site d))}
      ≤ ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * L ^ 2))) := by
    intro s hs
    have h := hupneg s hs
    have hset : {ζ : Site d → ℝ | -(∫ η, centeredDeviation d η n
          ∂(LatticeProb.gaussLaw (Site d))) + s ≤ -centeredDeviation d ζ n}
        = {ζ : Site d → ℝ | centeredDeviation d ζ n + s
          ≤ ∫ η, centeredDeviation d η n ∂(LatticeProb.gaussLaw (Site d))} := by
      ext ζ
      simp only [Set.mem_setOf_eq]
      constructor <;> intro hh <;> linarith
    rw [hset] at h
    exact h
  have h2 := measure_abs_sub_mean_ge_le_two_mul (LatticeProb.gaussLaw (Site d))
    (fun ζ => centeredDeviation d ζ n) L hLpos hup hlo t ht
  rw [hLdef] at h2
  exact h2

end Sandpile
