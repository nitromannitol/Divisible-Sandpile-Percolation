import Sandpile.Support.Dgt4AL2Bound

/-!
# The second moment of `D_n` at the optimized horizon

The second moment of `D_n` at the optimized horizon `T=n^{1/3}`:
`\E[D_n^2]\leq(2\E u_n(0)+M)n^{-2/3}`, so `(\E[D_n^2])^{1/2}\leq Cn^{-1/3}(\log(n+2))^{1/4}` once
`\E u_n(0)\leq C\sqrt{\log(n+2)}` (`eq:dgt4-gaussian-height-order`, `sandpile.tex:5035-5037`). The
exponent `1/3` is larger than the `1/4` that Step 1 needs after the telescoping, which is why the
fourth moment suffices in place of the paper's Gaussian concentration.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `\E[D_n^2]\leq(2\E u_n(0)+M)n^{-2/3}` (`sandpile.tex:5048-5052`). -/
theorem exists_integral_sceneryDeviation_sq_le_cube (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν)
    (hsq : Integrable (fun z : ℝ => |z| ^ (2 : ℝ)) ν)
    (hmom : Integrable (fun z : ℝ => |z| ^ (4 : ℝ)) ν) :
    ∃ M : ℝ, ∀ n : ℕ, 1 ≤ n →
      (∫ ζ, sceneryDeviation d ζ n ^ 2 ∂(LatticeProb.iidLaw d ν))
        ≤ (2 * meanOdometer (centeredMassLaw d ν) n + M) * (n : ℝ) ^ (-(2 : ℝ) / 3) := by
  obtain ⟨M, hM⟩ := Sandpile.exists_integral_sceneryDeviation_sq_le hd ν hint hmean hpos hsq hmom
  refine ⟨M, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hTpos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hn0 _
  have h := hM n hn ((n : ℝ) ^ ((1 : ℝ) / 3)) hTpos
  have hTn : (n : ℝ) ^ ((1 : ℝ) / 3) / (n : ℝ) = (n : ℝ) ^ (-(2 : ℝ) / 3) := by
    have hs := Real.rpow_sub hn0 ((1 : ℝ) / 3) 1
    rw [Real.rpow_one] at hs
    rw [← hs, show (1 : ℝ) / 3 - 1 = -(2 : ℝ) / 3 by norm_num]
  have hT2 : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (n : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hn0.le]
    norm_num
  have hinv : M / (n : ℝ) ^ ((2 : ℝ) / 3) = M * (n : ℝ) ^ (-(2 : ℝ) / 3) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le,
      show -((2 : ℝ) / 3) = -(2 : ℝ) / 3 by ring]
  rw [hT2, hinv] at h
  refine h.trans (le_of_eq ?_)
  rw [show (n : ℝ) ^ ((1 : ℝ) / 3)
        * (2 * Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / (n : ℝ))
      = 2 * Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n
        * ((n : ℝ) ^ ((1 : ℝ) / 3) / (n : ℝ)) by ring, hTn]
  ring


end Sandpile
