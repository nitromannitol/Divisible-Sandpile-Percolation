import Sandpile.Support.LinStep2Pi
import Sandpile.Support.LinStep2Targets

/-!
# Step 2 of the path-survival lemma, with the paper's levels and weights in place

This module proves Step 2 of `lem:dgt4-path-survival` along one path, with the paper's own data
in place (`sandpile.tex:5529-5571`).

`Support/LinStep2Uniform.lean` proves the one-path bound for an abstract level function `b` and
an abstract weight family `\pi`. Here the level function is the paper's `b_r=\E u_{n-r-1}(0)`
clamped at the path length (`Sandpile.stepLevel`), the weights are the threshold probabilities
`\pi_{R,r}=\P(J(0)>b_r)` themselves, and the identity `\P(J(0)\leq b_r)=1-\pi_{R,r}` is the
complement identity of `Support/LinStep2Pi.lean`, read through the null measurability of the
threshold event. The smallness `\pi\leq1/2` that the logarithm expansion needs is
`weight_le_half`, whose hypothesis is `4G(0,0)\kappa\leq\varepsilon n_R`.

What is left to supply is exactly the paper's three inputs: the threshold-replacement error
`eq:dgt4-uniform-contact-thresholds` (`hthr` and `hwin`), the factorization of Step 1
(`hfact`), and `lem:dgt4-weighted-last-visits` (`hlv`). The main result is
`integral_abs_survival_sub_profile_le_steps`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- **Step 2 of `lem:dgt4-path-survival` along one path, with the paper's levels and
weights** (`sandpile.tex:5524-5566`).  The five errors are the threshold replacement, the
factorization of Step 1, the square sum of the weights, the mean last-visit defect, and the
product of the first with the last. -/
theorem integral_abs_survival_sub_profile_le_steps [NeZero d]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ)
    (hshift : ∀ (t : ℕ) (c : ℝ) (y : Site d),
      (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t y = 0} {σ : Site d → ℝ | c < J σ y})
        = (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t 0 = 0} {σ : Site d → ℝ | c < J σ 0}))
    (hnull : ∀ b : ℝ, NullMeasurableSet {σ : Site d → ℝ | b < J σ 0} (centeredMassLaw d ν))
    (hmono : Monotone (fun t : ℕ => meanOdometer (centeredMassLaw d ν) t))
    (hd3 : 3 ≤ d) (n j : ℕ) (hj : j < n) (ε : ℝ) (hε0 : 0 < ε)
    (hjn : (j : ℝ) ≤ (1 - ε) * (n : ℝ)) (κ : ℝ) (hκ : 0 < κ)
    (eta theta eta' : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1 / 2)
    (hn4 : 4 * (κ * green d 0 0) ≤ ε * (n : ℝ))
    (hthr : ∀ r, r ≤ j → ((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
        (symmDiff {σ : Site d → ℝ | odometer σ (n - r) 0 = 0}
          {σ : Site d → ℝ | stepLevel ν d n j r < J σ 0}) ≤ eta)
    (hwin : ∀ r ∈ Finset.range (j + 1),
      |((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
          {σ : Site d → ℝ | stepLevel ν d n j r < J σ 0} / (κ * green d 0 0) - 1| ≤ eta)
    (hfact : ∀ X : ℕ → Site d, ∀ (m : ℕ) (ts : Fin m → ℕ),
      Function.Injective (fun i => X (ts i)) → (m : ℝ) ≤ (j : ℝ) + 1 →
      |(centeredMassLaw d ν).real
          {σ : Site d → ℝ | ∀ i : Fin m, J σ (X (ts i)) ≤ stepLevel ν d n j (ts i)}
        - ∏ i : Fin m, (centeredMassLaw d ν).real
          {σ : Site d → ℝ | J σ 0 ≤ stepLevel ν d n j (ts i)}| ≤ theta)
    (hlv : ∫ X, |green d 0 0 * lvSum n j X + Real.log (1 - (j : ℝ) / (n : ℝ))|
      ∂(walkLaw d 0) ≤ eta') :
    ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
            (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - (1 - (j : ℝ) / (n : ℝ)) ^ κ|
        ∂(walkLaw d 0)
      ≤ eta * (1 + Real.log (1 / ε)) + theta
        + 16 * (κ * green d 0 0) ^ 2 / (ε * (n : ℝ))
        + (κ * eta' + eta * κ * (eta' + Real.log (1 / ε))) := by
  have hG : (0 : ℝ) < green d 0 0 := lt_of_lt_of_le zero_lt_one (one_le_green hd3)
  have hGk : (0 : ℝ) < κ * green d 0 0 := mul_pos hκ hG
  set pi : ℕ → ℝ := fun r => (centeredMassLaw d ν).real
    {σ : Site d → ℝ | stepLevel ν d n j r < J σ 0} with hpidef
  have heta1' : eta ≤ 1 := by linarith
  obtain ⟨hpiu, hpirel⟩ := weights_of_window n j hj pi (κ * green d 0 0) eta hGk heta1' hwin
  have hpih : ∀ r ∈ Finset.range (j + 1), pi r ≤ 1 / 2 :=
    weight_le_half n j hj ε (κ * green d 0 0) hε0 hGk hjn hn4 pi hpiu
  refine integral_abs_survival_sub_profile_le_window ν J (stepLevel ν d n j)
    (antitone_stepLevel ν n j hmono) hshift n j hj ε hε0 hjn eta theta eta' heta0 heta1'
    hthr hfact pi (fun r => ?_) κ (green d 0 0) hκ hG
    (fun r _ => measureReal_nonneg) hpih hwin hlv
  exact measureReal_le_eq_one_sub (centeredMassLaw d ν) (fun σ => J σ 0)
    (stepLevel ν d n j r) (hnull (stepLevel ν d n j r))

end Sandpile
