/-
Step 2 of `lem:dgt4-path-survival` along one path, with the errors in the form
`eq:dgt4-uniform-contact-thresholds` supplies them (`sandpile.tex:5529-5583`).

The paper's hypothesis is a bound on `|m\P(J(0)>\E u_{m-1}(0))/(G(0,0)\kappa)-1|` uniformly
over the window `\lceil\varepsilon n_R\rceil\leq m\leq n_R`.  With `m=n_R-r` that is a
RELATIVE bound on the weights, and `weights_of_window` reads off the two forms the chain
consumes: the uniform upper bound `\pi_{R,r}\leq2G(0,0)\kappa/(n_R-r)` and the relative
deviation from `G(0,0)\kappa/(n_R-r)`.

The other two window bounds are the paper's two constants.  `harmonic_window_le` is
`\sum_{m=\lceil\varepsilon n_R\rceil}^{n_R}1/m\leq1+\log(1/\varepsilon)`, which is what
multiplies the threshold-replacement error at `sandpile.tex:5545-5547`, and
`neg_log_window_le` is `-\log(1-j/n_R)\leq\log(1/\varepsilon)`, which is what multiplies
the relative weight error in the profile comparison.

`integral_abs_survival_sub_profile_le_window` collects them: along a path of at most
`(1-\varepsilon)n_R` steps the survival probability differs from `(1-j/n_R)^\kappa` in
mean by at most
`\eta(1+\log(1/\varepsilon))+\theta+16(G(0,0)\kappa)^2/(\varepsilon n_R)
 +\kappa\eta'+\eta\kappa(\eta'+\log(1/\varepsilon))`,
with `\eta` the window bound, `\theta` the factorization error of Step 1 and `\eta'` the
mean last-visit defect of `lem:dgt4-weighted-last-visits`.  Every one of the four tends to
zero, which is the paper's "each summand tends to zero uniformly for `j\leq(1-\varepsilon)n_R`".
-/
import Sandpile.Support.LinStep2Weights

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The truncated subtraction of the window agrees with the real one below the horizon. -/
theorem cast_nat_sub_eq (n r : ℕ) (hr : r ≤ n) : ((n - r : ℕ) : ℝ) = (n : ℝ) - (r : ℝ) := by
  push_cast [Nat.cast_sub hr]
  ring

/-- **The two forms of the paper's weight asymptotic** (`sandpile.tex:5558-5559`): a relative
error `\eta` in `m\pi_{R,r}/(G(0,0)\kappa)` gives both the uniform upper bound
`2G(0,0)\kappa/(n_R-r)` and the relative deviation from `G(0,0)\kappa/(n_R-r)`. -/
theorem weights_of_window (n j : ℕ) (hj : j < n) (pi : ℕ → ℝ) (Gk eta : ℝ) (hGk : 0 < Gk)
    (heta1 : eta ≤ 1)
    (hwin : ∀ r ∈ Finset.range (j + 1), |((n - r : ℕ) : ℝ) * pi r / Gk - 1| ≤ eta) :
    (∀ r ∈ Finset.range (j + 1), pi r ≤ 2 * Gk / ((n - r : ℕ) : ℝ)) ∧
      (∀ r ∈ Finset.range (j + 1),
        |pi r - Gk * (1 / ((n : ℝ) - (r : ℝ)))|
          ≤ eta * (Gk * (1 / ((n : ℝ) - (r : ℝ))))) := by
  have hpos : ∀ r ∈ Finset.range (j + 1), 0 < n - r := by
    intro r hr
    have := Finset.mem_range.mp hr
    omega
  constructor
  · intro r hr
    exact weight_le_of_abs_le (n - r) (hpos r hr) Gk eta (pi r) hGk heta1 (hwin r hr)
  · intro r hr
    have hrn : r ≤ n := by
      have := Finset.mem_range.mp hr
      omega
    have h := abs_weight_sub_le (n - r) (hpos r hr) Gk eta (pi r) hGk (hwin r hr)
    rw [cast_nat_sub_eq n r hrn] at h
    have hid : Gk / ((n : ℝ) - (r : ℝ)) = Gk * (1 / ((n : ℝ) - (r : ℝ))) := by
      rw [mul_one_div]
    rwa [hid] at h

/-- **The harmonic factor of the replacement error** (`sandpile.tex:5540-5542`):
`\sum_{r\leq j}1/(n_R-r)\leq1+\log(1/\varepsilon)` on the window. -/
theorem harmonic_window_le (n j : ℕ) (hj : j < n) (epsw : ℝ) (heps0 : 0 < epsw)
    (hjn : (j : ℝ) ≤ (1 - epsw) * (n : ℝ)) :
    ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ ≤ 1 + Real.log (1 / epsw) := by
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le j) hj
  have hnj1 : 1 ≤ n - j := by omega
  have hnjn : n - j ≤ n := by omega
  have h1 := sum_inv_range_sub_eq n j (le_of_lt hj)
  have h2 := sum_inv_Icc_le (n - j) n hnj1 hnjn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnjR : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by exact_mod_cast hnj1
  have hge : epsw * (n : ℝ) ≤ ((n - j : ℕ) : ℝ) := by
    rw [cast_nat_sub_eq n j (le_of_lt hj)]
    nlinarith [hjn]
  have hlog : Real.log ((n : ℝ) / ((n - j : ℕ) : ℝ)) ≤ Real.log (1 / epsw) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ hnjR heps0]
    nlinarith [hge]
  rw [h1]
  linarith [h2, hlog]

/-- **The profile factor of the relative weight error**: `-\log(1-j/n_R)\leq\log(1/\varepsilon)`
on the window. -/
theorem neg_log_window_le (n j : ℕ) (hj : j < n) (epsw : ℝ) (heps0 : 0 < epsw)
    (hjn : (j : ℝ) ≤ (1 - epsw) * (n : ℝ)) :
    -Real.log (1 - (j : ℝ) / (n : ℝ)) ≤ Real.log (1 / epsw) := by
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le j) hj
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hbase : epsw ≤ 1 - (j : ℝ) / (n : ℝ) := by
    have hdiv : (j : ℝ) / (n : ℝ) ≤ 1 - epsw := by
      rw [div_le_iff₀ hnR]
      nlinarith [hjn]
    linarith
  have hlog : Real.log epsw ≤ Real.log (1 - (j : ℝ) / (n : ℝ)) :=
    Real.log_le_log heps0 hbase
  have : Real.log (1 / epsw) = -Real.log epsw := by
    rw [one_div, Real.log_inv]
  linarith [hlog, this.le, this.ge]

/-- **Step 2 of `lem:dgt4-path-survival` along one path of at most `(1-\varepsilon)n_R`
steps** (`sandpile.tex:5524-5566`), with the four errors in the form the hypothesis
`eq:dgt4-uniform-contact-thresholds`, Step 1 and `lem:dgt4-weighted-last-visits` supply. -/
theorem integral_abs_survival_sub_profile_le_window [NeZero d]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ) (b : ℕ → ℝ) (hb : Antitone b)
    (hshift : ∀ (t : ℕ) (c : ℝ) (y : Site d),
      (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t y = 0} {σ : Site d → ℝ | c < J σ y})
        = (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t 0 = 0} {σ : Site d → ℝ | c < J σ 0}))
    (n j : ℕ) (hj : j < n) (epsw : ℝ) (heps0 : 0 < epsw)
    (hjn : (j : ℝ) ≤ (1 - epsw) * (n : ℝ))
    (eta theta eta' : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hthr : ∀ r, r ≤ j → ((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
        (symmDiff {σ : Site d → ℝ | odometer σ (n - r) 0 = 0}
          {σ : Site d → ℝ | b r < J σ 0}) ≤ eta)
    (hfact : ∀ X : ℕ → Site d, ∀ (m : ℕ) (ts : Fin m → ℕ),
      Function.Injective (fun i => X (ts i)) → (m : ℝ) ≤ (j : ℝ) + 1 →
      |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ i : Fin m, J σ (X (ts i)) ≤ b (ts i)}
        - ∏ i : Fin m, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b (ts i)}|
        ≤ theta)
    (pi : ℕ → ℝ)
    (hpi : ∀ r, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b r} = 1 - pi r)
    (kappa G : ℝ) (hkappa : 0 < kappa) (hG : 0 < G)
    (hpi0 : ∀ r ∈ Finset.range (j + 1), 0 ≤ pi r)
    (hpih : ∀ r ∈ Finset.range (j + 1), pi r ≤ 1 / 2)
    (hwin : ∀ r ∈ Finset.range (j + 1),
      |((n - r : ℕ) : ℝ) * pi r / (kappa * G) - 1| ≤ eta)
    (hlvint : ∫ X, |G * lvSum n j X + Real.log (1 - (j : ℝ) / (n : ℝ))| ∂(walkLaw d 0)
      ≤ eta') :
    ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
            (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - (1 - (j : ℝ) / (n : ℝ)) ^ kappa|
        ∂(walkLaw d 0)
      ≤ eta * (1 + Real.log (1 / epsw)) + theta
        + 16 * (kappa * G) ^ 2 / (epsw * (n : ℝ))
        + (kappa * eta' + eta * kappa * (eta' + Real.log (1 / epsw))) := by
  have hGk : (0 : ℝ) < kappa * G := mul_pos hkappa hG
  obtain ⟨hpiu, hpirel⟩ := weights_of_window n j hj pi (kappa * G) eta hGk heta1 hwin
  have hbase := integral_abs_survival_sub_profile_le ν J b hb hshift n j hj eta theta hthr
    hfact pi hpi kappa G eta eta' hpi0 hpih hpiu hpirel hkappa hG.le heta0 hlvint
  have hH := harmonic_window_le n j hj epsw heps0 hjn
  have hL := neg_log_window_le n j hj epsw heps0 hjn
  have hnjR : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by
    have : 0 < n - j := by omega
    exact_mod_cast this
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le j) hj
    exact_mod_cast this
  have hge : epsw * (n : ℝ) ≤ ((n - j : ℕ) : ℝ) := by
    rw [cast_nat_sub_eq n j (le_of_lt hj)]
    nlinarith [hjn]
  have hsq : 2 * ((2 * (kappa * G)) ^ 2 * (2 / ((n - j : ℕ) : ℝ)))
      ≤ 16 * (kappa * G) ^ 2 / (epsw * (n : ℝ)) := by
    have hinv : 1 / ((n - j : ℕ) : ℝ) ≤ 1 / (epsw * (n : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hge
    have hid1 : 2 * ((2 * (kappa * G)) ^ 2 * (2 / ((n - j : ℕ) : ℝ)))
        = 16 * (kappa * G) ^ 2 * (1 / ((n - j : ℕ) : ℝ)) := by ring
    have hid2 : 16 * (kappa * G) ^ 2 / (epsw * (n : ℝ))
        = 16 * (kappa * G) ^ 2 * (1 / (epsw * (n : ℝ))) := by ring
    rw [hid1, hid2]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have h1 : eta * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹
      ≤ eta * (1 + Real.log (1 / epsw)) := mul_le_mul_of_nonneg_left hH heta0
  have h2 : eta * kappa * (eta' - Real.log (1 - (j : ℝ) / (n : ℝ)))
      ≤ eta * kappa * (eta' + Real.log (1 / epsw)) :=
    mul_le_mul_of_nonneg_left (by linarith [hL]) (mul_nonneg heta0 hkappa.le)
  linarith [hbase, h1, h2, hsq]

end Sandpile
