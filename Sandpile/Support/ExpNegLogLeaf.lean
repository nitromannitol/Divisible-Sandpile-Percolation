import Mathlib

/-!
# An elementary exponential decay leaf

An elementary decay leaf: `exp (-k * log r) < q` eventually.
-/

open Filter Real

namespace Sandpile

/-- `Real.exp (-(k * Real.log r))` is eventually, in `r : ℕ`, less than `q`: past the
threshold `r₀ = ⌈exp (-(log q) / k)⌉ + 1`, taking logarithms and using the monotonicity of
`Real.exp` and `Real.log` turns the claim into the elementary comparison `-(log q)/k < log r`.
-/
lemma eventually_exp_neg_mul_log_lt {k q : ℝ} (hk : 0 < k) (hq : 0 < q) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → Real.exp (-(k * Real.log (r : ℝ))) < q := by
  have hR : 0 < Real.exp (-(Real.log q) / k) := Real.exp_pos _
  refine ⟨Nat.ceil (Real.exp (-(Real.log q) / k)) + 1, fun r hr => ?_⟩
  have hpos : 0 < Nat.ceil (Real.exp (-(Real.log q) / k)) := Nat.ceil_pos.mpr hR
  have hr1 : 1 ≤ r := by omega
  have hlt : Real.exp (-(Real.log q) / k) < (r : ℝ) := by
    have h1 : Real.exp (-(Real.log q) / k) ≤ ((Nat.ceil (Real.exp (-(Real.log q) / k)) : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp (-(Real.log q) / k)) : ℕ) : ℝ) < (r : ℝ) := by
      exact_mod_cast hr
    exact lt_of_le_of_lt h1 h2
  have hlog : -(Real.log q) / k < Real.log (r : ℝ) := by
    have h := Real.log_lt_log hR hlt
    rwa [Real.log_exp] at h
  have hneg : -(k : ℝ) < 0 := by linarith
  have h2 := mul_lt_mul_of_neg_left hlog hneg
  have e1 : (-(k : ℝ)) * Real.log (r : ℝ) = -(k * Real.log (r : ℝ)) := by ring
  have e2 : (-(k : ℝ)) * (-(Real.log q) / k) = Real.log q := by field_simp
  rw [e1, e2] at h2
  have hq' : q = Real.exp (Real.log q) := (Real.exp_log hq).symm
  rw [hq']
  exact Real.exp_lt_exp.mpr h2

end Sandpile