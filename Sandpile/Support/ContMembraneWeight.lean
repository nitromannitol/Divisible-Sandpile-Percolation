/-
The time weight `(1 - r/T)^κ` of the power-weighted continuum membrane field
`ℋ_{κ,T}` (`eq:power-weighted-continuum-membrane`, `sandpile.tex:954-1069`) as a
function of the exponent.

This is the elementary half of the distinctness clause of
`thm:dgt4-many-limits`, which the paper states at `sandpile.tex:983-987`: "for
every `T > 0` and every nonzero nonnegative test function `φ`,
`Var(ℋ_{κ,T}(φ))` is strictly decreasing in `κ`".  Since
`0 < 1 - r/T < 1` for `r` in the open interval, the weight decreases in `κ`
there, strictly, and so does the product of the two weights the covariance is
built from.  What the covariance still needs is the exchange of the two space
integrals with the two time integrals, after which the comparison is the one
proved here against a bounded strictly positive kernel.
-/
import Sandpile.Continuum.Membrane

namespace Sandpile.Support

/-- The time weight lies strictly between zero and one on the open interval. -/
theorem membraneWeight_base_mem {T r : ℝ} (hT : 0 < T) (hr : 0 < r) (hrT : r < T) :
    0 < 1 - r / T ∧ 1 - r / T < 1 := by
  have h1 : r / T < 1 := (div_lt_one hT).mpr hrT
  have h2 : 0 < r / T := div_pos hr hT
  exact ⟨by linarith, by linarith⟩

/-- The time weight decreases in the exponent. -/
theorem membraneWeight_le {T r κ κ' : ℝ} (hT : 0 < T) (hr : 0 ≤ r) (hrT : r ≤ T)
    (hκ : 0 ≤ κ) (h : κ ≤ κ') : (1 - r / T) ^ κ' ≤ (1 - r / T) ^ κ := by
  have h1 : r / T ≤ 1 := (div_le_one hT).mpr hrT
  have h2 : 0 ≤ r / T := div_nonneg hr hT.le
  exact Real.rpow_le_rpow_of_exponent_ge' (by linarith) (by linarith) hκ h

/-- The time weight decreases strictly in the exponent on the open interval. -/
theorem membraneWeight_lt {T r κ κ' : ℝ} (hT : 0 < T) (hr : 0 < r) (hrT : r < T)
    (h : κ < κ') : (1 - r / T) ^ κ' < (1 - r / T) ^ κ := by
  obtain ⟨h0, h1⟩ := membraneWeight_base_mem hT hr hrT
  exact Real.rpow_lt_rpow_of_exponent_gt h0 h1 h

/-- The time weight is nonnegative. -/
theorem membraneWeight_nonneg {T r κ : ℝ} (hT : 0 < T) (hrT : r ≤ T) :
    0 ≤ (1 - r / T) ^ κ := by
  have h1 : r / T ≤ 1 := (div_le_one hT).mpr hrT
  exact Real.rpow_nonneg (by linarith) _

/-- **The product of the two time weights of the covariance decreases strictly in
the exponent** on the open square, which is what makes the variance of
`ℋ_{κ,T}(φ)` strictly decreasing in `κ` for a nonzero nonnegative test function. -/
theorem membraneWeight_mul_lt {T r r' κ κ' : ℝ} (hT : 0 < T) (hr : 0 < r) (hrT : r < T)
    (hr' : 0 < r') (hrT' : r' < T) (h : κ < κ') :
    (1 - r / T) ^ κ' * (1 - r' / T) ^ κ' < (1 - r / T) ^ κ * (1 - r' / T) ^ κ := by
  obtain ⟨h0, h1⟩ := membraneWeight_base_mem hT hr hrT
  obtain ⟨h0', h1'⟩ := membraneWeight_base_mem hT hr' hrT'
  have hA : (1 - r / T) ^ κ' < (1 - r / T) ^ κ := membraneWeight_lt hT hr hrT h
  have hB : (1 - r' / T) ^ κ' < (1 - r' / T) ^ κ := membraneWeight_lt hT hr' hrT' h
  have hA0 : 0 < (1 - r / T) ^ κ' := Real.rpow_pos_of_pos h0 _
  have hB0 : 0 < (1 - r' / T) ^ κ' := Real.rpow_pos_of_pos h0' _
  calc (1 - r / T) ^ κ' * (1 - r' / T) ^ κ'
      < (1 - r / T) ^ κ * (1 - r' / T) ^ κ' := by
        exact mul_lt_mul_of_pos_right hA hB0
    _ < (1 - r / T) ^ κ * (1 - r' / T) ^ κ := by
        refine mul_lt_mul_of_pos_left hB ?_
        exact lt_trans hA0 hA

end Sandpile.Support
