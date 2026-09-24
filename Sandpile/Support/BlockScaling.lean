/-
Deterministic scaling arithmetic for the final step of the proof of
`thm:d4-critical-level-percolation` (`sandpile.tex:4067-4071`): with
`r = ⌊√(t/(A_ex+1))⌋` one has `(A_ex+1) r² ≤ t`, and `log r ≥ (1/3) log t`
for all large `t`, so a level `c log r` bounds the level `c/3 log t` from
above and the odometer is monotone in time.
-/
import Mathlib

open MeasureTheory

namespace Sandpile

/-- With `r = ⌊√(t/(A_ex+1))⌋` the block time `(A_ex+1) r²` is at most `t`. -/
theorem floor_sqrt_mul_le (Aex : ℕ) (t : ℕ) :
    (Aex + 1) * (Nat.floor (Real.sqrt ((t : ℝ) / (Aex + 1)))) ^ 2 ≤ t := by
  set s := Nat.floor (Real.sqrt ((t : ℝ) / (Aex + 1))) with hs
  have hn : (0:ℝ) ≤ (t:ℝ)/(Aex+1) := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hsn : (0:ℝ) ≤ Real.sqrt ((t:ℝ)/(Aex+1)) := Real.sqrt_nonneg _
  have hs' : ((s:ℝ)) ≤ Real.sqrt ((t:ℝ)/(Aex+1)) := Nat.floor_le hsn
  have hsq : ((s:ℝ))^2 ≤ (t:ℝ)/(Aex+1) := by
    have h : ((s:ℝ)) * ((s:ℝ)) ≤ Real.sqrt ((t:ℝ)/(Aex+1)) * Real.sqrt ((t:ℝ)/(Aex+1)) :=
      mul_self_le_mul_self (Nat.cast_nonneg s) hs'
    rw [Real.mul_self_sqrt hn] at h
    nlinarith [h]
  have h4 : ((Aex+1):ℝ) * ((s:ℝ))^2 ≤ (t:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ ((Aex+1):ℝ))
    have hcancel : ((Aex+1):ℝ) * ((t:ℝ)/(Aex+1)) = (t:ℝ) := by field_simp
    linarith [h, hcancel]
  have h5 : ((Aex+1) * s ^ 2 : ℕ) ≤ t := by
    have h' : ((Aex+1) * s ^ 2 : ℝ) ≤ (t:ℝ) := by linarith
    exact_mod_cast h'
  exact h5

/-- For `A_ex ≥ 1` and all large `t`, the scale `r = ⌊√(t/(A_ex+1))⌋` is at
least `2` and `log r ≥ (1/4) log t`. -/
theorem exists_log_floor_sqrt (Aex : ℕ) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → 2 ≤ Nat.floor (Real.sqrt ((t : ℝ) / (Aex + 1))) ∧
      (1 / 4 : ℝ) * Real.log t
        ≤ Real.log (Nat.floor (Real.sqrt ((t : ℝ) / (Aex + 1)))) := by
  refine ⟨256 * (Aex + 1) ^ 4 + 1, ?_⟩
  intro t ht
  have hA1 : (1:ℝ) ≤ ((Aex+1):ℝ) := by
    have : (1:ℕ) ≤ Aex + 1 := by omega
    exact_mod_cast this
  have hA0 : (0:ℝ) < ((Aex+1):ℝ) := by linarith
  have hAne : ((Aex+1):ℝ) ≠ 0 := ne_of_gt hA0
  have htpos : (0:ℝ) < (t:ℝ) := by
    have h1t : (1:ℕ) ≤ t := by omega
    have : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast h1t
    linarith
  -- power bounds
  have hq : (((Aex+1):ℝ))^4 ≤ (t:ℝ) := by
    have h3 : ((Aex+1)^4 : ℕ) ≤ t := by omega
    exact_mod_cast h3
  have hq2 : (256:ℝ) * ((Aex+1):ℝ)^2 ≤ (t:ℝ)/((Aex+1):ℝ) := by
    have h5 : ((256:ℝ) * ((Aex+1):ℝ)^4 < (t:ℝ)) := by
      have h6 : ((256*(Aex+1)^4 : ℕ) < t) := by omega
      exact_mod_cast h6
    have h6 : ((256:ℝ) * ((Aex+1):ℝ)^2) * ((Aex+1):ℝ) ≤ (t:ℝ) := by nlinarith [h5]
    have h7 : ((256:ℝ) * ((Aex+1):ℝ)^2) * ((Aex+1):ℝ)
        ≤ (t:ℝ)/((Aex+1):ℝ) * ((Aex+1):ℝ) := by
      rw [div_mul_cancel₀ _ hAne]; exact h6
    have h8 : (0:ℝ) ≤ (t:ℝ) := by positivity
    have h9 : (0:ℝ) ≤ (t:ℝ)/((Aex+1):ℝ) := by
      apply div_nonneg _ hA0.le
      positivity
    nlinarith [h7, hA0, h9]
  have hq3 : ((Aex+1):ℝ)^3 ≤ (t:ℝ)/((Aex+1):ℝ) := by
    have h6 : ((Aex+1):ℝ)^3 * ((Aex+1):ℝ) ≤ (t:ℝ) := by nlinarith [hq]
    have h7 : ((Aex+1):ℝ)^3 * ((Aex+1):ℝ)
        ≤ (t:ℝ)/((Aex+1):ℝ) * ((Aex+1):ℝ) := by
      rw [div_mul_cancel₀ _ hAne]; exact h6
    have h9 : (0:ℝ) ≤ (t:ℝ)/((Aex+1):ℝ) := by
      apply div_nonneg _ hA0.le
      positivity
    nlinarith [h7, hA0, h9]
  -- sqrt lower bounds
  have hs16 : (16:ℝ) ≤ Real.sqrt ((t:ℝ)/((Aex+1):ℝ)) := by
    have h5 : Real.sqrt ((256:ℝ) * ((Aex+1):ℝ)^2)
        ≤ Real.sqrt ((t:ℝ)/((Aex+1):ℝ)) := Real.sqrt_le_sqrt hq2
    have h6 : ((256:ℝ) * ((Aex+1):ℝ)^2) = ((16:ℝ)*((Aex+1):ℝ))^2 := by ring
    rw [h6, Real.sqrt_sq (by nlinarith : (0:ℝ) ≤ (16:ℝ)*((Aex+1):ℝ))] at h5
    have h7 : (16:ℝ) ≤ (16:ℝ)*((Aex+1):ℝ) := by nlinarith [hA1]
    linarith
  have hsA : ((Aex+1):ℝ) ≤ Real.sqrt ((t:ℝ)/((Aex+1):ℝ)) := by
    rw [Real.le_sqrt hA0.le
      (div_nonneg (Nat.cast_nonneg _) hA0.le)]
    have h10 : ((Aex+1):ℝ)^2 ≤ ((Aex+1):ℝ)^3 := by nlinarith [hA1]
    have h11 : ((Aex+1):ℝ)^3 ≤ (t:ℝ)/((Aex+1):ℝ) := hq3
    linarith
  -- floor bounds
  have hfl2 : 2 ≤ Nat.floor (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) := by
    exact Nat.le_floor (n := 2) (by nlinarith [hs16])
  have hflhalf : Real.sqrt ((t:ℝ)/((Aex+1):ℝ)) / 2
      ≤ Nat.floor (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) := by
    have h9 : Real.sqrt ((t:ℝ)/((Aex+1):ℝ))
        < (Nat.floor (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h10 : (2:ℝ) ≤ Real.sqrt ((t:ℝ)/((Aex+1):ℝ)) := by nlinarith [hs16]
    have h11 : (2:ℝ) * (Nat.floor (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) : ℝ)
        ≥ Real.sqrt ((t:ℝ)/((Aex+1):ℝ)) := by nlinarith [h9, h10]
    have h12 : (0:ℝ) < 2 := by norm_num
    nlinarith [h11, h12]
  -- log bounds
  have hsq : (0:ℝ) < Real.sqrt ((t:ℝ)/((Aex+1):ℝ)) := by
    apply Real.sqrt_pos_of_pos
    exact div_pos htpos hA0
  have hflpos : (0:ℝ) < (Nat.floor (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) : ℝ) := by
    have : (2:ℝ) ≤ Nat.floor (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) := by
      exact_mod_cast hfl2
    linarith
  have hlogt : Real.log (t:ℝ)
      = Real.log ((Aex+1):ℝ) + Real.log ((t:ℝ)/((Aex+1):ℝ)) := by
    rw [Real.log_div htpos.ne' hAne]
    ring
  have hlogA : Real.log ((Aex+1):ℝ) ≤ Real.log (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) :=
    Real.log_le_log hA0 hsA
  have hlogdiv : Real.log ((t:ℝ)/((Aex+1):ℝ))
      = 2 * Real.log (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) := by
    have h1 : (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))
          * Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) = (t:ℝ)/((Aex+1):ℝ) :=
      Real.mul_self_sqrt (div_nonneg htpos.le hA0.le)
    have h2 : Real.log ((t:ℝ)/((Aex+1):ℝ))
        = Real.log (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))
          * Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) := by
      rw [h1]
    rw [h2, Real.log_mul hsq.ne' hsq.ne']
    ring
  have hloghalf : Real.log 2
      ≤ (1/4:ℝ) * Real.log (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) := by
    have h8 : (16:ℝ) ≤ Real.sqrt ((t:ℝ)/((Aex+1):ℝ)) := hs16
    have h8log : Real.log 16
        ≤ Real.log (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) :=
      Real.log_le_log (by norm_num) h8
    have h8eq : Real.log 16 = 4 * Real.log 2 := by
      have : (16:ℝ) = (2:ℝ)^(4:ℕ) := by norm_num
      rw [this, Real.log_pow]
      ring
    rw [h8eq] at h8log
    linarith
  have hlogfloor : Real.log (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) - Real.log 2
      ≤ Real.log (Nat.floor (Real.sqrt ((t:ℝ)/((Aex+1):ℝ)))) := by
    have h9 : Real.sqrt ((t:ℝ)/((Aex+1):ℝ)) / 2
        ≤ (Nat.floor (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) : ℝ) := hflhalf
    have h10 : (0:ℝ) < Real.sqrt ((t:ℝ)/((Aex+1):ℝ)) / 2 := by
      apply div_pos hsq _
      norm_num
    have h11 : Real.log (Real.sqrt ((t:ℝ)/((Aex+1):ℝ)) / 2)
        ≤ Real.log (Nat.floor (Real.sqrt ((t:ℝ)/((Aex+1):ℝ)))) :=
      Real.log_le_log h10 h9
    rw [Real.log_div hsq.ne' (by norm_num : ((2:ℝ)) ≠ 0)] at h11
    linarith
  refine ⟨hfl2, ?_⟩
  rw [hlogt, hlogdiv]
  have h5 : Real.log (Real.sqrt ((t:ℝ)/((Aex+1):ℝ)))
      ≤ Real.log (Nat.floor (Real.sqrt ((t:ℝ)/((Aex+1):ℝ)))) + Real.log 2 := by
    linarith [hlogfloor]
  have h6 : (1/4:ℝ) * (Real.log ((Aex+1):ℝ)
      + 2 * Real.log (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))))
      ≤ Real.log (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) - Real.log 2 := by
    have h7 : Real.log ((Aex+1):ℝ)
        ≤ Real.log (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) := hlogA
    have h8 : Real.log 2
        ≤ (1/4:ℝ) * Real.log (Real.sqrt ((t:ℝ)/((Aex+1):ℝ))) := hloghalf
    linarith
  linarith


end Sandpile