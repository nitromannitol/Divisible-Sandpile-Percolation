import Sandpile.External.RSW.ScaleInterpolation

/-!
# Interpolation from a divisible base scale

Geometric scales starting at any positive integer base cover all larger scales within a
factor of four.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- Every scale above a positive base lies between two consecutive base-four scales. -/
theorem exists_base_four_scale {M n : ℕ} (hM : 0 < M) (hn : M ≤ n) :
    ∃ j : ℕ, M * 4 ^ j ≤ n ∧ n ≤ 4 * (M * 4 ^ j) := by
  let q := n / M
  have hq : 0 < q := Nat.div_pos hn hM
  let j := Nat.log 4 q
  have hsmall : 4 ^ j ≤ q := Nat.pow_log_le_self 4 (by omega)
  have hlarge : q < 4 * 4 ^ j := by
    have hh := Nat.lt_pow_succ_log_self (b := 4) (by decide) q
    simpa only [pow_succ, Nat.mul_comm] using hh
  refine ⟨j, ?_, ?_⟩
  · exact (Nat.mul_le_mul_left M hsmall).trans (Nat.mul_div_le n M)
  · have hdiv := Nat.div_add_mod n M
    have hmod := Nat.mod_lt n hM
    have hbound : n < M * (q + 1) := by
      dsimp [q]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hscale : M * (q + 1) ≤ 4 * (M * 4 ^ j) := by
      have hh := Nat.mul_le_mul_left M (show q + 1 ≤ 4 * 4 ^ j by omega)
      nlinarith
    exact (hbound.le.trans hscale)

/-- A comparison at aspect eight on base-four scales above a base `M` implies the
aspect-two comparison at every scale at least `M`. -/
theorem crossing_comparison_two_of_eight_base_four (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (ψ : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1)
    {M n : ℕ} (hM : 0 < M) (hn : M ≤ n) (level : ℝ)
    (h : ∀ j : ℕ,
      (ψ (probabilityInUnitInterval μ
        (planarCrossingEvent (2 * (M * 4 ^ j)) (16 * (M * 4 ^ j)) level)) : ℝ) ≤
        μ.real (planarCrossingEvent (16 * (M * 4 ^ j)) (2 * (M * 4 ^ j)) level)) :
    (ψ (probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (4 * n) level)) : ℝ) ≤
      μ.real (planarCrossingEvent (4 * n) (2 * n) level) := by
  obtain ⟨j, hj₁, hj₂⟩ := exists_base_four_scale hM hn
  exact crossing_comparison_two_of_eight μ ψ hj₁ hj₂ level (h j)

end Sandpile.External.RSW
