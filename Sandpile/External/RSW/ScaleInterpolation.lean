import Sandpile.Support.RectangleMonotonicity

/-!
# Interpolation of rectangle crossing comparisons

A comparison between crossings of rectangles of aspect ratio eight at one scale gives a
comparison at aspect ratio two at any scale within a factor of four. The proof restricts each
crossing to a suitable smaller rectangle.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- An aspect-ratio-eight comparison at scale `m` implies an aspect-ratio-two comparison at
any scale `n` between `m` and `4 * m`. -/
theorem crossing_comparison_two_of_eight (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (ψ : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1)
    {m n : ℕ} (hmn : m ≤ n) (hnm : n ≤ 4 * m) (level : ℝ)
    (h : (ψ (probabilityInUnitInterval μ (planarCrossingEvent (2 * m) (16 * m) level)) : ℝ) ≤
      μ.real (planarCrossingEvent (16 * m) (2 * m) level)) :
    (ψ (probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (4 * n) level)) : ℝ) ≤
      μ.real (planarCrossingEvent (4 * n) (2 * n) level) := by
  have hshort : planarCrossingEvent (2 * n) (4 * n) level ⊆
      planarCrossingEvent (2 * m) (16 * m) level :=
    planarCrossingEvent_width_height_mono (by omega) (by omega) level
  have hlong : planarCrossingEvent (16 * m) (2 * m) level ⊆
      planarCrossingEvent (4 * n) (2 * n) level :=
    planarCrossingEvent_width_height_mono (by omega) (by omega) level
  have hp : probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (4 * n) level) ≤
      probabilityInUnitInterval μ (planarCrossingEvent (2 * m) (16 * m) level) :=
    measureReal_mono hshort (measure_ne_top μ _)
  have hψ : (ψ (probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (4 * n) level)) : ℝ) ≤
      (ψ (probabilityInUnitInterval μ (planarCrossingEvent (2 * m) (16 * m) level)) : ℝ) :=
    ψ.monotone hp
  exact hψ.trans (h.trans (measureReal_mono hlong (measure_ne_top μ _)))

/-- Comparisons at aspect ratio eight on powers of four imply the aspect-ratio-two
comparison at every positive integer scale. -/
theorem crossing_comparison_two_of_eight_pow_four (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (ψ : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1) (level : ℝ)
    (h : ∀ j : ℕ,
      (ψ (probabilityInUnitInterval μ
        (planarCrossingEvent (2 * 4 ^ j) (16 * 4 ^ j) level)) : ℝ) ≤
        μ.real (planarCrossingEvent (16 * 4 ^ j) (2 * 4 ^ j) level))
    {n : ℕ} (hn : 1 ≤ n) :
    (ψ (probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (4 * n) level)) : ℝ) ≤
      μ.real (planarCrossingEvent (4 * n) (2 * n) level) := by
  have hmn : 4 ^ Nat.log 4 n ≤ n := Nat.pow_log_le_self 4 (by omega)
  have hnm : n ≤ 4 * 4 ^ Nat.log 4 n := by
    have hlt := Nat.lt_pow_succ_log_self (b := 4) (by decide) n
    rw [pow_succ, Nat.mul_comm] at hlt
    exact hlt.le
  exact crossing_comparison_two_of_eight μ ψ hmn hnm level (h (Nat.log 4 n))

end Sandpile.External.RSW
