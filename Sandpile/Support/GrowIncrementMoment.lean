/-
The moment bound of `Sandpile.Support.exists_isKolmogorovProcess_potStrip`, read
back as a real-valued inequality on the potential itself (rather than the
`IsKolmogorovProcess` package around its `ENNReal`-valued lintegral), at the
clamped time replaced by the time itself once it is known to lie in `[0,T]`.
This is the exact real-valued increment bound `kolmogorov_polynomial_tail`
consumes.
-/
import Sandpile.Support.MeanAGauss
import Sandpile.Support.MeanAIncrement

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- **The moment of an increment of the potential, at exponent `8(d+2)` and
Hölder exponent `d+2` in the space-time distance, for both points inside a
strip `[0,T]`.** The constant depends only on `T` and `d`, and it does not move
under translation of the space coordinates: `x` and `y` range over the whole of
`Space d`. -/
theorem exists_potential_moment_bound (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2)
    {T : ℝ} (hT : 0 < T) {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x y : Space d,
      Integrable (fun ω => |gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W s y ω|
          ^ (8 * ((d : ℝ) + 2))) PW ∧
      ∫ ω, |gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W s y ω|
          ^ (8 * ((d : ℝ) + 2)) ∂PW
        ≤ Kc * (max |t - s| ‖x - y‖) ^ ((d : ℝ) + 2) := by
  obtain ⟨MH, hMH0, hMH⟩ := exists_greenTimeBM_holder hd hd3 hT
  set p : ℝ := 8 * ((d : ℝ) + 2) with hpdef
  have hp : 0 < p := by rw [hpdef]; positivity
  set base : ℝ := ν2 * MH with hbase
  have hbase0 : 0 ≤ base := mul_nonneg hν2 hMH0
  set Kc : ℝ := gaussAbsMoment p * base ^ (p / 2) with hKc
  have hKc0 : 0 ≤ Kc := mul_nonneg (gaussAbsMoment_nonneg p) (Real.rpow_nonneg hbase0 _)
  refine ⟨Kc, hKc0, fun t ht s hs x y => ?_⟩
  have hL0 : (0 : ℝ) ≤ ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2 :=
    integral_nonneg fun w => by positivity
  have hbound : ∫ ω, |gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W s y ω| ^ p ∂PW
      ≤ Kc * (max |t - s| ‖x - y‖) ^ ((d : ℝ) + 2) := by
    rw [integral_abs_rpow_gaussianPotential_sub PW W hW hd hd3 hν2 ht.1 hs.1 x y hp.le]
    have h1 : (ν2 * ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2)
        ≤ base * (max |t - s| ‖x - y‖) ^ ((1 : ℝ) / 4) := by
      have hchain := hMH t ht s hs x y
      have := mul_le_mul_of_nonneg_left hchain hν2
      rw [hbase]; linarith [this]
    have h2 : (ν2 * ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2) ^ (p / 2)
        ≤ (base * (max |t - s| ‖x - y‖) ^ ((1 : ℝ) / 4)) ^ (p / 2) :=
      Real.rpow_le_rpow (mul_nonneg hν2 hL0) h1 (by positivity)
    have h3 : (base * (max |t - s| ‖x - y‖) ^ ((1 : ℝ) / 4)) ^ (p / 2)
        = base ^ (p / 2) * (max |t - s| ‖x - y‖) ^ ((d : ℝ) + 2) := by
      rw [Real.mul_rpow hbase0 (Real.rpow_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) _),
        ← Real.rpow_mul (le_trans (abs_nonneg _) (le_max_left _ _))]
      congr 2
      rw [hpdef]; ring
    rw [h3] at h2
    have hm0 := gaussAbsMoment_nonneg p
    have hdq : (0 : ℝ) ≤ (max |t - s| ‖x - y‖) ^ ((d : ℝ) + 2) :=
      Real.rpow_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) _
    rw [hKc]
    nlinarith [h2, hm0, hdq]
  exact ⟨integrable_abs_rpow_gaussianPotential_sub PW W hW hd hd3 hν2 ht.1 hs.1 x y hp, hbound⟩

end Sandpile.Support
