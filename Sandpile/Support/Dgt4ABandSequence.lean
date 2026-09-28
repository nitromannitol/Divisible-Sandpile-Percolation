import Sandpile.Support.Dgt4ABandPointwise
import Sandpile.Support.Dgt4ABand

/-!
# Contact thresholds along a sequence of band exponents

The sequence-indexed passage from the two band estimates to the contact thresholds in Step 3 of
`thm:dgt4-many-limits` (`sandpile.tex:6305-6309`). The band exponents may vary with the index and
converge only after extraction.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile

/-- The contact thresholds along a specified sequence of scales. -/
def UniformContactThresholdsAlong (d : ℕ) (ν : Measure ℝ) (κ T : ℝ)
    (Rseq : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
    ∀ᶠ k : ℕ in atTop, ∀ m : ℕ,
      ⌈ε * (⌊Rseq k ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊Rseq k ^ 2 * T⌋₊ →
        |(m : ℝ) * ((centeredMassLaw d ν)
            {σ | meanOdometer (centeredMassLaw d ν) (m - 1) <
              -(green d 0 0 * scenery d σ 0)}).toReal / (green d 0 0 * κ) - 1| +
          (m : ℝ) * ((centeredMassLaw d ν)
            (symmDiff {σ | odometer σ m 0 = 0}
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) <
                -(green d 0 0 * scenery d σ 0)})).toReal ≤ η

/-- The rate and comparison estimates along a sequence give the uniform contact
thresholds at the limit of its band exponents.  The two hypotheses are exactly
`BandContactRate` and `BandContactComparison`, which are stated in this
sequence-indexed form precisely because the band exponents move with the
scale. -/
theorem uniformContactThresholdsAlong_of_band
    (d : ℕ) (ν : Measure ℝ) (Rseq kseq : ℕ → ℝ)
    (hRtop : Tendsto Rseq atTop atTop) (κ T : ℝ) (hκ : 0 < κ) (hT : 0 < T)
    (hkseq : Tendsto kseq atTop (𝓝 κ))
    (hrate : BandContactRate d ν kseq Rseq T)
    (hcomp : BandContactComparison d ν Rseq T) :
    UniformContactThresholdsAlong d ν κ T Rseq := by
  intro ε hε η hη
  have hδ : ε * T / 2 ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · exact div_pos (mul_pos hε.1 hT) (by norm_num)
    · nlinarith [hε.2]
  have hsquare : Tendsto (fun k => Rseq k ^ 2 * T) atTop atTop :=
    ((tendsto_pow_atTop (n := 2) (by norm_num)).comp hRtop).atTop_mul_const hT
  have hkclose : ∀ᶠ k : ℕ in atTop, |kseq k - κ| < η * κ / 4 := by
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp hkseq (η * κ / 4) (by positivity))
  filter_upwards [hrate (ε * T / 2) hδ (η * κ / 4) (by positivity),
    hcomp (ε * T / 2) hδ (η / (2 * T)) (by positivity),
    hkclose, hsquare.eventually_ge_atTop 2] with k hratek hcompk hk hlarge
  apply uniformContactThresholds_at d ν κ T hT ε hε η hη (Rseq k) hlarge
  · intro n hn hn'
    set a : ℝ := (n : ℝ) * ((centeredMassLaw d ν)
      {σ | meanOdometer (centeredMassLaw d ν) (n - 1) <
        -(green d 0 0 * scenery d σ 0)}).toReal / green d 0 0
    have ha : |a - κ| ≤ η * κ / 2 := by
      have htri := abs_sub_le a (kseq k) κ
      have hrate' : |a - kseq k| ≤ η * κ / 4 := hratek n hn hn'
      linarith
    rw [← div_div]
    change |a / κ - 1| ≤ η / 2
    have heq : a / κ - 1 = (a - κ) / κ := by
      rw [sub_div, div_self (ne_of_gt hκ)]
    rw [heq, abs_div, abs_of_pos hκ]
    exact (div_le_iff₀ hκ).2 (by nlinarith [ha])
  · intro n hnlow hn
    have hnreal : (n : ℝ) ≤ Rseq k ^ 2 * T :=
      (by exact_mod_cast hn : (n : ℝ) ≤ (⌊Rseq k ^ 2 * T⌋₊ : ℝ)).trans
        (Nat.floor_le (by nlinarith : 0 ≤ Rseq k ^ 2 * T))
    have hbound := hcompk n hnlow hn
    have hprob := ENNReal.toReal_nonneg (a := (centeredMassLaw d ν)
      (symmDiff {σ | odometer σ n 0 = 0}
        {σ | meanOdometer (centeredMassLaw d ν) (n - 1) <
          -(green d 0 0 * scenery d σ 0)}))
    have hmul := mul_le_mul_of_nonneg_right hnreal hprob
    have hscaled := mul_le_mul_of_nonneg_left hbound hT.le
    have heq : T * (η / (2 * T)) = η / 2 := by field_simp
    nlinarith

end Sandpile.Support
