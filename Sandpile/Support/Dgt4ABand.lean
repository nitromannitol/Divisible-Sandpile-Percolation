import Sandpile.Support.ManyLStep3
import Sandpile.Support.Dgt4ABandLaw
import Sandpile.Support.Dgt4ABandIndex

/-!
# The band contact-rate and contact-comparison estimates

Two limits over the band `δ R_k^2 ≤ n ≤ ⌊R_k^2 T⌋`: the contact rate `BandContactRate`, comparing
the threshold probability at the level `E u_{n-1}(0)` against `G(0,0)κ_k/n`, and the contact
comparison `BandContactComparison`, comparing the contact event `{u_n(0) = 0}` against the
threshold event. Both are stated along a sequence of scales `R_k` against a sequence of
exponents `κ_k`, since the band exponents vary with the index; the constant-exponent readings are
recovered by `bandContactRate_const` and `bandContactComparison_const`. Finally
`uniformContactThresholds_of_band` passes from the two band limits at a fixed real scale to the
uniform contact-threshold estimate `UniformContactThresholds` on the index range
`⌈ε n_R⌉ ≤ m ≤ n_R`, taking `δ = εT/2`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- `eq:dgt4-band-contact-rate` (`sandpile.tex:6252-6262`), along a sequence of
scales and against a sequence of exponents: uniformly over the band
`δ R_k^2 ≤ n ≤ ⌊R_k^2 T⌋`, the threshold probability at the level
`E u_{n-1}(0)` is `G(0,0)κ_k/n` to leading order. -/
def BandContactRate (d : ℕ) (ν : Measure ℝ) (kseq Rseq : ℕ → ℝ) (T : ℝ) : Prop :=
  ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) T → ∀ η : ℝ, 0 < η →
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, δ * Rseq k ^ 2 ≤ (n : ℝ) → n ≤ ⌊Rseq k ^ 2 * T⌋₊ →
      |(n : ℝ) * ((Sandpile.centeredMassLaw d ν)
            {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n - 1) <
              -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}).toReal /
          Sandpile.green d 0 0 - kseq k| ≤ η

/-- `eq:dgt4-band-contact-comparison` (`sandpile.tex:6273-6287`), along a sequence
of scales: uniformly over the band `δ R_k^2 ≤ n ≤ ⌊R_k^2 T⌋`, the contact event
`{u_n(0)=0}` agrees with the threshold event up to `o(1/R_k^2)`. -/
def BandContactComparison (d : ℕ) (ν : Measure ℝ) (Rseq : ℕ → ℝ) (T : ℝ) : Prop :=
  ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) T → ∀ η : ℝ, 0 < η →
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, δ * Rseq k ^ 2 ≤ (n : ℝ) → n ≤ ⌊Rseq k ^ 2 * T⌋₊ →
      Rseq k ^ 2 * ((Sandpile.centeredMassLaw d ν)
        (symmDiff {σ | Sandpile.odometer σ n 0 = 0}
          {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n - 1) <
            -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)})).toReal ≤ η

/-- **The paper's fixed-`κ` reading of the rate estimate**, recovered at a
constant exponent sequence: the threshold probability at the level `E u_{n-1}(0)`
is `G(0,0)κ/n` to leading order. -/
theorem bandContactRate_const (d : ℕ) (ν : Measure ℝ) (κ T : ℝ) (hκ : 0 < κ)
    (Rseq : ℕ → ℝ) (h : BandContactRate d ν (fun _ => κ) Rseq T) :
    ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) T → ∀ η : ℝ, 0 < η →
      ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, δ * Rseq k ^ 2 ≤ (n : ℝ) → n ≤ ⌊Rseq k ^ 2 * T⌋₊ →
        |(n : ℝ) * ((Sandpile.centeredMassLaw d ν)
              {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n - 1) <
                -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}).toReal /
            (Sandpile.green d 0 0 * κ) - 1| ≤ η := by
  intro δ hδ η hη
  filter_upwards [h δ hδ (η * κ) (by positivity)] with k hk n hn1 hn2
  have hA := hk n hn1 hn2
  set A : ℝ := (n : ℝ) * ((Sandpile.centeredMassLaw d ν)
      {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n - 1) <
        -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}).toReal /
      Sandpile.green d 0 0 with hAdef
  have heq : (n : ℝ) * ((Sandpile.centeredMassLaw d ν)
        {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n - 1) <
          -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}).toReal /
      (Sandpile.green d 0 0 * κ) - 1 = (A - κ) / κ := by
    rw [hAdef, ← div_div, sub_div, div_self (ne_of_gt hκ)]
  rw [heq, abs_div, abs_of_pos hκ, div_le_iff₀ hκ]
  simpa using hA

/-- **The paper's fixed-`n` reading of the comparison estimate**, recovered from
the scale-normalized one: over the band the two events agree up to `o(1/n)`. -/
theorem bandContactComparison_const (d : ℕ) (ν : Measure ℝ) (T : ℝ) (hT : 0 < T)
    (Rseq : ℕ → ℝ) (h : BandContactComparison d ν Rseq T) :
    ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) T → ∀ η : ℝ, 0 < η →
      ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, δ * Rseq k ^ 2 ≤ (n : ℝ) → n ≤ ⌊Rseq k ^ 2 * T⌋₊ →
        (n : ℝ) * ((Sandpile.centeredMassLaw d ν)
          (symmDiff {σ | Sandpile.odometer σ n 0 = 0}
            {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n - 1) <
              -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)})).toReal ≤ η := by
  intro δ hδ η hη
  filter_upwards [h δ hδ (η / T) (by positivity)] with k hk n hn1 hn2
  have hA := hk n hn1 hn2
  set Q : ℝ := ((Sandpile.centeredMassLaw d ν)
      (symmDiff {σ | Sandpile.odometer σ n 0 = 0}
        {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n - 1) <
          -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)})).toReal with hQ
  have hQnn : 0 ≤ Q := ENNReal.toReal_nonneg
  have hRpos : 0 ≤ Rseq k ^ 2 := sq_nonneg _
  have hnle : (n : ℝ) ≤ Rseq k ^ 2 * T := by
    refine le_trans (by exact_mod_cast hn2) (Nat.floor_le ?_)
    positivity
  calc (n : ℝ) * Q ≤ Rseq k ^ 2 * T * Q := mul_le_mul_of_nonneg_right hnle hQnn
    _ = T * (Rseq k ^ 2 * Q) := by ring
    _ ≤ T * (η / T) := mul_le_mul_of_nonneg_left hA hT.le
    _ = η := by field_simp

/-- **The Step-2 output from the two band limits at a fixed real scale**
(`sandpile.tex:6300`): the uniform contact-threshold estimate over
`⌈ε n_R⌉ ≤ m ≤ n_R` follows from the two band limits at `δ = ε T/2`, because
`⌈ε ⌊R^2 T⌋⌉ ≥ ε(R^2 T - 1) ≥ (ε T/2) R^2` for all large `R`.  The hypotheses are
written out rather than named, because they read a single real scale rather than
a sequence; the sequence-indexed passage is
`uniformContactThresholdsAlong_of_band`. -/
theorem uniformContactThresholds_of_band (d : ℕ) (ν : Measure ℝ) (κ T : ℝ)
    (hT : 0 < T)
    (hrate : ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) T → ∀ η : ℝ, 0 < η →
      ∀ᶠ R : ℝ in atTop, ∀ n : ℕ, δ * R ^ 2 ≤ (n : ℝ) → n ≤ ⌊R ^ 2 * T⌋₊ →
        |(n : ℝ) * ((Sandpile.centeredMassLaw d ν)
              {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n - 1) <
                -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}).toReal /
            (Sandpile.green d 0 0 * κ) - 1| ≤ η)
    (hcomp : ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) T → ∀ η : ℝ, 0 < η →
      ∀ᶠ R : ℝ in atTop, ∀ n : ℕ, δ * R ^ 2 ≤ (n : ℝ) → n ≤ ⌊R ^ 2 * T⌋₊ →
        (n : ℝ) * ((Sandpile.centeredMassLaw d ν)
          (symmDiff {σ | Sandpile.odometer σ n 0 = 0}
            {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n - 1) <
              -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)})).toReal ≤ η) :
    UniformContactThresholds d ν κ T := by
  intro ε hε η hη
  have hδmem : ε * T / 2 ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · exact div_pos (mul_pos hε.1 hT) (by norm_num)
    · nlinarith [hε.1, hε.2, hT]
  have hhalf : (0 : ℝ) < η / 2 := by linarith
  have h1 := hrate (ε * T / 2) hδmem (η / 2) hhalf
  have h2 := hcomp (ε * T / 2) hδmem (η / 2) hhalf
  have h3 := eventually_ceil_ge_half ε T hε.1 hε.2 hT
  filter_upwards [h1, h2, h3] with R hR1 hR2 hR3 m hm1 hm2
  have hlow : ε * T / 2 * R ^ 2 ≤ (m : ℝ) :=
    le_trans hR3 (by exact_mod_cast hm1)
  have hA := hR1 m hlow hm2
  have hB := hR2 m hlow hm2
  linarith

end Sandpile.Support
