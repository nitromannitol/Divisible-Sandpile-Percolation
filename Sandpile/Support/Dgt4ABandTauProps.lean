import Sandpile.Support.Dgt4ABandDiverge
import Sandpile.Support.Dgt4ABandScaled

/-!
# The hitting-index properties the summed profile consumes

The two properties of the hitting index that the summed profile consumes.
`scaledProfile_bound_family` needs exactly two things of its starts `s k`: that the profile is
bounded at the start, and that the start is of smaller order than the square of the scale. At the
sandpile law the start is the hitting index `τ_k` of the band (`bandTau`), and both properties
(`bandTau_profile_bounded`, `bandTau_div_scaleSq_tendsto`) come from the generic hitting-index
lemmas once the band parameters are supplied.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- The hitting index of the `k`-th band at the sandpile law. -/
def bandTau (P : BandParameters) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z) (k : ℕ) : ℕ :=
  Nat.find (bandHitting_exists_sandpile P hd ν hint hmean hnondeg k)

/-- **The hitting index is at most a constant over the band weight.**  Before the
index is reached the level rises by at least `c ω_k a_k` at each step, so the
index is at most the level divided by that, plus one. -/
theorem bandTau_le (P : BandParameters) (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z) {c : ℝ} (hc : 0 < c)
    (hstep : ∀ k n : ℕ,
      meanOdometer (centeredMassLaw d ν) n / green d 0 0
          ≤ P.level k - (1 - P.l1) * P.level k / 2 →
        c * P.weight k * P.level k
          ≤ meanOdometer (centeredMassLaw d ν) (n + 1) / green d 0 0
            - meanOdometer (centeredMassLaw d ν) n / green d 0 0) :
    ∀ᶠ k : ℕ in atTop,
      ((bandTau P hd ν hint hmean hnondeg k : ℕ) : ℝ) ≤ (1 / c + 1) / P.weight k := by
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    hint.abs.mono' (by fun_prop) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
      exact max_le (le_abs_self z) (abs_nonneg z))
  have hb0 : meanOdometer (centeredMassLaw d ν) 0 / green d 0 0 = 0 := by
    rw [meanOdometer_zero d ν, zero_div]
  have hmono : Monotone (fun n : ℕ => meanOdometer (centeredMassLaw d ν) n / green d 0 0) :=
    fun m n h => div_le_div_of_nonneg_right (meanOdometer_mono (by omega) ν hpos h) hG.le
  have hwt : Tendsto (fun k => P.c0 * Real.exp (-(P.level k))) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp P.level_tendsto)).const_mul P.c0
    simpa [Function.comp_def] using h
  filter_upwards [hwt.eventually_lt_const one_pos] with k hk
  exact bandHittingTime_le P.hl1.1.le P.hl1.2.le hc P.level P.weight
    (fun n => meanOdometer (centeredMassLaw d ν) n / green d 0 0) k (P.level_pos k)
    (P.weight_pos k) hk.le hb0 hmono
    (fun n hn => by have := hstep k n hn.le; linarith)
    (bandHitting_exists_sandpile P hd ν hint hmean hnondeg k)

/-- **The profile is bounded at the hitting index.**  This is the first of the
two properties `scaledProfile_bound_family` requires of its starts. -/
theorem bandTau_profile_bounded (P : BandParameters) (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z) {M Θ : ℝ} (hM : 0 ≤ M) (hΘ : ∀ k, P.theta k ≤ Θ)
    (hstep : ∀ n : ℕ, meanOdometer (centeredMassLaw d ν) (n + 1) / green d 0 0
      - meanOdometer (centeredMassLaw d ν) n / green d 0 0 ≤ M)
    (hsmall : ∀ᶠ k : ℕ in atTop, M / ((1 - P.l1) * P.level k) ≤ 1 / 4) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
      |bandLevelCoord P.l1 P.level
          (fun n => meanOdometer (centeredMassLaw d ν) n / green d 0 0) k
          (bandTau P hd ν hint hmean hnondeg k) ^ (-(P.theta k))| ≤ C := by
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    hint.abs.mono' (by fun_prop) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
      exact max_le (le_abs_self z) (abs_nonneg z))
  have hb0 : meanOdometer (centeredMassLaw d ν) 0 / green d 0 0 = 0 := by
    rw [meanOdometer_zero d ν, zero_div]
  refine ⟨(4 : ℝ) ^ Θ, ?_⟩
  filter_upwards [hsmall] with k hk
  have h1l : 0 < 1 - P.l1 := by linarith [P.hl1.2]
  have hW : 0 < (1 - P.l1) * P.level k := mul_pos h1l (P.level_pos k)
  have hh : 0 ≤ P.level k - (1 - P.l1) * P.level k / 2 := by
    nlinarith [P.level_pos k, P.hl1.1, P.hl1.2]
  have hex := bandHitting_exists_sandpile P hd ν hint hmean hnondeg k
  have hlow := half_sub_le_bandLevelCoord_hitting P.level
    (fun n => meanOdometer (centeredMassLaw d ν) n / green d 0 0) k hW hM hb0 hh hstep hex
  have hcoord : 0 ≤ bandLevelCoord P.l1 P.level
      (fun n => meanOdometer (centeredMassLaw d ν) n / green d 0 0) k (Nat.find hex) := by
    linarith
  have hθ : 0 ≤ P.theta k := by linarith [(P.htheta k).1]
  have hbd := bandProfile_hitting_le P.level
    (fun n => meanOdometer (centeredMassLaw d ν) n / green d 0 0) P.theta k hW hM hb0 hh
    hstep hθ (hΘ k) hk hex
  show |bandLevelCoord P.l1 P.level
      (fun n => meanOdometer (centeredMassLaw d ν) n / green d 0 0) k (Nat.find hex)
        ^ (-(P.theta k))| ≤ (4 : ℝ) ^ Θ
  rw [abs_of_nonneg (Real.rpow_nonneg hcoord _)]
  exact hbd

/-- **The hitting index is of smaller order than the square of the scale.**  This
is the second property `scaledProfile_bound_family` requires of its starts. -/
theorem bandTau_div_scaleSq_tendsto (P : BandParameters) (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z) (R L : ℕ → ℝ) {G00 C : ℝ}
    (hG : 0 < G00) (hω : ∀ k, 0 < P.weight k) (hL : Tendsto L atTop atTop)
    (hRL : ∀ k : ℕ, R k ^ 2 * P.weight k = G00 * L k)
    (hτ : ∀ᶠ k : ℕ in atTop,
      ((bandTau P hd ν hint hmean hnondeg k : ℕ) : ℝ) ≤ C / P.weight k) :
    Tendsto (fun k : ℕ =>
        ((bandTau P hd ν hint hmean hnondeg k : ℕ) : ℝ) / R k ^ 2) atTop (𝓝 0) :=
  tendsto_hittingTime_div_scaleSq _ P.weight L R hG hω hL hRL hτ

end Sandpile.Support
