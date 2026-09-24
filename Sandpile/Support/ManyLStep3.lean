/-
Step 3 of the proof of `thm:dgt4-many-limits` (`sandpile.tex:5900-5928`,
proof at `sandpile.tex:6275-6305`): from the uniform contact thresholds of
Step 2, `lem:dgt4-path-survival` and `lem:dgt4-linearization-from-survival`
give the linearization of the rescaled centred odometer along the subsequence
`R_{k_ℓ}`, and `prop:weighted-membrane-limit` identifies the limit of the
time-weighted field.

`UniformContactThresholds` is the Step-2 output
(`sandpile.tex:6051-6275`, equations `eq:dgt4-band-contact-rate` and
`eq:dgt4-band-contact-comparison`), stated for the threshold field
`J = -G(0,0)ζ` of the constructed scenery.  It is the one input of Step 3 that
is not one of the frozen dgt4 nodes.

`dgt4_linearization_of_survival` discharges the frozen
`prop:dgt4-linearization` from that input: `lem:dgt4-path-survival` supplies
the two hypotheses of `lem:dgt4-linearization-from-survival` at the weight
`q(r) = (1-r/T)^κ`, and the latter's first conjunct is the frozen linearization
verbatim.

`dgt4_many_limits_of_scenery_and_sub` is the whole node with the scenery
existentially quantified: `exists_scenery_law` produces the law and its four
analytic properties, and the Step-3 subsequential convergence is the
hypothesis.
-/
import Sandpile.Support.ManyLManyLimits
import Sandpile.Support.ContLogisticLaw
import Sandpile.Frozen.DGT4PathSurvival
import Sandpile.Frozen.DGT4LinearizationFromSurvival
import Sandpile.Frozen.WeightedMembraneLimit
import Sandpile.Support.ContDGT4Membrane

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The uniform contact thresholds of Step 2 of the proof of
`thm:dgt4-many-limits` (`sandpile.tex:6046-6270`), for the threshold field
`J = -G(0,0)ζ` of the constructed scenery.  This is the one input of Step 3 that
is not one of the three frozen dgt4 nodes. -/
def UniformContactThresholds (d : ℕ) (ν : Measure ℝ) (κ T : ℝ) : Prop :=
  ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
    ∀ᶠ R : ℝ in atTop, ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
      |(m : ℝ) * ((Sandpile.centeredMassLaw d ν)
            {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) <
              -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}).toReal /
          (Sandpile.green d 0 0 * κ) - 1| +
        (m : ℝ) * ((Sandpile.centeredMassLaw d ν)
          (symmDiff {σ | Sandpile.odometer σ m 0 = 0}
            {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) <
              -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)})).toReal ≤ η

/-- **The linearization `prop:dgt4-linearization` from the survival lemma.**
`lem:dgt4-path-survival` supplies the two hypotheses of
`lem:dgt4-linearization-from-survival` at the weight `q(r) = (1-r/T)^κ`, and the
latter's first conjunct is the frozen linearization verbatim. -/
theorem dgt4_linearization_of_survival
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hNormal : Sandpile.External.NormalComparison)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hRK : Sandpile.External.RellichKondrachovNegSobolev)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (κ : ℝ)
    (hcase :
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧ κ = 1) ∨
      (∃ α : ℝ, 2 < α ∧ (∃ M : ℝ, ν (Set.Ioi M) = 0) ∧
        (∀ lam : ℝ, 0 < lam →
          Tendsto (fun r : ℝ => (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
            atTop (𝓝 (lam ^ (-α)))) ∧
        κ = 1 - 1 / α))
    (T : ℝ) (hT : 0 < T)
    (hthresholds : UniformContactThresholds d ν κ T)
    (φ : Sandpile.Continuum.Space d → ℝ) (hφ : Sandpile.Continuum.IsTestFn Set.univ φ) :
    Tendsto (fun R : ℝ =>
        ∫ σ, (R ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
              ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
                (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ *
                  (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
          ∂(Sandpile.centeredMassLaw d ν))
      atTop (𝓝 0) := by
  have hκ : 0 < κ := by
    rcases hcase with ⟨-, hκ1⟩ | ⟨α, hα, ⟨M, hM⟩, hlam, hκ2⟩
    · rw [hκ1]; norm_num
    · rw [hκ2]
      have h1 : 1 / α < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      linarith
  have hJ : Sandpile.Frozen.DGT4PathSurvival.IsThresholdField ν
      (fun σ x => -(Sandpile.green d 0 0 * Sandpile.scenery d σ x)) :=
    Or.inl fun σ x => rfl
  obtain ⟨hsurv, hcov⟩ := Sandpile.Frozen.dgt4_path_survival hGreenHigh hNormal d hd ν hatom
    hmean hvar hvar' _ hJ T hT κ hκ hthresholds
  have hq : ∀ (R : ℝ) (j : ℕ), j < ⌊R ^ 2 * T⌋₊ →
      (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ ∈ Set.Icc (0 : ℝ) 1 := by
    intro R j hj
    have hR2 : 0 < R ^ 2 * T := by
      rcases eq_or_ne R 0 with h | h
      · rw [h] at hj; simp at hj
      · exact mul_pos (sq_pos_of_ne_zero h) hT
    have hj' : (j : ℝ) < R ^ 2 * T := by
      have h1 : (⌊R ^ 2 * T⌋₊ : ℝ) ≤ R ^ 2 * T := Nat.floor_le hR2.le
      have h2 : (j : ℝ) < (⌊R ^ 2 * T⌋₊ : ℝ) := by exact_mod_cast hj
      linarith
    have h0 : 0 ≤ 1 - (j : ℝ) / (R ^ 2 * T) := by
      rw [sub_nonneg, div_le_one hR2]
      linarith
    have h1 : 1 - (j : ℝ) / (R ^ 2 * T) ≤ 1 := by
      rw [sub_le_iff_le_add, le_add_iff_nonneg_right]
      exact div_nonneg (Nat.cast_nonneg j) hR2.le
    exact ⟨Real.rpow_nonneg h0 κ, Real.rpow_le_one h0 h1 hκ.le⟩
  exact (Sandpile.Frozen.dgt4_linearization_from_survival hGreenHigh hInter d hd hBesov hRK ν
    hatom hmean hvar hvar' T hT (fun R j => (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ) hq hsurv hcov).1
    φ hφ

/-- **`thm:dgt4-many-limits` from the Step-3 subsequential convergence at an
arbitrary scenery law.**  The scenery law and its four analytic properties are
produced by `exists_scenery_law`; the hypothesis `hsub` is the Step-3
subsequential convergence, which the paper obtains from the Step-2 uniform
contact thresholds through `lem:dgt4-path-survival` and
`lem:dgt4-linearization-from-survival`. -/
theorem dgt4_many_limits_of_scenery_and_sub (d : ℕ) (hd : 5 ≤ d)
    (hsub : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], ∫ z, z ∂ν = 0 →
      variance (id : ℝ → ℝ) ν = 1 →
      (∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
        ν = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z)) →
      (∃ c C θ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ ∧
        Integrable (fun z => Real.exp (θ * |z|)) ν ∧
        ∀ᶠ r : ℝ in atTop,
          c * r ≤ -Real.log (ν (Set.Iic (-r))).toReal ∧
            -Real.log (ν (Set.Iic (-r))).toReal ≤ C * r) →
      ∃ Rseq : ℕ → ℝ, StrictMono Rseq ∧ Tendsto Rseq atTop atTop ∧
        ∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
          ∃ kl : ℕ → ℕ, StrictMono kl ∧
            ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
              Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
                (fun (L : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
                  Rseq (kl ⌊L⌋₊) ^ (((d : ℝ) - 4) / 2) *
                    Sandpile.Continuum.latticePairing (Rseq (kl ⌊L⌋₊))
                      (fun x => Sandpile.odometer σ ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊ x -
                        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν)
                          ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊) φ)
                (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T)) :
    ∃ ν : Measure ℝ, ∃ _ : IsProbabilityMeasure ν,
      ∫ z, z ∂ν = 0 ∧ variance (id : ℝ → ℝ) ν = 1 ∧
      (∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
        ν = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z)) ∧
      (∃ c C θ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ ∧
        Integrable (fun z => Real.exp (θ * |z|)) ν ∧
        ∀ᶠ r : ℝ in atTop,
          c * r ≤ -Real.log (ν (Set.Iic (-r))).toReal ∧
            -Real.log (ν (Set.Iic (-r))).toReal ≤ C * r) ∧
      (∃ Rseq : ℕ → ℝ, StrictMono Rseq ∧ Tendsto Rseq atTop atTop ∧
        ∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
          ∃ kl : ℕ → ℕ, StrictMono kl ∧
            ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
              Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
                (fun (L : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
                  Rseq (kl ⌊L⌋₊) ^ (((d : ℝ) - 4) / 2) *
                    Sandpile.Continuum.latticePairing (Rseq (kl ⌊L⌋₊))
                      (fun x => Sandpile.odometer σ ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊ x -
                        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν)
                          ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊) φ)
                (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T)) ∧
      ∀ T : ℝ, 0 < T → ∀ κ κ' : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
        κ' ∈ Set.Icc ((3 : ℝ) / 2) 2 → κ ≠ κ' →
        ∃ φ : Sandpile.Continuum.Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ ∧
          Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T φ φ ≠
            Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ' T φ φ := by
  obtain ⟨ν, hprob, hmean, hvar, hdens, htail⟩ := exists_scenery_law
  exact dgt4_many_limits_of_sub d hd ν hprob hmean hvar hdens htail
    (hsub ν hmean hvar hdens htail)

end Sandpile.Support
