/-
**The threshold field of `prop:dgt4-contact-asymptotics` in both cases**
(`sandpile.tex:5454-5455`): "Set `J=-V_\infty` in case (a) and `J=-G(0,0)\zeta` in case (b)."

Case (a) is `Support/Dgt4GaussTail.lean` once the two estimates of
`sandpile.tex:4977-4984` are supplied, which is what Steps 1 to 4 of
`Support/Dgt4AStep4Mean.lean` and `Support/Dgt4AStep4Rel.lean` do; case (b) is
`Support/Dgt4PairHitting.lean` once its moment, regular-variation and summability inputs are
read off the paper's hypothesis.  The moment is `integrable_abs_rpow_of_lowerTail` at an
exponent strictly between `\alpha/2` and `\alpha`, and the summability of the site weights
is the square summability of the Green function, because the weights `G(0,z)/G(0,0)` are at
most one and the exponent is at least two.
-/
import Sandpile.Support.Dgt4AStep4Rel
import Sandpile.Support.Dgt4GaussTail
import Sandpile.Support.Dgt4PairHitting
import Sandpile.Support.Dgt4LowerTailMoment
import Sandpile.Support.LinWeights

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The site weights `G(0,z)/G(0,0)` of case (b) are `p`-summable for every `p\geq2`, because
they are at most one and the Green function is square summable. -/
theorem summable_greenRatioWeight_rpow (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    {p : ℝ} (hp : 2 ≤ p) :
    Summable fun z : Site d => greenRatioWeight d z ^ p := by
  have hG : (0 : ℝ) < green d 0 0 := lt_of_lt_of_le zero_lt_one (one_le_green (by omega))
  have hsum2 : Summable fun z : Site d => greenRatioWeight d z ^ (2 : ℕ) := by
    have h := ((hGH d hd).2.1).div_const (green d 0 0 ^ 2)
    refine h.congr fun z => ?_
    rw [greenRatioWeight, div_pow]
  refine Summable.of_nonneg_of_le
    (fun z => Real.rpow_nonneg (greenRatioWeight_nonneg hd z) p) (fun z => ?_) hsum2
  have h0 := greenRatioWeight_nonneg hd z
  have h1 := greenRatioWeight_le_one hd z
  have hconv : greenRatioWeight d z ^ (2 : ℝ) = greenRatioWeight d z ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (greenRatioWeight d z) 2]
    norm_num
  rcases eq_or_lt_of_le h0 with hz | hz
  · rw [← hz, Real.zero_rpow (by linarith)]
    positivity
  · rw [← hconv]
    exact Real.rpow_le_rpow_of_exponent_ge hz h1 hp

/-- **The threshold field of `prop:dgt4-contact-asymptotics` in both cases of
`thm:dgt4-diffusive-membrane`.** -/
theorem caseThresholdField_of_hcase
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (κ : ℝ)
    (hcase :
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧ κ = 1) ∨
      (∃ α : ℝ, 2 < α ∧ (∃ M : ℝ, ν (Set.Ioi M) = 0) ∧
        (∀ lam : ℝ, 0 < lam →
          Tendsto (fun r : ℝ => (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
            atTop (𝓝 (lam ^ (-α)))) ∧
        κ = 1 - 1 / α)) :
    CaseThresholdField d ν κ := by
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hint : Integrable (id : ℝ → ℝ) ν := hLp.integrable (by norm_num)
  rcases hcase with ⟨⟨v, hgauss⟩, hκ⟩ | ⟨α, hα, ⟨M, hM⟩, hrv, hκ⟩
  · subst hκ
    have hv : v ≠ 0 := gaussian_var_ne_zero hvar hgauss
    have hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) := by
      have h := (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
      simpa using h
    have hincr : GaussianMeanIncrement d ν (fieldVar d v) := by
      rw [hgauss]
      exact gaussianMeanIncrement_of hGaussConc hGreenHigh hd v hv hsq
    have hrel : ThresholdRelativeError d ν
        (fun σ x => -infiniteGreenField (scenery d σ) x) := by
      rw [hgauss]
      exact thresholdRelativeError_gaussian hGaussConc hGreenHigh hd v hv hsq
    exact caseThresholdField_gaussian_of_hcase hd ν hint hmean hatom hvar v hgauss hincr hrel
  · subst hκ
    set p : ℝ := max 2 (3 * α / 4) with hpdef
    have hα0 : (0 : ℝ) < α := by linarith
    have hp2 : (2 : ℝ) ≤ p := le_max_left _ _
    have hp34 : 3 * α / 4 ≤ p := le_max_right _ _
    have hppos : (0 : ℝ) < p := by linarith
    have hpα : p < α := max_lt (by linarith) (by linarith)
    have h2p : α < 2 * p := by linarith
    have hrv' : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α) := hrv
    have hmom : Integrable (fun z : ℝ => |z| ^ p) ν :=
      integrable_abs_rpow_of_lowerTail ν hM hppos hpα hrv'
    exact caseThresholdField_linear hGreenHigh hd ν hatom hmean hvar hvar' (by linarith)
      hppos h2p hmom hrv' (summable_greenRatioWeight_rpow hGreenHigh hd hp2) M hM

/-- **`prop:dgt4-contact-asymptotics`** (`sandpile.tex:4818-4820`) from the case
dichotomy. -/
theorem dgt4_contact_asymptotics_of_hcase
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (κ : ℝ)
    (hcase :
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧ κ = 1) ∨
      (∃ α : ℝ, 2 < α ∧ (∃ M : ℝ, ν (Set.Ioi M) = 0) ∧
        (∀ lam : ℝ, 0 < lam →
          Tendsto (fun r : ℝ => (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
            atTop (𝓝 (lam ^ (-α)))) ∧
        κ = 1 - 1 / α)) :
    Tendsto (fun n : ℕ =>
        ((Sandpile.centeredMassLaw d ν) {σ | Sandpile.odometer σ n 0 = 0}).toReal /
          (Sandpile.green d 0 0 * κ / n)) atTop (𝓝 1) :=
  dgt4_contact_asymptotics_of (by omega) (kappa_pos hcase)
    (caseThresholdField_of_hcase hGreenHigh hGaussConc d hd ν hatom hmean hvar hvar' κ hcase)

end Sandpile
