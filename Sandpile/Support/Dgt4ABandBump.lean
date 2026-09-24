/-
A smooth probability density on `[0,1]` and its distribution function, the
building blocks of the band components of the one-site law constructed in Step 1
of `thm:dgt4-many-limits` (`sandpile.tex:5930-6055`).

The law of that step is a mixture of an almost sure value, of band components
supported on the intervals `(ℓ₁ a_k, a_k]`, and of a smoothing summand.  The
band components must have smooth densities, so each one is built from the
smooth bump below rather than from the exact tail `((1-y)/(1-ℓ₁))^ϑ` of the
paper, whose density is not smooth at the endpoints; the distribution functions
agree to any prescribed accuracy, which is all Step 1 uses.
-/
import Sandpile.Support.SmoothCutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Sandpile.Support

/-- The unnormalized smooth bump: positive exactly on `(0,1)`. -/
def bandBumpRaw (x : ℝ) : ℝ := expNegInvGlue x * expNegInvGlue (1 - x)

lemma contDiff_bandBumpRaw : ContDiff ℝ (⊤ : ℕ∞) bandBumpRaw :=
  expNegInvGlue.contDiff.mul (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

lemma continuous_bandBumpRaw : Continuous bandBumpRaw := contDiff_bandBumpRaw.continuous

lemma bandBumpRaw_nonneg (x : ℝ) : 0 ≤ bandBumpRaw x :=
  mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

lemma bandBumpRaw_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : bandBumpRaw x = 0 := by
  simp [bandBumpRaw, expNegInvGlue.zero_of_nonpos hx]

lemma bandBumpRaw_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : bandBumpRaw x = 0 := by
  have : (1 : ℝ) - x ≤ 0 := by linarith
  simp [bandBumpRaw, expNegInvGlue.zero_of_nonpos this]

lemma bandBumpRaw_pos {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : 0 < bandBumpRaw x :=
  mul_pos (expNegInvGlue.pos_of_pos hx) (expNegInvGlue.pos_of_pos (by linarith))

/-- The mass of the unnormalized bump. -/
def bandBumpMass : ℝ := ∫ x in (0 : ℝ)..1, bandBumpRaw x

lemma bandBumpMass_pos : 0 < bandBumpMass := by
  have hcont : ContinuousOn bandBumpRaw (Icc (0 : ℝ) 1) :=
    continuous_bandBumpRaw.continuousOn
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ one_pos
  · exact continuous_bandBumpRaw.intervalIntegrable _ _
  · intro x hx
    exact bandBumpRaw_pos hx.1 hx.2

/-- The smooth probability density on `[0,1]`. -/
def bandBump (x : ℝ) : ℝ := bandBumpRaw x / bandBumpMass

lemma contDiff_bandBump : ContDiff ℝ (⊤ : ℕ∞) bandBump :=
  contDiff_bandBumpRaw.div_const _

lemma continuous_bandBump : Continuous bandBump := contDiff_bandBump.continuous

lemma bandBump_nonneg (x : ℝ) : 0 ≤ bandBump x :=
  div_nonneg (bandBumpRaw_nonneg x) bandBumpMass_pos.le

lemma bandBump_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : bandBump x = 0 := by
  simp [bandBump, bandBumpRaw_eq_zero_of_nonpos hx]

lemma bandBump_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : bandBump x = 0 := by
  simp [bandBump, bandBumpRaw_eq_zero_of_one_le hx]

lemma integral_bandBump : ∫ x in (0 : ℝ)..1, bandBump x = 1 := by
  simp only [bandBump]
  rw [intervalIntegral.integral_div]
  exact div_self bandBumpMass_pos.ne'

lemma exists_bandBump_bound : ∃ M : ℝ, 1 ≤ M ∧ ∀ x : ℝ, |bandBump x| ≤ M := by
  have hsupp : HasCompactSupport bandBump := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    intro x hx
    rcases lt_or_ge x 0 with h | h
    · exact bandBump_eq_zero_of_nonpos h.le
    · have : 1 < x := by
        by_contra hc
        exact hx ⟨h, le_of_not_gt hc⟩
      exact bandBump_eq_zero_of_one_le this.le
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous continuous_bandBump
  refine ⟨max 1 M, le_max_left _ _, fun x => ?_⟩
  simpa only [Real.norm_eq_abs] using (hM x).trans (le_max_right _ _)

/-- The distribution function of `bandBump`: a smooth nondecreasing function
that vanishes on `(-∞,0]` and equals one on `[1,∞)`. -/
def bandStep (r : ℝ) : ℝ := ∫ x in (0 : ℝ)..r, bandBump x

lemma hasDerivAt_bandStep (r : ℝ) : HasDerivAt bandStep (bandBump r) r :=
  (continuous_bandBump.integral_hasStrictDerivAt 0 r).hasDerivAt

lemma deriv_bandStep (r : ℝ) : deriv bandStep r = bandBump r :=
  continuous_bandBump.deriv_integral _ _ _

lemma differentiable_bandStep : Differentiable ℝ bandStep :=
  intervalIntegral.differentiable_integral_of_continuous continuous_bandBump

lemma contDiff_bandStep : ContDiff ℝ (⊤ : ℕ∞) bandStep := by
  refine contDiff_infty_iff_deriv.mpr ⟨differentiable_bandStep, ?_⟩
  have : deriv bandStep = bandBump := funext deriv_bandStep
  rw [this]
  exact contDiff_bandBump

lemma bandStep_eq_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) : bandStep r = 0 := by
  refine intervalIntegral.integral_zero_ae (Filter.Eventually.of_forall fun x hx => ?_)
  have hx' : x ≤ 0 := by
    rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hx) with h1 | h1
    · exact le_trans h1.2 hr
    · exact h1.2
  exact bandBump_eq_zero_of_nonpos hx'

lemma bandStep_eq_one_of_one_le {r : ℝ} (hr : 1 ≤ r) : bandStep r = 1 := by
  have hsplit : bandStep r = (∫ x in (0 : ℝ)..1, bandBump x) + ∫ x in (1 : ℝ)..r, bandBump x := by
    rw [bandStep, intervalIntegral.integral_add_adjacent_intervals]
    · exact continuous_bandBump.intervalIntegrable _ _
    · exact continuous_bandBump.intervalIntegrable _ _
  have htail : (∫ x in (1 : ℝ)..r, bandBump x) = 0 := by
    refine intervalIntegral.integral_zero_ae (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : (1 : ℝ) ≤ x := by
      rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hx) with h1 | h1
      · exact h1.1
      · exact le_trans hr h1.1
    exact bandBump_eq_zero_of_one_le hx'
  rw [hsplit, htail, integral_bandBump, add_zero]

lemma bandStep_monotone : Monotone bandStep := by
  intro a b hab
  have : bandStep b - bandStep a = ∫ x in a..b, bandBump x := by
    rw [bandStep, bandStep, intervalIntegral.integral_interval_sub_left]
    · exact continuous_bandBump.intervalIntegrable _ _
    · exact continuous_bandBump.intervalIntegrable _ _
  have hnn : 0 ≤ ∫ x in a..b, bandBump x :=
    intervalIntegral.integral_nonneg hab (fun x _ => bandBump_nonneg x)
  linarith [this ▸ hnn]

lemma bandStep_nonneg (r : ℝ) : 0 ≤ bandStep r := by
  have := bandStep_monotone (le_max_left r 0)
  rcases le_or_gt r 0 with h | h
  · exact le_of_eq (bandStep_eq_zero_of_nonpos h).symm
  · have h0 : bandStep 0 = 0 := bandStep_eq_zero_of_nonpos le_rfl
    have := bandStep_monotone h.le
    linarith [h0 ▸ this]

lemma bandStep_le_one (r : ℝ) : bandStep r ≤ 1 := by
  rcases le_or_gt r 1 with h | h
  · have h1 : bandStep 1 = 1 := bandStep_eq_one_of_one_le le_rfl
    have := bandStep_monotone h
    linarith [h1 ▸ this]
  · exact le_of_eq (bandStep_eq_one_of_one_le h.le)

end Sandpile.Support
