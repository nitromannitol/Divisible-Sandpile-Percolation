/-
The `L²` modulus of continuity of the FIXED averaging density `ω`, the second
half of the second display of Step 2 of `prop:d4-superdiffusive-limit`
(`sandpile.tex:3374-3382`).

The `ω`-shift is `φ̃ = φ - ω∫_Dφ`, so its increment over one mesh step splits
into the increment of `φ`, controlled on the `H^s` unit ball by
`Sandpile.Support.integral_sq_sub_translate_le`, and the increment of `ω`,
which is not on that ball.  For `ω` the Fourier route is unnecessary: a smooth
compactly supported function is Lipschitz, and its increment is supported in the
union of its support with a translate of that support, a set of measure at most
twice the measure of the support.  That gives the `L²` modulus `C_ω‖h‖`, which
beats the `‖h‖^{\min\{s,1\}}` of the ball for `‖h‖ ≤ 1`.
-/
import Sandpile.Support.D4SCellL2
import Sandpile.Support.D4DefectOmega

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support
open Sandpile.Continuum

variable {d : ℕ}

/-- **A test function is Lipschitz.**  Its differential is continuous with
compact support, hence bounded, and the mean value inequality applies. -/
theorem exists_lipschitz_of_isTestFn {D : Set (Space d)} {w : Space d → ℝ}
    (hw : IsTestFn D w) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z z' : Space d, |w z - w z'| ≤ L * ‖z - z'‖ := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hw.2.1 hw.1
    (by exact_mod_cast (by norm_num : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0))
  refine ⟨(C : ℝ), C.coe_nonneg, fun z z' => ?_⟩
  have h := hC.dist_le_mul z z'
  rwa [Real.dist_eq, dist_eq_norm] at h

/-- The support of the increment of a test function over the step `h`. -/
theorem translate_support_subset {D : Set (Space d)} {w : Space d → ℝ}
    (_hw : IsTestFn D w) (h : Space d) (z : Space d)
    (hz : w z - w (z + h) ≠ 0) :
    z ∈ tsupport w ∪ (fun y : Space d => y + h) ⁻¹' tsupport w := by
  by_cases h1 : w z = 0
  · have h2 : w (z + h) ≠ 0 := by intro hc; exact hz (by rw [h1, hc]; ring)
    exact Or.inr (subset_tsupport _ h2)
  · exact Or.inl (subset_tsupport _ h1)

/-- **The `L²` modulus of continuity of a fixed test function**, with the
constant `2|{\rm supp}\,w|L_w^2` of the support and the Lipschitz constant. -/
theorem exists_integral_sq_sub_translate_testFn {D : Set (Space d)} {w : Space d → ℝ}
    (hw : IsTestFn D w) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ h : Space d,
      ∫ z : Space d, (w z - w (z + h)) ^ 2 ≤ Cw * ‖h‖ ^ 2 := by
  classical
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_of_isTestFn hw
  have hK : IsCompact (tsupport w) := hw.2.1
  have hVK : volume (tsupport w) ≠ ⊤ := hK.measure_lt_top.ne
  have hmK : MeasurableSet (tsupport w) := (isClosed_tsupport w).measurableSet
  refine ⟨2 * (volume (tsupport w)).toReal * L ^ 2, by positivity, fun h => ?_⟩
  set A : Set (Space d) := tsupport w ∪ (fun y : Space d => y + h) ⁻¹' tsupport w with hA
  have hmA : MeasurableSet A := hmK.union (measurable_add_const h hmK)
  have hVtr : volume ((fun y : Space d => y + h) ⁻¹' tsupport w) = volume (tsupport w) :=
    measure_preimage_add_right volume h (tsupport w)
  have hVA : volume A ≤ 2 * volume (tsupport w) := by
    refine le_trans (measure_union_le _ _) ?_
    rw [hVtr, two_mul]
  have hVA' : volume A ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hVA
    simp [hVK, ENNReal.mul_eq_top]
  have hVAr : (volume A).toReal ≤ 2 * (volume (tsupport w)).toReal := by
    have := ENNReal.toReal_mono (by simp [hVK, ENNReal.mul_eq_top]) hVA
    simpa [ENNReal.toReal_mul] using this
  -- the integrand is bounded by `L²‖h‖²` and supported in `A`
  have hpt : ∀ z : Space d, (w z - w (z + h)) ^ 2 ≤ L ^ 2 * ‖h‖ ^ 2 := by
    intro z
    have h1 := hL z (z + h)
    have h2 : ‖z - (z + h)‖ = ‖h‖ := by
      rw [show z - (z + h) = -h by abel, norm_neg]
    rw [h2] at h1
    have h3 : |w z - w (z + h)| ^ 2 = (w z - w (z + h)) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (w z - w (z + h)), mul_nonneg hL0 (norm_nonneg h)]
  have hmaj : Integrable (A.indicator (fun _ : Space d => L ^ 2 * ‖h‖ ^ 2)) :=
    (integrableOn_const hVA').integrable_indicator hmA
  have hgle : ∀ z : Space d, (w z - w (z + h)) ^ 2 ≤
      A.indicator (fun _ : Space d => L ^ 2 * ‖h‖ ^ 2) z := by
    intro z
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz]; exact hpt z
    · have h0 : w z - w (z + h) = 0 := by
        by_contra hc
        exact hz (translate_support_subset hw h z hc)
      rw [Set.indicator_of_notMem hz, h0]
      norm_num
  have hmain : ∫ z : Space d, (w z - w (z + h)) ^ 2 ≤
      ∫ z : Space d, A.indicator (fun _ : Space d => L ^ 2 * ‖h‖ ^ 2) z :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _) hmaj
      (Filter.Eventually.of_forall hgle)
  have hind : ∫ z : Space d, A.indicator (fun _ : Space d => L ^ 2 * ‖h‖ ^ 2) z
      = (volume A).toReal * (L ^ 2 * ‖h‖ ^ 2) := by
    rw [integral_indicator hmA, setIntegral_const, smul_eq_mul, measureReal_def]
  rw [hind] at hmain
  refine le_trans hmain ?_
  have hnn : (0:ℝ) ≤ L ^ 2 * ‖h‖ ^ 2 := by positivity
  nlinarith [ENNReal.toReal_nonneg (a := volume A)]

end Sandpile.Support
