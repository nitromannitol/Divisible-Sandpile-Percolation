import Sandpile.Support.D4SPairing
import Sandpile.Support.D4SStep3

/-!
# Steps 2 and 3 of the superdiffusive limit, in pairing form

Steps 2 and 3 of `prop:d4-superdiffusive-limit` in the pairing form the first clause of the
statement needs (`sandpile.tex:3368-3404`). The convergence in distribution of the proposition is
tested against one test function at a time, with no normalisation of its `H^s` norm, so the two
steps are repeated here with the `H^{-s}(D)` norm replaced by the absolute value of the pairing
with a single test function: `tendsto_step2_pairing_four` and `tendsto_step3_pairing_four`. The
proofs are the ones of the norm form with `Sandpile.Support.exists_abs_pairing_omegaRep_le` and
`Sandpile.Support.exists_abs_pairing_parityConst_le` in place of their unit-ball counterparts; the
rate of the second display improves to `R^{-1}`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

open Sandpile.Support Sandpile.Continuum Sandpile.D4Super

/-- **Step 2 in pairing form.** -/
theorem tendsto_step2_pairing_four (hHK : External.HeatKernelBounds) (hVS : External.VarianceScale)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    {D : Set (Space 4)} (hD : IsDomain D) {w : Space 4 → ℝ} (hw : IsAveragingDensity D w)
    {α : ℝ} (hα : 2 < α) {φ : Space 4 → ℝ} (hφ : IsTestFn D φ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => LatticeProb.iidLaw 4 ν
      {ζ | ENNReal.ofReal ε < ENNReal.ofReal
        |omegaRep D w (latticePairing R (smoothedError ν α R ζ)) φ|}) atTop (𝓝 0) := by
  classical
  set P : Measure (Site 4 → ℝ) := LatticeProb.iidLaw 4 ν with hP
  obtain ⟨M, hM, hsecond⟩ := exists_linError_second_moment hVS ν hmean θ hθ hexp
  obtain ⟨K, L, hK0, hL0, hKb⟩ := exists_abs_pairing_omegaRep_le (d := 4) hD hw hφ
  obtain ⟨Cm, hCm0, hmesh⟩ := exists_integral_mesh_sum_parity_le hHK
  obtain ⟨K2, hK20, hK2b⟩ := exists_abs_pairing_parityConst_le (d := 4) hD hw (0 : Fin 4) hφ
  set N1 : ℝ → (Site 4 → ℝ) → ℝ≥0∞ := fun R ζ => ENNReal.ofReal
    |omegaRep D w (latticePairing R
      (fun x => smoothedError ν α R ζ x - smoothedError ν α R ζ (parityBase x))) φ| with hN1
  set N2 : ℝ → (Site 4 → ℝ) → ℝ≥0∞ := fun R ζ => ENNReal.ofReal
    |omegaRep D w (latticePairing R (fun x => smoothedError ν α R ζ (parityBase x))) φ| with hN2
  set Y1 : ℝ → (Site 4 → ℝ) → ℝ := fun R ζ =>
    R⁻¹ ^ 4 * ∑ x ∈ Sandpile.boxFinset (0 : Site 4) (⌈|R| * L⌉₊ + 1),
      (smoothedError ν α R ζ x - smoothedError ν α R ζ (parityBase x)) ^ 2 with hY1
  set Y2 : ℝ → (Site 4 → ℝ) → ℝ := fun R ζ =>
    (smoothedError ν α R ζ 0 - smoothedError ν α R ζ ((0 : Site 4) + unit (0 : Fin 4))) ^ 2
    with hY2
  set B1 : ℝ → ℝ := fun R => K ^ 2 * (Cm * (L + 3) ^ 6 *
    (R ^ 2 * ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M)
      / (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ))) with hB1
  set B2 : ℝ → ℝ := fun R => K2 ^ 2 * (4 *
    (((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) * (R⁻¹) ^ 2)) with hB2
  have hev : ∀ᶠ R : ℝ in atTop, (2:ℝ) ≤ R ∧
      1 ≤ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ∧
      ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ≤ ⌊R ^ α⌋₊ ∧
      3 ≤ ⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ := eventually_step2_scales α hα
  have hmom : ∀ R : ℝ, 3 ≤ ⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ →
      ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ≤ ⌊R ^ α⌋₊ →
      (∀ z : Site 4, Integrable (fun ζ =>
        (linError ν (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ z) ^ 2) P) ∧
      (∀ z : Site 4, ∫ ζ, (linError ν
        (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ z) ^ 2 ∂P ≤
          (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) := by
    intro R h3 hnt
    refine ⟨fun z => (hsecond _ h3 z).1, fun z => ?_⟩
    exact le_trans (hsecond _ h3 z).2 (sq_loglog_mono h3 (Nat.sub_le _ _) M)
  have hsplit : ∀ R : ℝ, ∀ ζ : Site 4 → ℝ,
      ENNReal.ofReal |omegaRep D w (latticePairing R (smoothedError ν α R ζ)) φ|
        ≤ N1 R ζ + N2 R ζ := by
    intro R ζ
    obtain ⟨Lw, hLw0, hLw⟩ := exists_radius_of_isDomain hD
    have hshift : IsTestFn (Set.univ : Set (Space 4)) (omegaShift D w φ) :=
      isTestFn_univ_omegaShift hw.1 hφ
    have hintφ : Integrable (omegaShift D w φ) :=
      hshift.1.continuous.integrable_of_hasCompactSupport hshift.2.1
    have hsub := latticePairing_sub R (smoothedError ν α R ζ)
      (fun x => smoothedError ν α R ζ (parityBase x)) (omegaShift D w φ) hintφ
      (omegaShift_support hw.1 hφ hLw)
    have hrep : ∀ f : Site 4 → ℝ,
        omegaRep D w (latticePairing R f) φ = latticePairing R f (omegaShift D w φ) :=
      fun _ => rfl
    simp only [hN1, hN2, hrep]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : latticePairing R (smoothedError ν α R ζ) (omegaShift D w φ)
        = latticePairing R
            (fun x => smoothedError ν α R ζ x - smoothedError ν α R ζ (parityBase x))
            (omegaShift D w φ)
          + latticePairing R (fun x => smoothedError ν α R ζ (parityBase x))
            (omegaShift D w φ) := by rw [hsub]; ring
    rw [heq]
    exact abs_add_le _ _
  have hM1 : Tendsto (fun R : ℝ => P {ζ | ENNReal.ofReal (ε / 2) < N1 R ζ}) atTop (𝓝 0) := by
    refine tendsto_measure_gt_of_tendsto_bound P N1 Y1 B1 (fun _ => K)
      (Filter.Eventually.of_forall fun _ => hK0) ?_ ?_ ?_ ?_ ?_ (by positivity)
    · intro R ζ
      rw [hY1]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => sq_nonneg _)
    · filter_upwards [hev] with R hRs
      obtain ⟨hR2, hn1, hnt, h3⟩ := hRs
      have hmeas : ∀ z : Site 4, AEStronglyMeasurable (fun ζ =>
          linError ν (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ z) P :=
        fun z => (measurable_linError ν _ z).aestronglyMeasurable
      have hi := (hmom R h3 hnt).1
      rw [hY1]
      exact (integrable_finsetSum _ (fun x _ => integrable_sq_smoothing_increment P
        (fun ζ => linError ν (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ)
        (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) x (parityBase x) hmeas hi)).const_mul _
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR0 ζ
      rw [hN1, hY1]
      exact ENNReal.ofReal_le_ofReal (hKb R hR0 _)
    · filter_upwards [hev] with R hRs
      obtain ⟨hR2, hn1, hnt, h3⟩ := hRs
      have hmeas : ∀ z : Site 4, AEStronglyMeasurable (fun ζ =>
          linError ν (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ z) P :=
        fun z => (measurable_linError ν _ z).aestronglyMeasurable
      obtain ⟨hi, hV⟩ := hmom R h3 hnt
      have hb := hmesh P (fun ζ => linError ν
        (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ)
        ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) hmeas hi hV
        (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) hn1 R L (by linarith) hL0
      rw [hB1]
      exact mul_le_mul_of_nonneg_left hb (sq_nonneg K)
    · rw [hB1]
      have h := (tendsto_scale_sep_first_sq α hα M hM).const_mul (Cm * (L + 3) ^ 6)
      simpa using h.const_mul (K ^ 2)
  have hM2 : Tendsto (fun R : ℝ => P {ζ | ENNReal.ofReal (ε / 2) < N2 R ζ}) atTop (𝓝 0) := by
    refine tendsto_measure_gt_of_tendsto_bound P N2 Y2 B2 (fun R => K2 * R⁻¹)
      ?_ ?_ ?_ ?_ ?_ ?_ (by positivity)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR0
      exact mul_nonneg hK20 (by positivity)
    · intro R ζ; rw [hY2]; exact sq_nonneg _
    · filter_upwards [hev] with R hRs
      obtain ⟨hR2, hn1, hnt, h3⟩ := hRs
      have hmeas : ∀ z : Site 4, AEStronglyMeasurable (fun ζ =>
          linError ν (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ z) P :=
        fun z => (measurable_linError ν _ z).aestronglyMeasurable
      have hi := (hmom R h3 hnt).1
      rw [hY2]
      exact integrable_sq_smoothing_increment P
        (fun ζ => linError ν (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ)
        (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) 0 ((0 : Site 4) + unit (0 : Fin 4)) hmeas hi
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR1 ζ
      have hC₀ : ∀ x : Site 4, Sandpile.External.SameParity x 0 →
          smoothedError ν α R ζ (parityBase x) = smoothedError ν α R ζ 0 := by
        intro x hx; rw [parityBase, if_pos hx]
      have hC₁ : ∀ x : Site 4, ¬ Sandpile.External.SameParity x 0 →
          smoothedError ν α R ζ (parityBase x) =
            smoothedError ν α R ζ ((0 : Site 4) + unit (0 : Fin 4)) := by
        intro x hx; rw [parityBase, if_neg hx]
      have hb := hK2b R hR1 (fun x => smoothedError ν α R ζ (parityBase x))
        (smoothedError ν α R ζ 0)
        (smoothedError ν α R ζ ((0 : Site 4) + unit (0 : Fin 4))) hC₀ hC₁
      rw [hN2, hY2]
      refine ENNReal.ofReal_le_ofReal (le_trans hb (le_of_eq ?_))
      rw [Real.sqrt_sq_eq_abs]
      ring
    · filter_upwards [hev] with R hRs
      obtain ⟨hR2, hn1, hnt, h3⟩ := hRs
      have hR0 : (0:ℝ) < R := by linarith
      have hmeas : ∀ z : Site 4, AEStronglyMeasurable (fun ζ =>
          linError ν (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ z) P :=
        fun z => (measurable_linError ν _ z).aestronglyMeasurable
      obtain ⟨hi, hV⟩ := hmom R h3 hnt
      have hb : ∫ ζ, (smoothedError ν α R ζ 0 -
          smoothedError ν α R ζ ((0 : Site 4) + unit (0 : Fin 4))) ^ 2 ∂P ≤
          4 * ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) :=
        integral_sq_smoothing_increment_le_four (by norm_num : (1:ℕ) ≤ 4) P
          (fun ζ => linError ν (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ)
          (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) 0 ((0 : Site 4) + unit (0 : Fin 4))
          ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) hi hV
      rw [hB2, hY2]
      have hsq : (K2 * R⁻¹) ^ 2 = K2 ^ 2 * (R⁻¹) ^ 2 := by ring
      rw [hsq]
      have hcA : (0:ℝ) ≤ K2 ^ 2 * (R⁻¹) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hb hcA]
    · rw [hB2]
      have h := (tendsto_loglog_mul_inv_sq α hα M hM).const_mul 4
      simpa using h.const_mul (K2 ^ 2)
  have hsum : Tendsto (fun R : ℝ =>
      P {ζ | ENNReal.ofReal (ε / 2) < N1 R ζ} + P {ζ | ENNReal.ofReal (ε / 2) < N2 R ζ})
      atTop (𝓝 0) := by simpa using hM1.add hM2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun R => by simp)
    (Filter.Eventually.of_forall fun R =>
      measure_gt_le_add P _ (N1 R) (N2 R) (hsplit R) hε)

/-- **Step 3 in pairing form.** -/
theorem tendsto_step3_pairing_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hintν : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν)
    {D : Set (Space 4)} (hD : IsDomain D) {w : Space 4 → ℝ} (hw : IsAveragingDensity D w)
    {α : ℝ} (hα : 2 < α) {φ : Space 4 → ℝ} (hφ : IsTestFn D φ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => LatticeProb.iidLaw 4 ν
      {ζ | ENNReal.ofReal ε < ENNReal.ofReal
        |omegaRep D w (latticePairing R (windowField ν α R ζ)) φ|}) atTop (𝓝 0) := by
  classical
  haveI := hprob
  set P : Measure (Site 4 → ℝ) := LatticeProb.iidLaw 4 ν with hP
  obtain ⟨A₀, Cx, hA₀, hCx, hwin⟩ :=
    exists_window_second_moment_four hVS ν hprob hmean hvar hvar' θ hθ hexp hintν hpos
  obtain ⟨K, L, hK0, hL0, hKb⟩ := exists_abs_pairing_omegaRep_le (d := 4) hD hw hφ
  set mm : ℝ → ℝ := fun R =>
    ∫ η, reflectionSum η ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ 0 ∂P with hmm
  set Y : ℝ → (Site 4 → ℝ) → ℝ := fun R ζ =>
    R⁻¹ ^ 4 * ∑ x ∈ Sandpile.boxFinset (0 : Site 4) (⌈|R| * L⌉₊ + 1),
      (windowField ν α R ζ x) ^ 2 with hY
  set V : ℝ → ℝ := fun R =>
    2 * ((A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) * mm R +
      (A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) ^ 2 * (Cx / ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2))
      + 2 * (mm R) ^ 2 with hV
  set B : ℝ → ℝ := fun R => K ^ 2 * ((2 * L + 5) ^ 4 * V R) with hB
  -- the scales
  have hev : ∀ᶠ R : ℝ in atTop, (2:ℝ) ≤ R ∧
      1 ≤ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ∧
      ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ≤ ⌊R ^ α⌋₊ ∧
      3 ≤ ⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ := eventually_step2_scales α hα
  -- the uniform second moment of the centred window
  have hunif : ∀ R : ℝ, 2 ≤ R → ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ≤ ⌊R ^ α⌋₊ →
      (∀ x : Site 4, Integrable (fun ζ => (windowField ν α R ζ x) ^ 2) P) ∧
      (∀ x : Site 4, ∫ ζ, (windowField ν α R ζ x) ^ 2 ∂P ≤ V R) := by
    intro R hR hnt
    have ht2 : 2 ≤ ⌊R ^ α⌋₊ := by
      have h4 : (4:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := four_le_floor_rpow α hα R hR
      have : (2:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := by linarith
      exact_mod_cast this
    have hcon : ∀ x : Site 4, (∀ ζ : Site 4 → ℝ, (windowField ν α R ζ x) ^ 2 ≤
        2 * (reflectionSum ζ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x) ^ 2
          + 2 * (mm R) ^ 2) := by
      intro x ζ
      show (reflectionSum ζ _ _ x - mm R) ^ 2 ≤ _
      nlinarith [sq_nonneg (reflectionSum ζ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x
        + mm R)]
    have hSint : ∀ x : Site 4, Integrable (fun ζ => reflectionSum ζ
        ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x) P :=
      fun x => integrable_reflectionSum ν hintν hpos _ _ x
    have hmajx : ∀ x : Site 4, Integrable (fun ζ =>
        2 * (reflectionSum ζ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x) ^ 2
          + 2 * (mm R) ^ 2) P := by
      intro x
      exact ((hwin _ _ hnt ht2 x).1.const_mul 2).add (integrable_const _)
    have hwf : ∀ x : Site 4, Integrable (fun ζ => (windowField ν α R ζ x) ^ 2) P := by
      intro x
      refine Integrable.mono' (hmajx x)
        (((hSint x).aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2)
        (Filter.Eventually.of_forall fun ζ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hcon x ζ
    refine ⟨hwf, fun x => ?_⟩
    obtain ⟨hSsq, hSb⟩ := hwin _ _ hnt ht2 x
    have hx0 : (∫ ζ, reflectionSum ζ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x ∂P)
        = mm R := by
      have e1 := integral_reflectionSum (d := 4) (by norm_num) ν hintν hmean hpos x
        ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ hnt
      have e2 := integral_reflectionSum (d := 4) (by norm_num) ν hintν hmean hpos
        (0 : Site 4) ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ hnt
      simp only [hmm, hP]
      rw [e1, e2]
    have hmono := integral_mono (hwf x) (hmajx x) (hcon x)
    have hconst : ∫ _ζ : Site 4 → ℝ, 2 * (mm R) ^ 2 ∂P = 2 * (mm R) ^ 2 := by
      rw [hP]; simp
    rw [integral_add ((hwin _ _ hnt ht2 x).1.const_mul 2) (integrable_const _),
      integral_const_mul, hconst] at hmono
    rw [hx0] at hSb
    rw [hV]
    linarith [hmono, hSb]
  -- Markov
  refine tendsto_measure_gt_of_tendsto_bound P _ Y B (fun _ => K)
    (Filter.Eventually.of_forall fun _ => hK0) ?_ ?_ ?_ ?_ ?_ hε
  · intro R ζ
    rw [hY]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => sq_nonneg _)
  · filter_upwards [hev] with R hRs
    obtain ⟨hR2, hn1, hnt, h3⟩ := hRs
    rw [hY]
    exact (integrable_finsetSum _ (fun x _ => (hunif R hR2 hnt).1 x)).const_mul _
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR0 ζ
    rw [hY]
    exact ENNReal.ofReal_le_ofReal (hKb R hR0 _)
  · filter_upwards [hev] with R hRs
    obtain ⟨hR2, hn1, hnt, h3⟩ := hRs
    obtain ⟨hi, hVb⟩ := hunif R hR2 hnt
    have hb := integral_mesh_sum_le P (fun ζ x => windowField ν α R ζ x) (V R) hi hVb
      R L (by linarith) hL0
    rw [hB, hY]
    exact mul_le_mul_of_nonneg_left hb (sq_nonneg K)
  · rw [hB]
    have h1 : Tendsto (fun R : ℝ => (A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) * mm R) atTop (𝓝 0) :=
      tendsto_log_mul_window_mean hVS ν hprob hmean θ hθ hexp hintν hpos α hα A₀ hA₀.le
    have h0 : Tendsto mm atTop (𝓝 0) :=
      tendsto_window_mean_four hVS ν hprob hmean θ (∫ z, Real.exp (θ * |z|) ∂ν) hθ hexp
        le_rfl hintν hpos α hα 0
    have h2 : Tendsto (fun R : ℝ => (A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) ^ 2 *
        (Cx / ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2)) atTop (𝓝 0) := by
      have hT : Tendsto (fun R : ℝ => ((⌊R ^ α⌋₊ : ℝ) + 2)) atTop atTop := by
        have hpow : Tendsto (fun R : ℝ => R ^ α) atTop atTop := tendsto_rpow_atTop (by linarith)
        refine tendsto_atTop_mono' atTop ?_ hpow
        filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
        have h := Nat.lt_floor_add_one (R ^ α)
        linarith
      have hbase : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) := by
        simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have hsq2 : Tendsto (fun T : ℝ => Real.log T ^ 2 / T ^ 2) atTop (𝓝 0) := by
        have h := hbase.pow 2
        simpa [div_pow] using h
      have hlog : Tendsto (fun R : ℝ => Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2 /
          ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2) atTop (𝓝 0) := hsq2.comp hT
      have hmaj : Tendsto (fun R : ℝ => Cx *
          ((A₀ + 1) ^ 2 * (Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2 /
            ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2))) atTop (𝓝 0) := by
        simpa using (hlog.const_mul ((A₀ + 1) ^ 2)).const_mul Cx
      refine squeeze_zero' ?_ ?_ hmaj
      · filter_upwards [eventually_ge_atTop (2:ℝ)] with R hR
        exact mul_nonneg (sq_nonneg _) (div_nonneg hCx (by positivity))
      · filter_upwards [eventually_ge_atTop (2:ℝ)] with R hR
        have ht4 : (4:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := four_le_floor_rpow α hα R hR
        have hLg1 : (1:ℝ) ≤ Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) :=
          (Sandpile.log_time_bounds_four (by linarith : (3:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ))).2.2.1
        have hcoef : A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1 ≤
            (A₀ + 1) * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) := by nlinarith
        have hcoef0 : (0:ℝ) ≤ A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1 := by nlinarith
        have hCxT : (0:ℝ) ≤ Cx / ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2 := div_nonneg hCx (by positivity)
        have hsq : (A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) ^ 2 ≤
            ((A₀ + 1) * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2)) ^ 2 := pow_le_pow_left₀ hcoef0 hcoef 2
        have hexp2 : ((A₀ + 1) * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2)) ^ 2
            = (A₀ + 1) ^ 2 * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2 := by ring
        calc (A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) ^ 2 *
              (Cx / ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2)
            ≤ ((A₀ + 1) ^ 2 * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2) *
                (Cx / ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2) := by
              rw [← hexp2]; exact mul_le_mul_of_nonneg_right hsq hCxT
          _ = Cx * ((A₀ + 1) ^ 2 * (Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2 /
                ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2)) := by ring
    have hsum : Tendsto V atTop (𝓝 0) := by
      rw [hV]
      have h3 := (h1.add h2).const_mul 2
      have h4 := (h0.mul h0).const_mul 2
      have h5 := h3.add h4
      simpa [pow_two] using h5
    have h6 := (hsum.const_mul ((2 * L + 5) ^ 4)).const_mul (K ^ 2)
    simpa using h6

end Sandpile
