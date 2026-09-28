import Sandpile.Support.D4SStep2Inputs
import Sandpile.Support.D4SStep2Scales
import Sandpile.Support.D4SStep2Second
import Sandpile.Support.D4SStep2Mesh
import Sandpile.Support.D4SMarkov
import Sandpile.Support.ContDGT4Membrane

/-!
# Step 2: Negligibility of the Smoothed Linearization Error

Step 2 of `prop:d4-superdiffusive-limit` (`sandpile.tex:3368-3382`): the
smoothed linearization error is negligible in `H^{-s}(D)`.

The paper writes the conclusion as `\E\|((P^{n_R}E_{t_R-n_R})^{(R)})^\omega\|^2
_{H^{-s}(D)}\to0` and proves it by two displays: the field is flat at the scale
of the mesh except for a parity-class constant, and the parity-class constant
cancels against the `\omega`-shift. What the limit theorem consumes is
convergence to zero in probability, and Markov's inequality gives it from the
expectations of the two dominating variables, so no second moment of the norm
itself has to be formed.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

open Sandpile.Support Sandpile.Continuum Sandpile.D4Super

/-- The smoothed centred error `F_R = P^{n_R}E_{t_R-n_R}` of Step 2. -/
noncomputable def smoothedError (ν : Measure ℝ) (α R : ℝ) (ζ : Site 4 → ℝ) : Site 4 → ℝ :=
  avg^[⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊]
    (linError ν (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ)

/-- **Step 2 of `prop:d4-superdiffusive-limit`.**  At superdiffusive times the
`ω`-representative of the rescaled smoothed error tends to zero in probability
in `H^{-s}(D)`. -/
theorem tendsto_step2_four (hHK : External.HeatKernelBounds) (hVS : External.VarianceScale)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    {D : Set (Space 4)} (hD : IsDomain D) {w : Space 4 → ℝ} (hw : IsAveragingDensity D w)
    {α : ℝ} (hα : 2 < α) {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => LatticeProb.iidLaw 4 ν
      {ζ | ENNReal.ofReal ε <
        negSobolevNorm 4 s D (omegaRep D w (latticePairing R (smoothedError ν α R ζ)))})
      atTop (𝓝 0) := by
  classical
  set P : Measure (Site 4 → ℝ) := LatticeProb.iidLaw 4 ν with hP
  obtain ⟨M, hM, hsecond⟩ := exists_linError_second_moment hVS ν hmean θ hθ hexp
  obtain ⟨K, L, hK0, hL0, hKb⟩ := exists_negSobolevNorm_omegaRep_le (d := 4) hs.le hD hw
  obtain ⟨Cm, hCm0, hmesh⟩ := exists_integral_mesh_sum_parity_le hHK
  obtain ⟨K2, hK20, hK2b⟩ := exists_negSobolevNorm_parityConst_le (d := 4) hs hD hw (0 : Fin 4)
  obtain ⟨rD, hrD⟩ := hD.2.1.subset_closedBall (0 : Space 4)
  set Lw : ℝ := max rD 0 with hLw
  have hLwd : ∀ z ∈ D, ‖z‖ ≤ Lw := by
    intro z hz
    have := hrD hz
    rw [mem_closedBall_zero_iff] at this
    exact le_trans this (le_max_left _ _)
  set σ : ℝ := min s 1 with hσ
  have hσ0 : 0 < σ := lt_min hs zero_lt_one
  -- the two pieces of the splitting
  set N1 : ℝ → (Site 4 → ℝ) → ℝ≥0∞ := fun R ζ =>
    negSobolevNorm 4 s D (omegaRep D w (latticePairing R
      (fun x => smoothedError ν α R ζ x - smoothedError ν α R ζ (parityBase x)))) with hN1
  set N2 : ℝ → (Site 4 → ℝ) → ℝ≥0∞ := fun R ζ =>
    negSobolevNorm 4 s D (omegaRep D w (latticePairing R
      (fun x => smoothedError ν α R ζ (parityBase x)))) with hN2
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
    (((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) * (R⁻¹) ^ (2 * σ))) with hB2
  -- the bookkeeping that holds for large `R`
  have hev : ∀ᶠ R : ℝ in atTop, (2:ℝ) ≤ R ∧
      1 ≤ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ∧
      ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ≤ ⌊R ^ α⌋₊ ∧
      3 ≤ ⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ := eventually_step2_scales α hα
  -- the second moment of the centred error at the time the window leaves
  have hmom : ∀ R : ℝ, 3 ≤ ⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ →
      ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ≤ ⌊R ^ α⌋₊ →
      (∀ z : Site 4, Integrable (fun ζ =>
        (linError ν (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ z) ^ 2) P) ∧
      (∀ z : Site 4, ∫ ζ, (linError ν
        (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ z) ^ 2 ∂P ≤
          (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) := by
    intro R h3 hnt
    refine ⟨fun z => (hsecond _ h3 z).1, fun z => ?_⟩
    refine le_trans (hsecond _ h3 z).2 ?_
    exact sq_loglog_mono h3 (Nat.sub_le _ _) M
  -- the splitting of the norm at the parity-class constant
  have hsplit : ∀ R : ℝ, ∀ ζ : Site 4 → ℝ,
      negSobolevNorm 4 s D (omegaRep D w (latticePairing R (smoothedError ν α R ζ)))
        ≤ N1 R ζ + N2 R ζ := by
    intro R ζ
    rw [hN1, hN2]
    refine negSobolevNorm_le_add s D _ _ _ ?_
    intro φ hφ
    have hshift : IsTestFn (Set.univ : Set (Space 4)) (omegaShift D w φ) :=
      isTestFn_univ_omegaShift hw.1 hφ
    have hintφ : Integrable (omegaShift D w φ) :=
      hshift.1.continuous.integrable_of_hasCompactSupport hshift.2.1
    have hsupp : ∀ z : Space 4, omegaShift D w φ z ≠ 0 → ‖z‖ ≤ Lw := by
      intro z hz
      by_cases hφz : φ z = 0
      · have hwz : w z ≠ 0 := by
          intro hc
          exact hz (by show φ z - w z * _ = 0; rw [hφz, hc]; ring)
        exact hLwd z (hw.1.2.2 (subset_tsupport _ hwz))
      · exact hLwd z (hφ.2.2 (subset_tsupport _ hφz))
    have hsub := latticePairing_sub R (smoothedError ν α R ζ)
      (fun x => smoothedError ν α R ζ (parityBase x)) (omegaShift D w φ) hintφ hsupp
    have hrep : ∀ f : Site 4 → ℝ,
        omegaRep D w (latticePairing R f) φ = latticePairing R f (omegaShift D w φ) :=
      fun _ => rfl
    rw [hrep, hrep, hrep]
    have heq : latticePairing R (smoothedError ν α R ζ) (omegaShift D w φ)
        = latticePairing R
            (fun x => smoothedError ν α R ζ x - smoothedError ν α R ζ (parityBase x))
            (omegaShift D w φ)
          + latticePairing R (fun x => smoothedError ν α R ζ (parityBase x))
            (omegaShift D w φ) := by
      rw [hsub]; ring
    rw [heq]
    exact abs_add_le _ _
  -- the first display, by Markov against the mesh sum
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
      exact hKb R hR0 _
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
      have hKsq : (0:ℝ) ≤ K ^ 2 := sq_nonneg K
      exact mul_le_mul_of_nonneg_left hb hKsq
    · rw [hB1]
      have h := (tendsto_scale_sep_first_sq α hα M hM).const_mul (Cm * (L + 3) ^ 6)
      have h2 := h.const_mul (K ^ 2)
      simpa using h2
  -- the second display, by Markov against the parity imbalance
  have hM2 : Tendsto (fun R : ℝ => P {ζ | ENNReal.ofReal (ε / 2) < N2 R ζ}) atTop (𝓝 0) := by
    refine tendsto_measure_gt_of_tendsto_bound P N2 Y2 B2 (fun R => K2 * (R⁻¹) ^ σ)
      ?_ ?_ ?_ ?_ ?_ ?_ (by positivity)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR0
      have : (0:ℝ) ≤ (R⁻¹) ^ σ := (Real.rpow_pos_of_pos (by positivity) σ).le
      exact mul_nonneg hK20 this
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
      refine le_trans hb (le_of_eq ?_)
      congr 1
      rw [Real.sqrt_sq_eq_abs]
      ring
    · filter_upwards [hev] with R hRs
      obtain ⟨hR2, hn1, hnt, h3⟩ := hRs
      have hR0 : (0:ℝ) < R := by linarith
      have hmeas : ∀ z : Site 4, AEStronglyMeasurable (fun ζ =>
          linError ν (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ z) P :=
        fun z => (measurable_linError ν _ z).aestronglyMeasurable
      obtain ⟨hi, hV⟩ := hmom R h3 hnt
      have hb := integral_sq_smoothing_increment_le_four (by norm_num : (1:ℕ) ≤ 4) P
        (fun ζ => linError ν (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) ζ)
        (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) 0 ((0 : Site 4) + unit (0 : Fin 4))
        ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) hi hV
      have hb' : ∫ ζ, (smoothedError ν α R ζ 0 -
          smoothedError ν α R ζ ((0 : Site 4) + unit (0 : Fin 4))) ^ 2 ∂P ≤
          4 * ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) := hb
      rw [hB2, hY2]
      have hsq : (K2 * (R⁻¹) ^ σ) ^ 2 = K2 ^ 2 * (R⁻¹) ^ (2 * σ) := by
        rw [mul_pow, rpow_sq_eq R⁻¹ σ (by positivity)]
      rw [hsq]
      have hrn : (0:ℝ) ≤ (R⁻¹) ^ (2 * σ) := (Real.rpow_pos_of_pos (by positivity) _).le
      have hK2sq : (0:ℝ) ≤ K2 ^ 2 := sq_nonneg K2
      have hcA : (0:ℝ) ≤ K2 ^ 2 * (R⁻¹) ^ (2 * σ) := mul_nonneg hK2sq hrn
      have hstep := mul_le_mul_of_nonneg_left hb' hcA
      nlinarith [hstep]
    · rw [hB2]
      have h := (tendsto_loglog_mul_rpow_inv α hα M (2 * σ) hM (by positivity)).const_mul 4
      have h2 := h.const_mul (K2 ^ 2)
      simpa using h2
  -- assemble
  have hsum : Tendsto (fun R : ℝ =>
      P {ζ | ENNReal.ofReal (ε / 2) < N1 R ζ} + P {ζ | ENNReal.ofReal (ε / 2) < N2 R ζ})
      atTop (𝓝 0) := by
    have h := hM1.add hM2
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun R => by simp)
    (Filter.Eventually.of_forall fun R =>
      measure_gt_le_add P _ (N1 R) (N2 R) (hsplit R) hε)

end Sandpile
