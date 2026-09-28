import Sandpile.Support.MeanAMgf
import Sandpile.Support.MeanAScale
import Sandpile.Support.ContMeanAsymptotic
import Sandpile.Support.MeanAInterp

/-!
# Uniform mean and variance bounds for the rescaled odometer

The mean of the rescaled odometer is bounded uniformly in the scale. `sandpile.tex:1995-2007`
reads the uniform exponential moment of `prop:continuum-value-selfsimilar` off the centred
variable `𝒰_R(1,0) - E𝒰_R(1,0)`, so it becomes a statement about `𝒰_R(1,0)` itself only once
the means are bounded. They are, and the argument needs no exponential input
(`exists_uniform_mean_rescaled_of_tail`, `exists_uniform_mean_rescaled_of_tightness`): the
tightness of the family at the origin gives one level `M` that the variable exceeds with
probability at most one half at every scale, the variance of `𝒰_R(1,0)` is bounded uniformly
in `R` (`exists_uniform_variance_rescaled_mass`) because the square sum of the Green weights
at the parabolic scale is (`eq:Qt-table` at `t = ⌊R²⌋`), and Chebyshev at a deviation larger
than twice that variance forbids the mean from standing more than that deviation above the
level (`mean_le_of_tail_and_variance`). `exists_uniform_exp_moment_rescaled_mass` then
combines the mean bound with the exponential moment of the centred variable to give the
uniform exponential moment of the rescaled odometer itself.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

variable {d : ℕ}

/-- **A mean bound from a tail bound and a variance bound.**  If a square
integrable variable exceeds the level `M` with probability at most one half and
its variance is less than `s²/2`, then its mean is at most `M + s`. -/
theorem mean_le_of_tail_and_variance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hmX : Measurable X) (hmem : MemLp X 2 P)
    (M s : ℝ) (hs : 0 < s)
    (htail : P {ω | M < X ω} ≤ ENNReal.ofReal (1 / 2))
    (hvar : variance X P < s ^ 2 / 2) :
    ∫ ω, X ω ∂P ≤ M + s := by
  by_contra hcontra
  have hcon : M + s < ∫ ω, X ω ∂P := not_le.mp hcontra
  set m : ℝ := ∫ ω, X ω ∂P with hm
  have hcheb : P {ω | s ≤ |X ω - m|} ≤ ENNReal.ofReal (variance X P / s ^ 2) :=
    ProbabilityTheory.meas_ge_le_variance_div_sq hmem hs
  have hsubset : {ω | X ω ≤ M} ⊆ {ω | s ≤ |X ω - m|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have hmeas : MeasurableSet {ω | M < X ω} := measurableSet_lt measurable_const hmX
  have hcompl : {ω | M < X ω}ᶜ = {ω | X ω ≤ M} := by
    ext ω; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  have h2 : ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have h3 : (1 : ENNReal) - ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / 2) := by
    rw [← h2, ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top]
  have hlow : ENNReal.ofReal (1 / 2) ≤ P {ω | X ω ≤ M} := by
    rw [← hcompl, prob_compl_eq_one_sub hmeas]
    calc ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := h3.symm
      _ ≤ 1 - P {ω | M < X ω} := tsub_le_tsub_left htail 1
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hlt : variance X P / s ^ 2 < 1 / 2 := by
    rw [div_lt_iff₀ hs2]
    linarith [hvar]
  have hchain : ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (variance X P / s ^ 2) :=
    le_trans hlow (le_trans (measure_mono hsubset) hcheb)
  have hnn : (0 : ℝ) ≤ variance X P / s ^ 2 :=
    div_nonneg (variance_nonneg X P) hs2.le
  rw [ENNReal.ofReal_le_ofReal_iff hnn] at hchain
  linarith

/-- The variance of the odometer at the origin is the same in the mass language
of the theorems and in the scenery language of the estimates. -/
theorem variance_odometer_mass_eq (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (t : ℕ) :
    variance (fun σ => Sandpile.odometer σ t 0) (Sandpile.centeredMassLaw d ν)
      = variance (fun ζ => Sandpile.odometerOf ζ t 0) (LatticeProb.iidLaw d ν) := by
  have hmean : (∫ σ, Sandpile.odometer σ t 0 ∂(Sandpile.centeredMassLaw d ν))
      = ∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) :=
    integral_comp_odometer_eq d ν hd t (fun s => s) measurable_id
  rw [variance_eq_integral (Sandpile.measurable_odometer t 0).aemeasurable,
    variance_eq_integral (Sandpile.measurable_odometerOf t 0).aemeasurable, hmean]
  exact integral_comp_odometer_eq d ν hd t
    (fun s => (s - ∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)) ^ 2)
    ((measurable_id.sub measurable_const).pow_const 2)

/-- **The variance of the odometer is at most a constant times the variance of
the membrane field at the same time.**  This is the third clause of
`prop:finite-time-concentration-scale` at `p = 2`. -/
theorem exists_variance_odometer_le_membrane (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      variance (fun ζ => Sandpile.odometerOf ζ t 0) (LatticeProb.iidLaw d ν)
        ≤ C * variance (fun ζ => Sandpile.membrane ζ t 0) (LatticeProb.iidLaw d ν) := by
  obtain ⟨C, hC, hb⟩ := Sandpile.exists_odometer_moment_variance (d := d) ν (p := 2) le_rfl
    (Sandpile.integrable_abs_rpow_two ν hsq)
  refine ⟨C, hC, fun t => ?_⟩
  have hbx := hb t (0 : Sandpile.Site d)
  have hrw : ∀ ζ : Sandpile.Site d → ℝ,
      |Sandpile.odometerOf ζ t 0 -
          ∫ η, Sandpile.odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)| ^ (2 : ℝ)
        = (Sandpile.odometerOf ζ t 0 -
          ∫ η, Sandpile.odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)) ^ 2 := by
    intro ζ
    set a : ℝ := Sandpile.odometerOf ζ t 0 -
      ∫ η, Sandpile.odometerOf η t 0 ∂(LatticeProb.iidLaw d ν) with ha
    have h1 : |a| ^ (2 : ℝ) = |a| ^ (2 : ℕ) := by
      have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
      have h := Real.rpow_natCast |a| 2
      rw [hcast] at h
      exact h
    rw [h1, sq_abs]
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw)] at hbx
  have hexp : variance (fun ζ => Sandpile.membrane ζ t 0) (LatticeProb.iidLaw d ν) ^ ((2 : ℝ) / 2)
      = variance (fun ζ => Sandpile.membrane ζ t 0) (LatticeProb.iidLaw d ν) := by
    norm_num
  rw [hexp] at hbx
  rwa [variance_eq_integral (Sandpile.measurable_odometerOf t 0).aemeasurable]

/-- **The variance of the rescaled odometer is bounded uniformly in the scale.**
`eq:Qt-table` at `t = ⌊R²⌋` makes the square sum of the Green weights uniform,
and the third clause of `prop:finite-time-concentration-scale` turns that into a
bound on the variance of the odometer itself. -/
theorem exists_uniform_variance_rescaled_mass (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : Integrable (fun z : ℝ => z ^ 2) ν) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ R : ℝ, 1 ≤ R →
      variance (fun σ => Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
        (Sandpile.centeredMassLaw d ν) ≤ V := by
  obtain ⟨C, hC, hCb⟩ := exists_variance_odometer_le_membrane d ν hsq
  obtain ⟨M, hM1, hMb⟩ := exists_scaled_greenTime_sq_bound d hd hd3
  have hid : MemLp (id : ℝ → ℝ) 2 ν :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 (by simpa using hsq)
  have hvn : (0 : ℝ) ≤ variance (id : ℝ → ℝ) ν := variance_nonneg _ _
  refine ⟨C * variance (id : ℝ → ℝ) ν * M,
    mul_nonneg (mul_nonneg hC.le hvn) (by linarith), fun R hR => ?_⟩
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  set a : ℝ := R ^ (-(2 - (d : ℝ) / 2)) with ha
  set G : ℝ := ∑' z : Sandpile.Site d, Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z ^ 2 with hG
  have hGnn : (0 : ℝ) ≤ G := tsum_nonneg fun z => sq_nonneg _
  have ha2 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg _
  have hfun : (fun σ => Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
      = fun σ => a * Sandpile.odometer σ ⌊R ^ 2⌋₊ 0 := by
    funext σ; exact rescaledOdometer_one_zero d R σ
  rw [hfun, variance_const_mul, variance_odometer_mass_eq d ν hd]
  have h1 := hCb ⌊R ^ 2⌋₊
  rw [variance_membrane ν hid ⌊R ^ 2⌋₊ 0] at h1
  have hsplit : (∑' z : Sandpile.Site d, (a * Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z) ^ 2)
      = a ^ 2 * G := by
    rw [hG, ← tsum_mul_left]
    exact tsum_congr fun z => by ring
  have h2 : a ^ 2 * G ≤ M := hsplit ▸ hMb R hR
  calc a ^ 2 * variance (fun ζ => Sandpile.odometerOf ζ ⌊R ^ 2⌋₊ 0) (LatticeProb.iidLaw d ν)
      ≤ a ^ 2 * (C * (variance (id : ℝ → ℝ) ν * G)) := by
        exact mul_le_mul_of_nonneg_left h1 ha2
    _ = C * variance (id : ℝ → ℝ) ν * (a ^ 2 * G) := by ring
    _ ≤ C * variance (id : ℝ → ℝ) ν * M :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hC.le hvn)

/-- **The mean of the rescaled odometer is bounded uniformly in the scale.**
The input is the tightness of the family at the origin at the level one half,
which is the uniform-norm clause of `thm:main-explosion`(i)(b) read on the
compact `{0}`; the variance bound is the one above, and no exponential moment
is needed. -/
theorem exists_uniform_mean_rescaled_of_tail (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    (M : ℝ)
    (htail : ∀ R : ℝ, 1 ≤ R →
      Sandpile.centeredMassLaw d ν
          {σ | M < Sandpile.Continuum.rescaledOdometer d R 1 0 σ} ≤ ENNReal.ofReal (1 / 2)) :
    ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R →
      ∫ σ, Sandpile.Continuum.rescaledOdometer d R 1 0 σ
        ∂(Sandpile.centeredMassLaw d ν) ≤ K := by
  obtain ⟨V, hV, hVb⟩ := exists_uniform_variance_rescaled_mass d hd hd3 ν hsq
  refine ⟨M + Real.sqrt (2 * V + 1), fun R hR => ?_⟩
  set s : ℝ := Real.sqrt (2 * V + 1) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hssq : s ^ 2 = 2 * V + 1 := Real.sq_sqrt (by linarith)
  have hmeas : Measurable (fun σ => Sandpile.Continuum.rescaledOdometer d R 1 0 σ) := by
    unfold Sandpile.Continuum.rescaledOdometer
    exact (Sandpile.measurable_odometer _ _).const_mul _
  refine mean_le_of_tail_and_variance (Sandpile.centeredMassLaw d ν)
    (fun σ => Sandpile.Continuum.rescaledOdometer d R 1 0 σ) hmeas
    (memLp_rescaledOdometer_centered d hd ν hsq R 1 0) M s hs0 (htail R hR) ?_
  rw [hssq]
  linarith [hVb R hR]

/-- **The mean bound from the tightness clause of `thm:main-explosion`(i)(b).**
At the compact `{0}`, at `T = 1` and at `ε = 1/2`, the uniform-norm clause of
that theorem is exactly the tail hypothesis above, because the rescaled odometer
at the origin is the interpolated field there. -/
theorem exists_uniform_mean_rescaled_of_tightness (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
      Sandpile.centeredMassLaw d ν
          {σ | ∃ z ∈ ({0} : Set (Sandpile.Continuum.Space d)),
            M < |Sandpile.Continuum.multilinearInterp R
              (fun y => R ^ (-(2 - (d : ℝ) / 2)) *
                Sandpile.odometer σ ⌊(1 : ℝ) * R ^ 2⌋₊ y) z|}
        ≤ ENNReal.ofReal ε) :
    ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R →
      ∫ σ, Sandpile.Continuum.rescaledOdometer d R 1 0 σ
        ∂(Sandpile.centeredMassLaw d ν) ≤ K := by
  obtain ⟨M, hM⟩ := htight (1 / 2) (by norm_num)
  refine exists_uniform_mean_rescaled_of_tail d hd hd3 ν hsq M (fun R hR => ?_)
  refine le_trans (measure_mono ?_) (hM R hR)
  intro σ hσ
  simp only [Set.mem_setOf_eq] at hσ ⊢
  refine ⟨0, Set.mem_singleton 0, ?_⟩
  rw [← rescaledOdometer_zero_eq_multilinearInterp d R 1
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hR)) σ]
  exact lt_of_lt_of_le hσ (le_abs_self _)

/-- **The uniform exponential moment of the rescaled odometer.**  The first
display of the middle clause of `prop:continuum-value-selfsimilar`.  The centred
variable has one exponential moment uniform in the scale, and the means are
bounded uniformly, so the variable itself does. -/
theorem exists_uniform_exp_moment_rescaled_mass (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ θ A : ℝ, 0 < θ ∧
      ∀ ν : Measure ℝ, ∀ _ : IsProbabilityMeasure ν,
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ K : ℝ, (∀ R : ℝ, 1 ≤ R →
            ∫ σ, Sandpile.Continuum.rescaledOdometer d R 1 0 σ
              ∂(Sandpile.centeredMassLaw d ν) ≤ K) →
        ∀ R : ℝ, 1 ≤ R →
          Integrable (fun σ => Real.exp (θ *
            Sandpile.Continuum.rescaledOdometer d R 1 0 σ)) (Sandpile.centeredMassLaw d ν) ∧
          (∫ σ, Real.exp (θ * Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
            ∂(Sandpile.centeredMassLaw d ν)) ≤ Real.exp (θ * K) * A := by
  obtain ⟨θ, A, hθ, hA, hmain⟩ := exists_uniform_mgf_rescaled_mass d hd hd3 θ₀ K₀ hθ₀
  refine ⟨θ, A, hθ, ?_⟩
  intro ν hprob hint hexp K hK R hR
  haveI := hprob
  set c : ℝ := ∫ σ, Sandpile.Continuum.rescaledOdometer d R 1 0 σ
    ∂(Sandpile.centeredMassLaw d ν) with hc
  obtain ⟨hI, hB⟩ := hmain ν hprob hint hexp R hR
  have hrew : (fun σ : Sandpile.Site d → ℝ => Real.exp (θ *
      (R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊R ^ 2⌋₊ 0 -
        ∫ τ, R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer τ ⌊R ^ 2⌋₊ 0
          ∂(Sandpile.centeredMassLaw d ν))))
      = fun σ => Real.exp (θ * (Sandpile.Continuum.rescaledOdometer d R 1 0 σ - c)) := by
    have hmean : (∫ τ, R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer τ ⌊R ^ 2⌋₊ 0
        ∂(Sandpile.centeredMassLaw d ν)) = c := by
      rw [hc]
      exact integral_congr_ae (Filter.Eventually.of_forall fun σ =>
        (rescaledOdometer_one_zero d R σ).symm)
    funext σ
    rw [hmean, rescaledOdometer_one_zero d R σ]
  rw [hrew] at hI hB
  have hsplit : ∀ σ : Sandpile.Site d → ℝ,
      Real.exp (θ * Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
        = Real.exp (θ * c) *
          Real.exp (θ * (Sandpile.Continuum.rescaledOdometer d R 1 0 σ - c)) := by
    intro σ
    rw [← Real.exp_add]
    ring_nf
  constructor
  · refine (hI.const_mul (Real.exp (θ * c))).congr
      (Filter.Eventually.of_forall fun σ => ?_)
    exact (hsplit σ).symm
  · rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_const_mul]
    have hnn : (0 : ℝ) ≤ ∫ σ, Real.exp (θ *
        (Sandpile.Continuum.rescaledOdometer d R 1 0 σ - c))
        ∂(Sandpile.centeredMassLaw d ν) :=
      integral_nonneg fun σ => (Real.exp_nonneg _)
    have hexple : Real.exp (θ * c) ≤ Real.exp (θ * K) := by
      refine Real.exp_le_exp.2 ?_
      have := hK R hR
      nlinarith [hθ]
    calc Real.exp (θ * c) * ∫ σ, Real.exp (θ *
          (Sandpile.Continuum.rescaledOdometer d R 1 0 σ - c))
          ∂(Sandpile.centeredMassLaw d ν)
        ≤ Real.exp (θ * K) * A := by
          exact mul_le_mul hexple hB hnn (Real.exp_nonneg _)


end Sandpile.Support
