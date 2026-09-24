/-
The uniform exponential moment of the centred rescaled odometer,
`sandpile.tex:1995-2007`.

`lem:weighted-exp-conc` bounds the moment generating function of a
coordinate-Lipschitz functional at every parameter below the reciprocal of the
supremum of its weights, with a constant read at the gap between the two.  For
the rescaled odometer that gap moves with `R`, so the bound is made uniform by
raising one weight to the common bound `√M`: the supremum norm is then exactly
`√M`, the parameter `θ = θ₀/(2√M)` leaves the fixed gap `θ₀/2`, and the square
sum, which is what multiplies the constant, is at most `2M` by the uniform
Green bound.  The product `θ²‖ℓ‖₂²` is then at most `θ₀²/2`, independent of `R`.
-/
import Sandpile.Support.MeanAConc
import Sandpile.Support.PointwiseConc
import Sandpile.Support.SceneryBridge

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

variable {d : ℕ}

theorem lInfNorm_update_eq {N : ℕ} (ℓ : Fin N → ℝ) (i₀ : Fin N) (m : ℝ)
    (hle : ∀ i, ℓ i ≤ m) : Sandpile.lInfNorm (Function.update ℓ i₀ m) = m := by
  haveI : Nonempty (Fin N) := ⟨i₀⟩
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun i => ?_
    by_cases h : i = i₀
    · subst h; simp
    · rw [Function.update_of_ne h]; exact hle i
  · have h := LatticeProb.le_lInfNorm (Function.update ℓ i₀ m) i₀
    simpa using h

/-- **The exponential moment of a coordinate-Lipschitz functional at the
Lipschitz scale.**  If the weights have square sum at most `M`, then the
centred functional has an exponential moment at `θ = θ₀/(2√M)` bounded by a
constant depending only on `θ₀`, `K₀` and `M`.  Raising one weight to the
common bound `√M` makes the supremum norm exactly `√M`, so the gap
`θ₀ - |λ|‖ℓ‖_∞` at which the concentration constant is read is the fixed
number `θ₀/2`, uniformly in the family. -/
theorem exists_mgf_of_square_sum (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) (M : ℝ) (hM : 1 ≤ M) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (_i₀ : Fin N) (ν : Measure ℝ), IsProbabilityMeasure ν →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
      ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∑ i, ℓ i ^ 2 ≤ M) →
        (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
            |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
          Integrable (fun ξ => Real.exp (θ₀ / (2 * Real.sqrt M) *
              (F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν))))
              (Measure.pi fun _ : Fin N => ν) ∧
            ∫ ξ, Real.exp (θ₀ / (2 * Real.sqrt M) *
              (F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)))
              ∂(Measure.pi fun _ : Fin N => ν) ≤ A := by
  obtain ⟨C, hC⟩ := Sandpile.Frozen.weighted_exp_concentration.2.2.2 θ₀ K₀ hθ₀
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hs1 : (1 : ℝ) ≤ Real.sqrt M := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hM
  have hs0 : (0 : ℝ) < Real.sqrt M := lt_of_lt_of_le zero_lt_one hs1
  have hsq : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM0.le
  refine ⟨Real.exp (|C (θ₀ / 2)| * (θ₀ ^ 2 / 2)), Real.exp_pos _, ?_⟩
  intro N i₀ ν hprob hint hexp F hF ℓ hℓ hsum hlip
  haveI := hprob
  -- each weight is at most √M
  have hle : ∀ i, ℓ i ≤ Real.sqrt M := by
    intro i
    have hi : ℓ i ^ 2 ≤ M :=
      le_trans (Finset.single_le_sum (f := fun j => ℓ j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)) hsum
    nlinarith [hℓ i]
  set ℓ' : Fin N → ℝ := Function.update ℓ i₀ (Real.sqrt M) with hℓ'
  have hmono : ∀ i, ℓ i ≤ ℓ' i := by
    intro i
    by_cases h : i = i₀
    · subst h; simpa [hℓ'] using hle i
    · simp [hℓ', Function.update_of_ne h]
  have hℓ'nn : ∀ i, 0 ≤ ℓ' i := fun i => le_trans (hℓ i) (hmono i)
  have hi₀ : ℓ' i₀ = Real.sqrt M := by simp [hℓ']
  have hne : ∃ i, ℓ' i ≠ 0 := ⟨i₀, by rw [hi₀]; exact ne_of_gt hs0⟩
  have hlip' : ∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
      |F ξ - F (Function.update ξ i y)| ≤ ℓ' i * |ξ i - y| := by
    intro ξ i y
    exact le_trans (hlip ξ i y) (mul_le_mul_of_nonneg_right (hmono i) (abs_nonneg _))
  have hinf : Sandpile.lInfNorm ℓ' = Real.sqrt M := lInfNorm_update_eq ℓ i₀ _ hle
  have htwo : Sandpile.lTwoNorm ℓ' ^ 2 ≤ 2 * M := by
    rw [LatticeProb.lTwoNorm_sq]
    have hsplit : ∑ i, ℓ' i ^ 2
        = ℓ' i₀ ^ 2 + ∑ i ∈ Finset.univ.erase i₀, ℓ' i ^ 2 :=
      (Finset.add_sum_erase _ (fun i => ℓ' i ^ 2) (Finset.mem_univ i₀)).symm
    have herase : ∑ i ∈ Finset.univ.erase i₀, ℓ' i ^ 2
        = ∑ i ∈ Finset.univ.erase i₀, ℓ i ^ 2 :=
      Finset.sum_congr rfl fun i hi => by
        rw [hℓ', Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    have hle2 : ∑ i ∈ Finset.univ.erase i₀, ℓ i ^ 2 ≤ ∑ i, ℓ i ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        fun j _ _ => sq_nonneg _
    rw [hsplit, herase, hi₀, hsq]
    linarith
  have hlam : |θ₀ / (2 * Real.sqrt M)| * Sandpile.lInfNorm ℓ' = θ₀ / 2 := by
    rw [hinf, abs_of_pos (by positivity)]
    field_simp
  have hlt : |θ₀ / (2 * Real.sqrt M)| * Sandpile.lInfNorm ℓ' < θ₀ := by
    rw [hlam]; linarith
  obtain ⟨hI, hB⟩ := hC N ν hprob hint hexp F hF ℓ' hℓ'nn hne hlip'
    (θ₀ / (2 * Real.sqrt M)) hlt
  refine ⟨hI, le_trans hB (Real.exp_le_exp.2 ?_)⟩
  rw [hlam, show θ₀ - θ₀ / 2 = θ₀ / 2 by ring]
  have hprod : (θ₀ / (2 * Real.sqrt M)) ^ 2 * Sandpile.lTwoNorm ℓ' ^ 2 ≤ θ₀ ^ 2 / 2 := by
    have h1 : (θ₀ / (2 * Real.sqrt M)) ^ 2 = θ₀ ^ 2 / (4 * M) := by
      rw [div_pow, mul_pow, hsq]; ring_nf
    rw [h1]
    have h2 : (0 : ℝ) < 4 * M := by linarith
    calc θ₀ ^ 2 / (4 * M) * Sandpile.lTwoNorm ℓ' ^ 2
        ≤ θ₀ ^ 2 / (4 * M) * (2 * M) :=
          mul_le_mul_of_nonneg_left htwo (by positivity)
      _ = θ₀ ^ 2 / 2 := by field_simp; ring
  have hnn : (0 : ℝ) ≤ (θ₀ / (2 * Real.sqrt M)) ^ 2 * Sandpile.lTwoNorm ℓ' ^ 2 := by positivity
  calc C (θ₀ / 2) * (θ₀ / (2 * Real.sqrt M)) ^ 2 * Sandpile.lTwoNorm ℓ' ^ 2
      = C (θ₀ / 2) * ((θ₀ / (2 * Real.sqrt M)) ^ 2 * Sandpile.lTwoNorm ℓ' ^ 2) := by ring
    _ ≤ |C (θ₀ / 2)| * ((θ₀ / (2 * Real.sqrt M)) ^ 2 * Sandpile.lTwoNorm ℓ' ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hnn
    _ ≤ |C (θ₀ / 2)| * (θ₀ ^ 2 / 2) := mul_le_mul_of_nonneg_left hprod (abs_nonneg _)

/-- **The uniform exponential moment of the centred rescaled odometer.**
`sandpile.tex:1995-2006`: the Green weights of `𝒰_R(1,0)` have square sum
bounded uniformly in `R`, so `lem:weighted-exp-conc` gives one `θ > 0` and one
bound for `E e^{θ(𝒰_R(1,0) - E𝒰_R(1,0))}` valid for every `R ≥ 1`. -/
theorem exists_uniform_mgf_rescaled (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ θ A : ℝ, 0 < θ ∧ 0 < A ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ R : ℝ, 1 ≤ R →
          Integrable (fun ζ => Real.exp (θ *
              (R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometerOf ζ ⌊R ^ 2⌋₊ 0 -
                ∫ η, R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometerOf η ⌊R ^ 2⌋₊ 0
                  ∂(LatticeProb.iidLaw d ν))))
              (LatticeProb.iidLaw d ν) ∧
            (∫ ζ, Real.exp (θ *
              (R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometerOf ζ ⌊R ^ 2⌋₊ 0 -
                ∫ η, R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometerOf η ⌊R ^ 2⌋₊ 0
                  ∂(LatticeProb.iidLaw d ν)))
              ∂(LatticeProb.iidLaw d ν)) ≤ A := by
  classical
  obtain ⟨M, hM, hMb⟩ := exists_scaled_greenTime_norm_bounds d hd hd3
  obtain ⟨A, hA, hmgf⟩ := exists_mgf_of_square_sum θ₀ K₀ hθ₀ M hM
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hs0 : (0 : ℝ) < Real.sqrt M := Real.sqrt_pos.2 hM0
  refine ⟨θ₀ / (2 * Real.sqrt M), A, by positivity, hA, ?_⟩
  intro ν hprob hint hexp R hR
  haveI := hprob
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  set t : ℕ := ⌊R ^ 2⌋₊ with ht
  set a : ℝ := R ^ (-(2 - (d : ℝ) / 2)) with ha
  have hann : (0 : ℝ) ≤ a := (rescale_factor_pos d R hR0).le
  set N : ℕ := (Sandpile.boxFinset (0 : Sandpile.Site d) t).card with hN
  obtain ⟨i₀, _hi₀⟩ := exists_siteEnum_eq (Sandpile.boxFinset (0 : Sandpile.Site d) t)
    (Sandpile.mem_boxFinset (x := (0 : Sandpile.Site d)) (y := (0 : Sandpile.Site d)) (r := t)
      (by rw [Sandpile.boxDist_self]; exact Nat.zero_le t))
  set F : (Fin N → ℝ) → ℝ := fun ξ => a * Sandpile.boxOdometer t 0 ξ with hF
  set ℓ : Fin N → ℝ := fun i => a * Sandpile.greenTime d t 0 (Sandpile.boxEnum 0 t i) with hℓ
  have hFmeas : Measurable F := (Sandpile.measurable_boxOdometer t 0).const_mul a
  have hℓnn : ∀ i, 0 ≤ ℓ i := fun i => mul_nonneg hann (Sandpile.greenTime_nonneg _ _ _)
  have hsum : ∑ i, ℓ i ^ 2 ≤ M := by
    have hsumbox : ∑ i : Fin N, ℓ i ^ 2
        = ∑ z ∈ Sandpile.boxFinset (0 : Sandpile.Site d) t,
            (a * Sandpile.greenTime d t 0 z) ^ 2 :=
      Sandpile.sum_boxEnum (0 : Sandpile.Site d) t
        (fun z => (a * Sandpile.greenTime d t 0 z) ^ 2)
    have htsum : (∑' z : Sandpile.Site d, (a * Sandpile.greenTime d t 0 z) ^ 2)
        = ∑ z ∈ Sandpile.boxFinset (0 : Sandpile.Site d) t,
            (a * Sandpile.greenTime d t 0 z) ^ 2 := by
      refine tsum_eq_sum fun z hz => ?_
      have hg : Sandpile.greenTime d t 0 z = 0 := by
        by_contra hne
        exact hz (Sandpile.mem_boxFinset (Sandpile.greenTime_support t 0 hne))
      simp [hg]
    rw [hsumbox, ← htsum]
    exact hMb R hR |>.1
  have hlip : ∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
      |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y| := by
    intro ξ i y
    have hstep := Sandpile.abs_boxOdometer_update_le t (0 : Sandpile.Site d) ξ i y
    have : |F ξ - F (Function.update ξ i y)|
        = a * |Sandpile.boxOdometer t 0 ξ - Sandpile.boxOdometer t 0 (Function.update ξ i y)| := by
      rw [hF]
      rw [← mul_sub, abs_mul, abs_of_nonneg hann]
    rw [this, hℓ]
    calc a * |Sandpile.boxOdometer t 0 ξ - Sandpile.boxOdometer t 0 (Function.update ξ i y)|
        ≤ a * (Sandpile.greenTime d t 0 (Sandpile.boxEnum 0 t i) * |ξ i - y|) :=
          mul_le_mul_of_nonneg_left hstep hann
      _ = a * Sandpile.greenTime d t 0 (Sandpile.boxEnum 0 t i) * |ξ i - y| := by ring
  obtain ⟨hI, hB⟩ := hmgf N i₀ ν hprob hint hexp F hFmeas ℓ hℓnn hsum hlip
  -- transfer from the box coordinates to the i.i.d. law
  have hmp := LatticeProb.measurePreserving_pick _ ν (Sandpile.boxEnum (0 : Sandpile.Site d) t)
    (Sandpile.boxEnum_injective (0 : Sandpile.Site d) t)
  have hmean : (∫ η, F η ∂(Measure.pi fun _ : Fin N => ν))
      = ∫ η, a * Sandpile.odometerOf η t 0 ∂(LatticeProb.iidLaw d ν) := by
    rw [← Sandpile.integral_pick ν (Sandpile.boxEnum (0 : Sandpile.Site d) t)
      (Sandpile.boxEnum_injective (0 : Sandpile.Site d) t) F hFmeas.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ζ => by
      rw [hF]; exact congrArg (fun s => a * s) (Sandpile.boxOdometer_pick t 0 ζ))
  set c : ℝ := ∫ η, a * Sandpile.odometerOf η t 0 ∂(LatticeProb.iidLaw d ν) with hc
  set G : ℝ → ℝ := fun s => Real.exp (θ₀ / (2 * Real.sqrt M) * (s - c)) with hG
  have hGmeas : Measurable G := (measurable_const.mul (measurable_id.sub measurable_const)).exp
  have hcomp : ∀ ζ : Sandpile.Site d → ℝ,
      F (fun i => ζ (Sandpile.boxEnum 0 t i)) = a * Sandpile.odometerOf ζ t 0 := by
    intro ζ
    rw [hF]
    exact congrArg (fun s => a * s) (Sandpile.boxOdometer_pick t 0 ζ)
  have hpickm : AEMeasurable
      (fun ζ : Sandpile.Site d → ℝ => fun i => ζ (Sandpile.boxEnum 0 t i))
      (LatticeProb.iidLaw d ν) :=
    (measurable_pi_lambda _ fun i =>
      measurable_pi_apply (Sandpile.boxEnum (0 : Sandpile.Site d) t i)).aemeasurable
  have hIm : Integrable (fun ξ => G (F ξ)) (Measure.pi fun _ : Fin N => ν) := by
    simpa [hG, hmean, hc] using hI
  have hiff := integrable_map_measure
    (μ := LatticeProb.iidLaw d ν) (g := fun ξ : Fin N → ℝ => G (F ξ))
    (f := fun ζ : Sandpile.Site d → ℝ => fun i => ζ (Sandpile.boxEnum 0 t i))
    (by rw [hmp.map_eq]; exact (hGmeas.comp hFmeas).aestronglyMeasurable) hpickm
  have hInt : Integrable (fun ζ : Sandpile.Site d → ℝ =>
      G (a * Sandpile.odometerOf ζ t 0)) (LatticeProb.iidLaw d ν) := by
    have := hiff.1 (by rw [hmp.map_eq]; exact hIm)
    refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [Function.comp_apply]
    rw [hcomp ζ]
  have hInteg : (∫ ζ, G (a * Sandpile.odometerOf ζ t 0) ∂(LatticeProb.iidLaw d ν))
      = ∫ ξ, G (F ξ) ∂(Measure.pi fun _ : Fin N => ν) := by
    rw [← Sandpile.integral_pick ν (Sandpile.boxEnum (0 : Sandpile.Site d) t)
      (Sandpile.boxEnum_injective (0 : Sandpile.Site d) t) (fun ξ => G (F ξ))
      (hGmeas.comp hFmeas).aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ζ => congrArg G (hcomp ζ).symm)
  have hGeq : ∀ ζ : Sandpile.Site d → ℝ,
      G (a * Sandpile.odometerOf ζ t 0)
        = Real.exp (θ₀ / (2 * Real.sqrt M) *
            (a * Sandpile.odometerOf ζ t 0 -
              ∫ η, a * Sandpile.odometerOf η t 0 ∂(LatticeProb.iidLaw d ν))) := fun ζ => rfl
  refine ⟨?_, ?_⟩
  · simpa only [hGeq] using hInt
  · have hbound : (∫ ξ, G (F ξ) ∂(Measure.pi fun _ : Fin N => ν)) ≤ A := by
      simpa [hG, hmean, hc] using hB
    simpa only [hGeq] using hInteg.trans_le hbound

/-- A functional of the odometer has the same integral in the mass language of
the theorems and in the scenery language of the estimates. -/
theorem integral_comp_odometer_eq (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (t : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ σ, f (Sandpile.odometer σ t 0) ∂(Sandpile.centeredMassLaw d ν)
      = ∫ ζ, f (Sandpile.odometerOf ζ t 0) ∂(LatticeProb.iidLaw d ν) := by
  have h1 : ∫ σ, f (Sandpile.odometer σ t 0) ∂(Sandpile.centeredMassLaw d ν)
      = ∫ σ, f (Sandpile.odometerOf (Sandpile.scenery d σ) t 0)
          ∂(Sandpile.centeredMassLaw d ν) :=
    integral_congr_ae (Filter.Eventually.of_forall fun σ =>
      congrArg f (congrFun (Sandpile.odometer_eq_odometerOf σ t) 0))
  have h2 : ∫ σ, f (Sandpile.odometerOf (Sandpile.scenery d σ) t 0)
        ∂(Sandpile.centeredMassLaw d ν)
      = ∫ ζ, f (Sandpile.odometerOf ζ t 0)
          ∂((Sandpile.centeredMassLaw d ν).map (Sandpile.scenery d)) :=
    (integral_map (μ := Sandpile.centeredMassLaw d ν)
      (Sandpile.measurable_scenery d).aemeasurable
      (hf.comp (Sandpile.measurable_odometerOf t 0)).aestronglyMeasurable).symm
  rw [h1, h2, Sandpile.map_scenery_centeredMassLaw d ν hd]

/-- The same transfer for integrability. -/
theorem integrable_comp_odometer_of (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (t : ℕ) (f : ℝ → ℝ) (hf : Measurable f)
    (h : Integrable (fun ζ => f (Sandpile.odometerOf ζ t 0)) (LatticeProb.iidLaw d ν)) :
    Integrable (fun σ => f (Sandpile.odometer σ t 0)) (Sandpile.centeredMassLaw d ν) := by
  have hmap : (Sandpile.centeredMassLaw d ν).map (Sandpile.scenery d)
      = LatticeProb.iidLaw d ν := Sandpile.map_scenery_centeredMassLaw d ν hd
  have hiff := integrable_map_measure
    (μ := Sandpile.centeredMassLaw d ν)
    (g := fun ζ : Sandpile.Site d → ℝ => f (Sandpile.odometerOf ζ t 0))
    (f := Sandpile.scenery (d := d))
    (by rw [hmap]; exact (hf.comp (Sandpile.measurable_odometerOf t 0)).aestronglyMeasurable)
    (Sandpile.measurable_scenery d).aemeasurable
  have := hiff.1 (by rw [hmap]; exact h)
  refine this.congr (Filter.Eventually.of_forall fun σ => ?_)
  simp only [Function.comp_apply]
  exact congrArg f (congrFun (Sandpile.odometer_eq_odometerOf σ t) 0).symm

/-- **The uniform exponential moment of the centred rescaled odometer in the
mass language of the theorems.**  `sandpile.tex:2007`. -/
theorem exists_uniform_mgf_rescaled_mass (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ θ A : ℝ, 0 < θ ∧ 0 < A ∧
      ∀ ν : Measure ℝ, ∀ _ : IsProbabilityMeasure ν,
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ R : ℝ, 1 ≤ R →
          Integrable (fun σ => Real.exp (θ *
              (R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊R ^ 2⌋₊ 0 -
                ∫ τ, R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer τ ⌊R ^ 2⌋₊ 0
                  ∂(Sandpile.centeredMassLaw d ν))))
              (Sandpile.centeredMassLaw d ν) ∧
            (∫ σ, Real.exp (θ *
              (R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊R ^ 2⌋₊ 0 -
                ∫ τ, R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer τ ⌊R ^ 2⌋₊ 0
                  ∂(Sandpile.centeredMassLaw d ν)))
              ∂(Sandpile.centeredMassLaw d ν)) ≤ A := by
  obtain ⟨θ, A, hθ, hA, hmain⟩ := exists_uniform_mgf_rescaled d hd hd3 θ₀ K₀ hθ₀
  refine ⟨θ, A, hθ, hA, ?_⟩
  intro ν hprob hint hexp R hR
  haveI := hprob
  set a : ℝ := R ^ (-(2 - (d : ℝ) / 2)) with ha
  have hmean : (∫ τ, a * Sandpile.odometer τ ⌊R ^ 2⌋₊ 0 ∂(Sandpile.centeredMassLaw d ν))
      = ∫ η, a * Sandpile.odometerOf η ⌊R ^ 2⌋₊ 0 ∂(LatticeProb.iidLaw d ν) :=
    integral_comp_odometer_eq d ν hd ⌊R ^ 2⌋₊ (fun s => a * s) (measurable_const.mul measurable_id)
  obtain ⟨hI, hB⟩ := hmain ν hprob hint hexp R hR
  set c : ℝ := ∫ η, a * Sandpile.odometerOf η ⌊R ^ 2⌋₊ 0 ∂(LatticeProb.iidLaw d ν) with hc
  set G : ℝ → ℝ := fun s => Real.exp (θ * (a * s - c)) with hG
  have hGmeas : Measurable G :=
    (measurable_const.mul ((measurable_const.mul measurable_id).sub measurable_const)).exp
  have hIscen : Integrable (fun ζ => G (Sandpile.odometerOf ζ ⌊R ^ 2⌋₊ 0))
      (LatticeProb.iidLaw d ν) := hI
  have hImass : Integrable (fun σ => G (Sandpile.odometer σ ⌊R ^ 2⌋₊ 0))
      (Sandpile.centeredMassLaw d ν) :=
    integrable_comp_odometer_of d ν hd ⌊R ^ 2⌋₊ G hGmeas hIscen
  have hEq : (∫ σ, G (Sandpile.odometer σ ⌊R ^ 2⌋₊ 0) ∂(Sandpile.centeredMassLaw d ν))
      = ∫ ζ, G (Sandpile.odometerOf ζ ⌊R ^ 2⌋₊ 0) ∂(LatticeProb.iidLaw d ν) :=
    integral_comp_odometer_eq d ν hd ⌊R ^ 2⌋₊ G hGmeas
  rw [hmean]
  exact ⟨hImass, by rw [hEq]; exact hB⟩

end Sandpile.Support
