/-
The tightness clause of `prop:d4-superdiffusive-limit` (`sandpile.tex:3324-3327`).

The clause asks for a single level `M` above which the `H^{-s}(D)` norm of the
`\omega`-representative of the rescaled centred odometer is unlikely, uniformly
over every `R\geq1`.  Above a threshold `R_0` the decomposition
`u_{t_R}-\E u_{t_R}(0)=V_{t_R}+P^{n_R}E_{t_R-n_R}+(S_R-\E S_R(0))` splits the
norm into three, Step 1 supplies a tightness level for the membrane and Steps 2
and 3 make the two error norms exceed one with small probability.  Below `R_0`
the whole field is bounded crudely by its uniform second moment.
-/
import Sandpile.Support.D4STightSmall
import Sandpile.Support.D4SAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum Sandpile.D4Super

/-- **A three-way union bound at three levels.**  If `N ≤ N₁+N₂+N₃` pointwise
and the three levels add up to at most `M`, then `N` exceeds `M` only when one
of the three pieces exceeds its own level. -/
theorem measure_gt_le_add3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N N₁ N₂ N₃ : Ω → ℝ≥0∞) (h : ∀ ω : Ω, N ω ≤ N₁ ω + N₂ ω + N₃ ω)
    (M M₁ M₂ M₃ : ℝ≥0∞) (hM : M₁ + M₂ + M₃ ≤ M) :
    P {ω | M < N ω} ≤
      P {ω | M₁ < N₁ ω} + P {ω | M₂ < N₂ ω} + P {ω | M₃ < N₃ ω} := by
  have hsub : {ω | M < N ω} ⊆
      {ω | M₁ < N₁ ω} ∪ ({ω | M₂ < N₂ ω} ∪ {ω | M₃ < N₃ ω}) := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hc
    have hsum : N ω ≤ M₁ + M₂ + M₃ :=
      le_trans (h ω) (add_le_add (add_le_add hc.1 hc.2.1) hc.2.2)
    exact absurd hω (not_lt.mpr (le_trans hsum hM))
  calc P {ω | M < N ω}
      ≤ P ({ω | M₁ < N₁ ω} ∪ ({ω | M₂ < N₂ ω} ∪ {ω | M₃ < N₃ ω})) := measure_mono hsub
    _ ≤ P {ω | M₁ < N₁ ω} + P ({ω | M₂ < N₂ ω} ∪ {ω | M₃ < N₃ ω}) := measure_union_le _ _
    _ ≤ P {ω | M₁ < N₁ ω} + (P {ω | M₂ < N₂ ω} + P {ω | M₃ < N₃ ω}) :=
        add_le_add (le_refl _) (measure_union_le _ _)
    _ = P {ω | M₁ < N₁ ω} + P {ω | M₂ < N₂ ω} + P {ω | M₃ < N₃ ω} := (add_assoc _ _ _).symm

/-- **The tightness clause of `prop:d4-superdiffusive-limit`.** -/
theorem d4_superdiffusive_tightness (hHK : External.HeatKernelBounds)
    (hVS : External.VarianceScale) (hMembrane : External.MembraneScalingLimitFour)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hintν : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν)
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    {D : Set (Space 4)} (hD : IsDomain D) {w : Space 4 → ℝ} (hw : IsAveragingDensity D w)
    {α : ℝ} (hα : 2 < α) {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
      centeredMassLaw 4 ν {σ | M < negSobolevNorm 4 s D (omegaRep D w (latticePairing R
        (fun x => odometer σ ⌊R ^ α⌋₊ x - meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))}
        ≤ ENNReal.ofReal ε := by
  classical
  haveI := hprob
  obtain ⟨Lw, hLw0, hLw⟩ := exists_radius_of_isDomain hD
  obtain ⟨-, htight1⟩ := d4_superdiffusive_step1 hHK hMembrane ν hprob hmean hvar hvar'
    D hD w hw s hs hα
  obtain ⟨M₁, hM₁top, hM₁⟩ := htight1 (ε / 4) (by positivity)
  have hstep2 := tendsto_step2_four hHK hVS ν hmean θ hθ hexp hD hw hα hs
    (show (0:ℝ) < 1 by norm_num)
  have hstep3 := tendsto_step3_four hVS ν hprob hmean hvar hvar' θ hθ hexp hintν hpos
    hD hw hα hs (show (0:ℝ) < 1 by norm_num)
  have h2e := ENNReal.tendsto_nhds_zero.mp hstep2 (ENNReal.ofReal (ε / 4))
    (ENNReal.ofReal_pos.mpr (by positivity))
  have h3e := ENNReal.tendsto_nhds_zero.mp hstep3 (ENNReal.ofReal (ε / 4))
    (ENNReal.ofReal_pos.mpr (by positivity))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp
    (h2e.and (h3e.and ((eventually_step2_scales α hα).and (eventually_ge_atTop (1:ℝ)))))
  obtain ⟨Ms, hMs0, hMs⟩ := exists_tight_bound_small ν hsq hs.le hD hw
    (show (0:ℝ) ≤ α by linarith) (max R₀ 1) (le_max_right _ _) hε
  refine ⟨max (ENNReal.ofReal Ms) (M₁ + 2), ?_, ?_⟩
  · refine (max_lt ENNReal.ofReal_lt_top ?_).ne
    exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hM₁top, ENNReal.ofNat_lt_top⟩
  intro R hR1
  have hmn : meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊
      = ∫ η, odometerOf η ⌊R ^ α⌋₊ 0 ∂(LatticeProb.iidLaw 4 ν) :=
    meanOdometer_centeredMassLaw_eq 4 ν (by norm_num) ⌊R ^ α⌋₊
  have hmapped : ∀ A : Set (Site 4 → ℝ),
      centeredMassLaw 4 ν (scenery 4 ⁻¹' A) ≤ LatticeProb.iidLaw 4 ν A := by
    intro A
    have h := MeasureTheory.Measure.le_map_apply (μ := centeredMassLaw 4 ν)
      (measurable_scenery 4).aemeasurable A
    rwa [map_scenery_centeredMassLaw 4 ν (by norm_num)] at h
  rcases le_or_gt R (max R₀ 1) with hsmall | hbig
  · -- Below the threshold the whole field is bounded by its uniform second moment.
    have hsub : {σ : Site 4 → ℝ | max (ENNReal.ofReal Ms) (M₁ + 2) < negSobolevNorm 4 s D
          (omegaRep D w (latticePairing R (fun x => odometer σ ⌊R ^ α⌋₊ x -
            meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))}
        ⊆ {σ : Site 4 → ℝ | ENNReal.ofReal Ms < negSobolevNorm 4 s D
          (omegaRep D w (latticePairing R (fun x => odometer σ ⌊R ^ α⌋₊ x -
            meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))} :=
      by
        intro σ hσ
        simp only [Set.mem_setOf_eq] at hσ ⊢
        exact lt_of_le_of_lt (le_max_left _ _) hσ
    have hset : {σ : Site 4 → ℝ | ENNReal.ofReal Ms < negSobolevNorm 4 s D
          (omegaRep D w (latticePairing R (fun x => odometer σ ⌊R ^ α⌋₊ x -
            meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))}
        = scenery 4 ⁻¹' {ζ : Site 4 → ℝ | ENNReal.ofReal Ms < negSobolevNorm 4 s D
          (omegaRep D w (latticePairing R (fun x => odometerOf ζ ⌊R ^ α⌋₊ x -
            ∫ η, odometerOf η ⌊R ^ α⌋₊ 0 ∂(LatticeProb.iidLaw 4 ν))))} := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [hmn]
      have hfun : (fun x : Site 4 => odometer σ ⌊R ^ α⌋₊ x -
          ∫ η, odometerOf η ⌊R ^ α⌋₊ 0 ∂(LatticeProb.iidLaw 4 ν))
          = fun x => odometerOf (scenery 4 σ) ⌊R ^ α⌋₊ x -
            ∫ η, odometerOf η ⌊R ^ α⌋₊ 0 ∂(LatticeProb.iidLaw 4 ν) := by
        funext x
        rw [congrFun (odometer_eq_odometerOf σ ⌊R ^ α⌋₊) x]
      rw [hfun]
    refine le_trans (measure_mono hsub) ?_
    rw [hset]
    exact le_trans (hmapped _) (hMs R hR1 hsmall)
  · -- Above the threshold the decomposition splits the norm into three.
    have hRge : R₀ ≤ R := le_trans (le_max_left _ _) hbig.le
    obtain ⟨h2R, h3R, hsc, -⟩ := hR₀ R hRge
    obtain ⟨-, -, hnt, -⟩ := hsc
    have hshiftT : ∀ φ : Space 4 → ℝ, IsTestFn D φ →
        Integrable (omegaShift D w φ) ∧ (∀ z : Space 4, omegaShift D w φ z ≠ 0 → ‖z‖ ≤ Lw) := by
      intro φ hφ
      have hshift : IsTestFn (Set.univ : Set (Space 4)) (omegaShift D w φ) :=
        isTestFn_univ_omegaShift hw.1 hφ
      exact ⟨hshift.1.continuous.integrable_of_hasCompactSupport hshift.2.1,
        omegaShift_support hw.1 hφ hLw⟩
    have hnorm : ∀ σ : Site 4 → ℝ,
        negSobolevNorm 4 s D (omegaRep D w (latticePairing R
            (fun x => odometer σ ⌊R ^ α⌋₊ x - meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))
          ≤ negSobolevNorm 4 s D (omegaRep D w (latticePairing R
              (membrane (scenery 4 σ) ⌊R ^ α⌋₊)))
            + negSobolevNorm 4 s D (omegaRep D w (latticePairing R
              (smoothedError ν α R (scenery 4 σ))))
            + negSobolevNorm 4 s D (omegaRep D w (latticePairing R
              (windowField ν α R (scenery 4 σ)))) := by
      intro σ
      have hdec : (fun x : Site 4 => odometer σ ⌊R ^ α⌋₊ x -
          meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)
          = fun x => membrane (scenery 4 σ) ⌊R ^ α⌋₊ x
            + (smoothedError ν α R (scenery 4 σ) x + windowField ν α R (scenery 4 σ) x) := by
        funext x
        rw [congrFun (odometer_eq_odometerOf σ ⌊R ^ α⌋₊) x, hmn]
        linarith [d4_field_decomposition ν hintν hmean hpos α R hnt (scenery 4 σ) x]
      rw [hdec]
      have h1 : negSobolevNorm 4 s D (omegaRep D w (latticePairing R
            (fun x => membrane (scenery 4 σ) ⌊R ^ α⌋₊ x
              + (smoothedError ν α R (scenery 4 σ) x + windowField ν α R (scenery 4 σ) x))))
          ≤ negSobolevNorm 4 s D (omegaRep D w (latticePairing R
              (membrane (scenery 4 σ) ⌊R ^ α⌋₊)))
            + negSobolevNorm 4 s D (omegaRep D w (latticePairing R
              (fun x => smoothedError ν α R (scenery 4 σ) x
                + windowField ν α R (scenery 4 σ) x))) := by
        refine negSobolevNorm_le_add s D _ _ _ ?_
        intro φ hφ
        obtain ⟨hintψ, hsuppψ⟩ := hshiftT φ hφ
        have heq : omegaRep D w (latticePairing R
            (fun x => membrane (scenery 4 σ) ⌊R ^ α⌋₊ x
              + (smoothedError ν α R (scenery 4 σ) x
                + windowField ν α R (scenery 4 σ) x))) φ
            = omegaRep D w (latticePairing R (membrane (scenery 4 σ) ⌊R ^ α⌋₊)) φ
              + omegaRep D w (latticePairing R
                (fun x => smoothedError ν α R (scenery 4 σ) x
                  + windowField ν α R (scenery 4 σ) x)) φ :=
          latticePairing_add R (membrane (scenery 4 σ) ⌊R ^ α⌋₊)
            (fun x => smoothedError ν α R (scenery 4 σ) x
              + windowField ν α R (scenery 4 σ) x) (omegaShift D w φ) hintψ hsuppψ
        rw [heq]
        exact abs_add_le _ _
      have h2 : negSobolevNorm 4 s D (omegaRep D w (latticePairing R
            (fun x => smoothedError ν α R (scenery 4 σ) x
              + windowField ν α R (scenery 4 σ) x)))
          ≤ negSobolevNorm 4 s D (omegaRep D w (latticePairing R
              (smoothedError ν α R (scenery 4 σ))))
            + negSobolevNorm 4 s D (omegaRep D w (latticePairing R
              (windowField ν α R (scenery 4 σ)))) := by
        refine negSobolevNorm_le_add s D _ _ _ ?_
        intro φ hφ
        obtain ⟨hintψ, hsuppψ⟩ := hshiftT φ hφ
        have heq : omegaRep D w (latticePairing R
            (fun x => smoothedError ν α R (scenery 4 σ) x
              + windowField ν α R (scenery 4 σ) x)) φ
            = omegaRep D w (latticePairing R (smoothedError ν α R (scenery 4 σ))) φ
              + omegaRep D w (latticePairing R (windowField ν α R (scenery 4 σ))) φ :=
          latticePairing_add R (smoothedError ν α R (scenery 4 σ))
            (windowField ν α R (scenery 4 σ)) (omegaShift D w φ) hintψ hsuppψ
        rw [heq]
        exact abs_add_le _ _
      calc negSobolevNorm 4 s D (omegaRep D w (latticePairing R
              (fun x => membrane (scenery 4 σ) ⌊R ^ α⌋₊ x
                + (smoothedError ν α R (scenery 4 σ) x
                  + windowField ν α R (scenery 4 σ) x))))
          ≤ _ := h1
        _ ≤ negSobolevNorm 4 s D (omegaRep D w (latticePairing R
              (membrane (scenery 4 σ) ⌊R ^ α⌋₊)))
            + (negSobolevNorm 4 s D (omegaRep D w (latticePairing R
                (smoothedError ν α R (scenery 4 σ))))
              + negSobolevNorm 4 s D (omegaRep D w (latticePairing R
                (windowField ν α R (scenery 4 σ))))) := add_le_add (le_refl _) h2
        _ = _ := (add_assoc _ _ _).symm
    have hlev : M₁ + ENNReal.ofReal 1 + ENNReal.ofReal 1
        ≤ max (ENNReal.ofReal Ms) (M₁ + 2) := by
      rw [ENNReal.ofReal_one, add_assoc, show (1:ℝ≥0∞) + 1 = 2 by norm_num]
      exact le_max_right _ _
    have hkey := measure_gt_le_add3 (centeredMassLaw 4 ν)
      (fun σ => negSobolevNorm 4 s D (omegaRep D w (latticePairing R
        (fun x => odometer σ ⌊R ^ α⌋₊ x - meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊))))
      (fun σ => negSobolevNorm 4 s D (omegaRep D w (latticePairing R
        (membrane (scenery 4 σ) ⌊R ^ α⌋₊))))
      (fun σ => negSobolevNorm 4 s D (omegaRep D w (latticePairing R
        (smoothedError ν α R (scenery 4 σ)))))
      (fun σ => negSobolevNorm 4 s D (omegaRep D w (latticePairing R
        (windowField ν α R (scenery 4 σ)))))
      hnorm (max (ENNReal.ofReal Ms) (M₁ + 2)) M₁ (ENNReal.ofReal 1) (ENNReal.ofReal 1) hlev
    have hb1 := hM₁ R hR1
    have hb2 : centeredMassLaw 4 ν {σ : Site 4 → ℝ | ENNReal.ofReal 1 < negSobolevNorm 4 s D
        (omegaRep D w (latticePairing R (smoothedError ν α R (scenery 4 σ))))}
        ≤ ENNReal.ofReal (ε / 4) := le_trans (hmapped _) h2R
    have hb3 : centeredMassLaw 4 ν {σ : Site 4 → ℝ | ENNReal.ofReal 1 < negSobolevNorm 4 s D
        (omegaRep D w (latticePairing R (windowField ν α R (scenery 4 σ))))}
        ≤ ENNReal.ofReal (ε / 4) := le_trans (hmapped _) h3R
    have hsum : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)
        ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    exact le_trans hkey (le_trans (add_le_add (add_le_add hb1 hb2) hb3) hsum)

end Sandpile.Support
