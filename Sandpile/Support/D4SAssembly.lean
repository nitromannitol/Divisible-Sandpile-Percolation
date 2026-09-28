import Sandpile.Support.D4SStepsPairing
import Sandpile.Support.SceneryBridge
import Sandpile.Support.D4Step1

/-!
# Assembly of the dimension-four superdiffusive limit's first clause

The assembly of `prop:d4-superdiffusive-limit` (`sandpile.tex:3330-3340`,
`3405-3406`).

`u_{t_R}-\E u_{t_R}(0)` is `V_{t_R}+E_{t_R}`, and
`E_{t_R}=P^{n_R}E_{t_R-n_R}+(S_R-\E S_R(0))` by `eq:d4-proof-two-terms`.  Step 1
identifies the limit of the first summand and Steps 2 and 3 send the other two
to zero.  The pairing is linear in the field, so the three summands separate;
the scenery bridge carries the two error terms from the i.i.d.\ law of the
scenery to the mass law of the statement, through `le_map_apply`, which needs no
measurability of the events. `d4_field_decomposition` gives the pointwise decomposition of the
centered odometer into `membrane`, `smoothedError` and `windowField`; `tendsto_errors_massLaw`
uses the linearity `latticePairing_add`, the measurability `measurable_latticePairing`, and the
scenery-to-mass-law transport to show the two error terms vanish in probability under the mass
law; and `d4_superdiffusive_first_clause` combines this with Step 1's convergence in
distribution via `tendstoInMeasure_of_tendsto_abs` and Slutsky's theorem to prove the first
clause of `prop:d4-superdiffusive-limit`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

open Sandpile.Support Sandpile.Continuum Sandpile.D4Super

/-- **The decomposition of `eq:d4-superdiffusive-decomposition`** at one site:
the centred odometer is the membrane, the smoothed linearization error, and the
centred reflection window. -/
theorem d4_field_decomposition (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hintν : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν)
    (α R : ℝ) (hnt : ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ≤ ⌊R ^ α⌋₊)
    (ζ : Site 4 → ℝ) (x : Site 4) :
    odometerOf ζ ⌊R ^ α⌋₊ x - (∫ η, odometerOf η ⌊R ^ α⌋₊ 0 ∂(LatticeProb.iidLaw 4 ν))
      = membrane ζ ⌊R ^ α⌋₊ x + smoothedError ν α R ζ x + windowField ν α R ζ x := by
  have hdec := diffField_centered_decomp (d := 4) (by norm_num) ν hintν hmean hpos ζ
    ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ hnt x
  have hsm : smoothedError ν α R ζ x
      = (avg^[⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊]
          (diffField ζ (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊))) x
        - ∫ η, odometerOf η (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊) 0
            ∂(LatticeProb.iidLaw 4 ν) :=
    avg_iterate_linError ν _ _ ζ x
  have hx : ∫ η, reflectionSum η ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x
        ∂(LatticeProb.iidLaw 4 ν)
      = ∫ η, reflectionSum η ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ 0
        ∂(LatticeProb.iidLaw 4 ν) := by
    rw [integral_reflectionSum (d := 4) (by norm_num) ν hintν hmean hpos x _ _ hnt,
      integral_reflectionSum (d := 4) (by norm_num) ν hintν hmean hpos 0 _ _ hnt]
  have hwf : windowField ν α R ζ x
      = reflectionSum ζ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x
        - ∫ η, reflectionSum η ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ 0
            ∂(LatticeProb.iidLaw 4 ν) := rfl
  rw [hsm, hwf, ← hx]
  linarith [hdec]

/-- The pairing is additive in the field. -/
theorem latticePairing_add {d : ℕ} (R : ℝ) (f g : Sandpile.Site d → ℝ) (φ : Space d → ℝ)
    (hφ : Integrable φ) {L : ℝ} (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L) :
    latticePairing R (fun x => f x + g x) φ
      = latticePairing R f φ + latticePairing R g φ := by
  have h := latticePairing_sub R (fun x => f x + g x) g φ hφ hsupp
  have h2 : (fun x : Sandpile.Site d => (f x + g x) - g x) = f := by funext x; ring
  rw [h2] at h
  linarith [h]

/-- **The two error terms vanish in probability**, in the pairing with one test
function and under the mass law of the statement. -/
theorem tendsto_errors_massLaw (hHK : External.HeatKernelBounds) (hVS : External.VarianceScale)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hintν : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν)
    {D : Set (Space 4)} (hD : IsDomain D) {w : Space 4 → ℝ} (hw : IsAveragingDensity D w)
    {α : ℝ} (hα : 2 < α) {φ : Space 4 → ℝ} (hφ : IsTestFn D φ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => centeredMassLaw 4 ν
      {σ | ε ≤ |omegaRep D w (latticePairing R
        (fun x => smoothedError ν α R (scenery 4 σ) x
          + windowField ν α R (scenery 4 σ) x)) φ|}) atTop (𝓝 0) := by
  classical
  obtain ⟨Lw, hLw0, hLw⟩ := exists_radius_of_isDomain hD
  have hshift : IsTestFn (Set.univ : Set (Space 4)) (omegaShift D w φ) :=
    isTestFn_univ_omegaShift hw.1 hφ
  have hintψ : Integrable (omegaShift D w φ) :=
    hshift.1.continuous.integrable_of_hasCompactSupport hshift.2.1
  -- the pairing of the sum splits
  have hadd : ∀ (R : ℝ) (ζ : Site 4 → ℝ),
      omegaRep D w (latticePairing R
        (fun x => smoothedError ν α R ζ x + windowField ν α R ζ x)) φ
      = omegaRep D w (latticePairing R (smoothedError ν α R ζ)) φ
        + omegaRep D w (latticePairing R (windowField ν α R ζ)) φ := by
    intro R ζ
    exact latticePairing_add R (smoothedError ν α R ζ) (windowField ν α R ζ)
      (omegaShift D w φ) hintψ (omegaShift_support hw.1 hφ hLw)
  -- the event lies inside the union of the two events of Steps 2 and 3
  have hsub : ∀ (R : ℝ),
      {σ : Site 4 → ℝ | ε ≤ |omegaRep D w (latticePairing R
        (fun x => smoothedError ν α R (scenery 4 σ) x
          + windowField ν α R (scenery 4 σ) x)) φ|}
      ⊆ scenery 4 ⁻¹' ({ζ : Site 4 → ℝ | ENNReal.ofReal (ε / 3) < ENNReal.ofReal
            |omegaRep D w (latticePairing R (smoothedError ν α R ζ)) φ|}
          ∪ {ζ : Site 4 → ℝ | ENNReal.ofReal (ε / 3) < ENNReal.ofReal
            |omegaRep D w (latticePairing R (windowField ν α R ζ)) φ|}) := by
    intro R σ hσ
    rw [Set.mem_preimage, Set.mem_union]
    by_contra hc
    rw [not_or] at hc
    have h1 : |omegaRep D w (latticePairing R (smoothedError ν α R (scenery 4 σ))) φ|
        ≤ ε / 3 := by
      have hx : ¬ (ENNReal.ofReal (ε / 3) < ENNReal.ofReal
        |omegaRep D w (latticePairing R (smoothedError ν α R (scenery 4 σ))) φ|) := hc.1
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (not_lt.mp hx)
    have h2 : |omegaRep D w (latticePairing R (windowField ν α R (scenery 4 σ))) φ|
        ≤ ε / 3 := by
      have hx : ¬ (ENNReal.ofReal (ε / 3) < ENNReal.ofReal
        |omegaRep D w (latticePairing R (windowField ν α R (scenery 4 σ))) φ|) := hc.2
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (not_lt.mp hx)
    rw [Set.mem_setOf_eq, hadd R (scenery 4 σ)] at hσ
    have := abs_add_le (omegaRep D w (latticePairing R (smoothedError ν α R (scenery 4 σ))) φ)
      (omegaRep D w (latticePairing R (windowField ν α R (scenery 4 σ))) φ)
    linarith
  -- transport to the mass law
  have hmapped : ∀ (R : ℝ) (A : Set (Site 4 → ℝ)),
      centeredMassLaw 4 ν (scenery 4 ⁻¹' A) ≤ LatticeProb.iidLaw 4 ν A := by
    intro R A
    have h := MeasureTheory.Measure.le_map_apply (μ := centeredMassLaw 4 ν)
      (measurable_scenery 4).aemeasurable A
    rwa [map_scenery_centeredMassLaw 4 ν (by norm_num)] at h
  have hstep2 := tendsto_step2_pairing_four hHK hVS ν hmean θ hθ hexp hD hw hα hφ
    (show (0:ℝ) < ε / 3 by positivity)
  have hstep3 := tendsto_step3_pairing_four hVS ν inferInstance hmean hvar hvar' θ hθ hexp
    hintν hpos hD hw hα hφ (show (0:ℝ) < ε / 3 by positivity)
  have hsum : Tendsto (fun R : ℝ =>
      LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | ENNReal.ofReal (ε / 3) < ENNReal.ofReal
        |omegaRep D w (latticePairing R (smoothedError ν α R ζ)) φ|}
      + LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | ENNReal.ofReal (ε / 3) < ENNReal.ofReal
        |omegaRep D w (latticePairing R (windowField ν α R ζ)) φ|}) atTop (𝓝 0) := by
    simpa using hstep2.add hstep3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun R => by simp)
    (Filter.Eventually.of_forall fun R => ?_)
  refine le_trans (measure_mono (hsub R)) (le_trans (hmapped R _) ?_)
  exact measure_union_le _ _

/-- The pairing with a fixed test function is a measurable function of the
field, because over the cells of the mesh it is a finite sum. -/
theorem measurable_latticePairing {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (R : ℝ)
    (F : Ω → Sandpile.Site d → ℝ) (hF : ∀ x : Sandpile.Site d, Measurable (fun ω => F ω x))
    (ψ : Space d → ℝ) (hψ : Integrable ψ) (S : Finset (Sandpile.Site d))
    (hS : ∀ z : Space d, ψ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ S) :
    Measurable (fun ω => latticePairing R (F ω) ψ) := by
  have heq : (fun ω => latticePairing R (F ω) ψ)
      = fun ω => ∑ x ∈ S, F ω x * cellMass R ψ x := by
    funext ω
    exact latticePairing_eq_sum R (F ω) ψ hψ S hS
  rw [heq]
  exact Finset.measurable_sum _ fun x _ => (hF x).mul_const _

/-- Convergence in probability of a real family, in the `edist` form Mathlib's
Slutsky theorem consumes. -/
theorem tendstoInMeasure_of_tendsto_abs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℝ → Ω → ℝ)
    (h : ∀ r : ℝ, 0 < r → Tendsto (fun R : ℝ => P {ω | r ≤ |Y R ω|}) atTop (𝓝 0)) :
    TendstoInMeasure P Y atTop (fun _ => (0:ℝ)) := by
  intro ε hε
  rcases eq_or_ne ε ⊤ with htop | htop
  · have hempty : ∀ R : ℝ, {ω | ε ≤ edist (Y R ω) 0} = (∅ : Set Ω) := by
      intro R
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le, htop]
      rw [edist_dist]
      exact ENNReal.ofReal_lt_top
    simp only [hempty, measure_empty]
    exact tendsto_const_nhds
  · have hr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    have hset : ∀ R : ℝ, {ω | ε ≤ edist (Y R ω) 0} = {ω | ε.toReal ≤ |Y R ω|} := by
      intro R
      ext ω
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, edist_dist, Real.dist_eq, sub_zero,
        ENNReal.le_ofReal_iff_toReal_le htop (abs_nonneg _)]
    simp only [hset]
    exact h ε.toReal hr

/-- **The first clause of `prop:d4-superdiffusive-limit`**
(`sandpile.tex:3324-3327`): the `ω`-representative of the rescaled centred
odometer, paired with a test function, converges in distribution to the
corresponding Gaussian. -/
theorem d4_superdiffusive_first_clause (hHK : External.HeatKernelBounds)
    (hVS : External.VarianceScale) (hMembrane : External.MembraneScalingLimitFour)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hintν : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν)
    {D : Set (Space 4)} (hD : IsDomain D) {w : Space 4 → ℝ} (hw : IsAveragingDensity D w)
    {α : ℝ} (hα : 2 < α) {s : ℝ} (hs : 0 < s)
    {φ : Space 4 → ℝ} (hφ : IsTestFn D φ) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site 4 → ℝ) =>
        omegaRep D w (latticePairing R (fun x => odometer σ ⌊R ^ α⌋₊ x -
          meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)) φ)
      atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal
        (omegaMembraneCov4 D w (variance id ν) φ φ))) := by
  classical
  haveI := hprob
  obtain ⟨hstep1, -⟩ := d4_superdiffusive_step1 hHK hMembrane ν hprob hmean hvar hvar'
    D hD w hw s hs hα
  have hX := hstep1 φ hφ
  obtain ⟨Lw, hLw0, hLw⟩ := exists_radius_of_isDomain hD
  have hshift : IsTestFn (Set.univ : Set (Space 4)) (omegaShift D w φ) :=
    isTestFn_univ_omegaShift hw.1 hφ
  have hintψ : Integrable (omegaShift D w φ) :=
    hshift.1.continuous.integrable_of_hasCompactSupport hshift.2.1
  have hsuppψ := omegaShift_support hw.1 hφ hLw
  set Ffull : ℝ → (Site 4 → ℝ) → ℝ := fun R σ =>
    omegaRep D w (latticePairing R (fun x => odometer σ ⌊R ^ α⌋₊ x -
      meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)) φ with hFfull
  set Xmem : ℝ → (Site 4 → ℝ) → ℝ := fun R σ =>
    omegaRep D w (latticePairing R (membrane (scenery 4 σ) ⌊R ^ α⌋₊)) φ with hXmem
  set Yerr : ℝ → (Site 4 → ℝ) → ℝ := fun R σ => Ffull R σ - Xmem R σ with hYerr
  -- the error is measurable
  have hmeasY : ∀ R : ℝ, AEMeasurable (Yerr R) (centeredMassLaw 4 ν) := by
    intro R
    have hmem : ∀ z : Space 4, omegaShift D w φ z ≠ 0 →
        (fun i => ⌊R * z i⌋) ∈ Sandpile.boxFinset (0 : Site 4) (⌈|R| * Lw⌉₊ + 1) :=
      fun z hz => floor_mem_boxFinset R z (hsuppψ z hz)
    have h1 : Measurable (fun σ : Site 4 → ℝ => Ffull R σ) := by
      refine measurable_latticePairing R
        (fun σ x => odometer σ ⌊R ^ α⌋₊ x - meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)
        (fun x => ?_) (omegaShift D w φ) hintψ _ hmem
      have hc : (fun σ : Site 4 → ℝ => odometer σ ⌊R ^ α⌋₊ x -
          meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)
          = fun σ => odometerOf (scenery 4 σ) ⌊R ^ α⌋₊ x -
            meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊ := by
        funext σ
        rw [congrFun (odometer_eq_odometerOf σ ⌊R ^ α⌋₊) x]
      rw [hc]
      exact ((measurable_odometerOf ⌊R ^ α⌋₊ x).comp (measurable_scenery 4)).sub
        measurable_const
    have h2 : Measurable (fun σ : Site 4 → ℝ => Xmem R σ) :=
      measurable_latticePairing R (fun σ => membrane (scenery 4 σ) ⌊R ^ α⌋₊)
        (fun x => (measurable_membrane ⌊R ^ α⌋₊ x).comp (measurable_scenery 4))
        (omegaShift D w φ) hintψ _ hmem
    exact (h1.sub h2).aemeasurable
  -- the error vanishes in probability
  have htend : TendstoInMeasure (centeredMassLaw 4 ν) Yerr atTop (fun _ => (0:ℝ)) := by
    refine tendstoInMeasure_of_tendsto_abs _ Yerr (fun r hr => ?_)
    have hcong : ∀ᶠ R : ℝ in atTop,
        {σ : Site 4 → ℝ | r ≤ |Yerr R σ|}
          = {σ : Site 4 → ℝ | r ≤ |omegaRep D w (latticePairing R
              (fun x => smoothedError ν α R (scenery 4 σ) x
                + windowField ν α R (scenery 4 σ) x)) φ|} := by
      filter_upwards [eventually_step2_scales α hα] with R hRs
      obtain ⟨hR2, hn1, hnt, h3⟩ := hRs
      ext σ
      have hdecomp : ∀ x : Site 4,
          odometer σ ⌊R ^ α⌋₊ x - meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊
            = membrane (scenery 4 σ) ⌊R ^ α⌋₊ x
              + (smoothedError ν α R (scenery 4 σ) x
                + windowField ν α R (scenery 4 σ) x) := by
        intro x
        have hod : odometer σ ⌊R ^ α⌋₊ x = odometerOf (scenery 4 σ) ⌊R ^ α⌋₊ x :=
          congrFun (odometer_eq_odometerOf σ ⌊R ^ α⌋₊) x
        have hmn : meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊
            = ∫ η, odometerOf η ⌊R ^ α⌋₊ 0 ∂(LatticeProb.iidLaw 4 ν) :=
          meanOdometer_centeredMassLaw_eq 4 ν (by norm_num) _
        rw [hod, hmn]
        linarith [d4_field_decomposition ν hintν hmean hpos α R hnt (scenery 4 σ) x]
      have hsplit : Ffull R σ = Xmem R σ + omegaRep D w (latticePairing R
          (fun x => smoothedError ν α R (scenery 4 σ) x
            + windowField ν α R (scenery 4 σ) x)) φ := by
        rw [hFfull, hXmem]
        have hpt : (fun x : Site 4 => odometer σ ⌊R ^ α⌋₊ x -
            meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)
            = fun x => membrane (scenery 4 σ) ⌊R ^ α⌋₊ x
              + (smoothedError ν α R (scenery 4 σ) x
                + windowField ν α R (scenery 4 σ) x) := by
          funext x; exact hdecomp x
        show latticePairing R _ (omegaShift D w φ) = _
        rw [hpt]
        exact latticePairing_add R (membrane (scenery 4 σ) ⌊R ^ α⌋₊)
          (fun x => smoothedError ν α R (scenery 4 σ) x
            + windowField ν α R (scenery 4 σ) x) (omegaShift D w φ) hintψ hsuppψ
      have hY : Yerr R σ = omegaRep D w (latticePairing R
          (fun x => smoothedError ν α R (scenery 4 σ) x
            + windowField ν α R (scenery 4 σ) x)) φ := by
        rw [hYerr]; simp only []; rw [hsplit]; ring
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hY]
    refine Tendsto.congr' ?_ (tendsto_errors_massLaw hHK hVS ν hmean hvar hvar' θ hθ hexp
      hintν hpos hD hw hα hφ hr)
    filter_upwards [hcong] with R hR
    rw [hR]
  -- Slutsky
  have hslut := hX.add_of_tendstoInMeasure_const htend hmeasY
  refine TendstoInDistribution.congr (fun R => ?_) (Filter.Eventually.of_forall fun x => ?_) hslut
  · refine Filter.Eventually.of_forall fun σ => ?_
    show Xmem R σ + Yerr R σ = Ffull R σ
    rw [hYerr]; ring
  · show (id : ℝ → ℝ) x + (0:ℝ) = (id : ℝ → ℝ) x
    ring

end Sandpile
