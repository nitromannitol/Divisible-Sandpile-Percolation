import Sandpile.Support.TightWeightedMembrane
import Sandpile.Support.ContVarianceLimit
import Sandpile.Frozen.WeightedMembraneLimit

/-!
# Diffusive odometer limit from the linearization

The diffusive odometer limit of `thm:dgt4-diffusive-membrane` (`sandpile.tex:4616-4639`),
assembled from the linearization.

The paper's proof (`sandpile.tex:4639-4691`) is in two steps. `prop:dgt4-linearization` says that
the rescaled centred odometer and the time-weighted field with the weight `(1-j/n)^κ` differ by
a term whose second moment tends to zero; `prop:weighted-membrane-limit`, applied with
`q(r) = (1-r/T)^κ`, identifies the limit of the second as `ℋ_{κ,T}`. The theorem below is that
assembly, with the first step taken as a hypothesis: once `prop:dgt4-linearization` is proved the
frozen node follows by applying it.

The bridge between the two steps is that convergence in `L²` is convergence in measure, so a
family within `L²`-distance `o(1)` of a family converging in distribution converges to the same
law. The pairing with a test function is a FINITE linear combination of the values of the field,
over the cells of the mesh above the support of the test function, so it is square integrable as
soon as the values are, which for the odometer is `memLp_two_odometer` and for the weighted field
is `memLp_two_weightedField_mass`. Tightness is the odometer's own, `dgt4_odometer_tight`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}


/-- Convergence of the second moment to zero is convergence of the `L²` norm to
zero, which is what convergence in measure needs. -/
theorem tendsto_eLpNorm_of_tendsto_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : ℝ → Ω → ℝ) (hmeas : ∀ R, AEStronglyMeasurable (Z R) P)
    (hint : ∀ R, Integrable (fun ω => Z R ω ^ 2) P)
    (h : Tendsto (fun R : ℝ => ∫ ω, Z R ω ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => eLpNorm (Z R) 2 P) atTop (𝓝 0) := by
  have hmem : ∀ R : ℝ, MemLp (Z R) 2 P := fun R =>
    (memLp_two_iff_integrable_sq (hmeas R)).2 (hint R)
  have h2 : ((2 : ℝ≥0∞).toReal) = (2:ℝ) := by norm_num
  have heq : ∀ R : ℝ, eLpNorm (Z R) 2 P
      = ENNReal.ofReal ((∫ ω, Z R ω ^ 2 ∂P) ^ ((2:ℝ)⁻¹)) := by
    intro R
    rw [(hmem R).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), h2]
    congr 2
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ‖Z R ω‖ ^ (2:ℝ) = Z R ω ^ 2
    rw [Real.norm_eq_abs, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  simp only [heq]
  have h1 : Continuous (fun x : ℝ => x ^ ((2:ℝ)⁻¹)) := Real.continuous_rpow_const (by norm_num)
  have hcomp : Tendsto (fun x : ℝ => ENNReal.ofReal (x ^ ((2:ℝ)⁻¹))) (𝓝 0) (𝓝 0) := by
    have hcc : Continuous (fun x : ℝ => ENNReal.ofReal (x ^ ((2:ℝ)⁻¹))) :=
      ENNReal.continuous_ofReal.comp h1
    have := hcc.tendsto 0
    simpa using this
  exact hcomp.comp h


/-- The pairing of a field with a test function is a finite linear combination of
the values of the field, so it is square integrable when they are. -/
theorem memLp_two_latticePairing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℝ) (F : Ω → Sandpile.Site d → ℝ)
    (hF : ∀ x : Sandpile.Site d, MemLp (fun ω => F ω x) 2 P)
    (φ : Space d → ℝ) (hint : Integrable φ) {L : ℝ}
    (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L) :
    MemLp (fun ω => Sandpile.Continuum.latticePairing R (F ω) φ) 2 P := by
  have hrep : ∀ ω : Ω, Sandpile.Continuum.latticePairing R (F ω) φ
      = ∑ x ∈ supportBox d R L, F ω x * cellMass R φ x := fun ω =>
    latticePairing_eq_sum R (F ω) φ hint (supportBox d R L)
      (fun z hz => floor_mem_boxFinset R z (hsupp z hz))
  have hsum : MemLp (fun ω : Ω => ∑ x ∈ supportBox d R L, F ω x * cellMass R φ x) 2 P := by
    refine MeasureTheory.memLp_finsetSum (supportBox d R L)
      (f := fun (x : Sandpile.Site d) (ω : Ω) => F ω x * cellMass R φ x) (fun x _ => ?_)
    have h := (hF x).const_mul (cellMass R φ x)
    exact (MeasureTheory.memLp_congr_ae
      (Filter.Eventually.of_forall fun ω => mul_comm (cellMass R φ x) (F ω x))).mp h
  exact (MeasureTheory.memLp_congr_ae
    (Filter.Eventually.of_forall fun ω => (hrep ω))).mpr hsum

/-- `Sandpile.Continuum.latticePairing` is additive in the field argument: pairing `f - g`
against `φ` equals the difference of the two pairings, since both `embed R f * φ` and
`embed R g * φ` are integrable (`integrable_embed_mul`) and integration is linear. -/
theorem latticePairing_sub (R : ℝ) (f g : Sandpile.Site d → ℝ) (φ : Space d → ℝ)
    (hφ : Integrable φ) {L : ℝ} (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L) :
    Sandpile.Continuum.latticePairing R (fun x => f x - g x) φ
      = Sandpile.Continuum.latticePairing R f φ
        - Sandpile.Continuum.latticePairing R g φ := by
  have hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ supportBox d R L :=
    fun z hz => floor_mem_boxFinset R z (hsupp z hz)
  have hf : Integrable (fun z : Space d => Sandpile.Continuum.embed R f z * φ z) :=
    integrable_embed_mul R f φ hφ (supportBox d R L) hs
  have hg : Integrable (fun z : Space d => Sandpile.Continuum.embed R g z * φ z) :=
    integrable_embed_mul R g φ hφ (supportBox d R L) hs
  show ∫ z : Space d, Sandpile.Continuum.embed R (fun x => f x - g x) z * φ z
    = (∫ z : Space d, Sandpile.Continuum.embed R f z * φ z)
      - ∫ z : Space d, Sandpile.Continuum.embed R g z * φ z
  rw [← MeasureTheory.integral_sub hf hg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show (f (fun i => ⌊R * z i⌋) - g (fun i => ⌊R * z i⌋)) * φ z
    = f (fun i => ⌊R * z i⌋) * φ z - g (fun i => ⌊R * z i⌋) * φ z
  ring

/-- The covariance of the paper's limit field `ℋ_{κ,T}` is the general-weight
covariance at the weight `(1-r/T)^κ`. -/
theorem weightedMembraneCov_eq (d : ℕ) (ν2 κ T : ℝ) (φ ψ : Space d → ℝ) :
    Sandpile.Continuum.weightedMembraneCov d ν2 κ T φ ψ
      = Sandpile.Frozen.WeightedMembraneLimit.generalWeightedMembraneCov d ν2 T
          (fun r => (1 - r / T) ^ κ) φ ψ := rfl


/-- A centred square-integrable law has an integrable positive part. -/
theorem integrable_max_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) : Integrable (fun z : ℝ => max z 0) ν := by
  have hid : Integrable (id : ℝ → ℝ) ν := hsq.integrable (by norm_num)
  refine hid.mono ((continuous_id.max continuous_const).measurable.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  show |max z 0| ≤ |z|
  rcases le_or_gt 0 z with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h.le, abs_zero]
    exact abs_nonneg z

/-- **The diffusive odometer limit, granted the linearization.**  The paper's
proof at `sandpile.tex:4634-4686` is exactly this: `prop:dgt4-linearization`
says that the rescaled centred odometer and the time-weighted field with the
weight `(1-j/n)^κ` differ by a term whose second moment tends to zero, and
`prop:weighted-membrane-limit` at `q(r) = (1-r/T)^κ` identifies the limit of the
second as `ℋ_{κ,T}`.  Convergence in `L²` is convergence in measure, so the two
have the same limit in distribution; tightness is the odometer's own. -/
theorem dgt4_diffusive_membrane_of
    (_hHeatKernel : Sandpile.External.HeatKernelBounds)
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (_hLocalCLT : Sandpile.External.LocalCLT)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (κ : ℝ) (hκ : 0 ≤ κ) (T : ℝ) (hT : 0 < T)
    (hLin : ∀ φ : Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ →
      Tendsto (fun R : ℝ =>
        ∫ σ, (R ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
              ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
                (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ *
                  (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
          ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 0))
    (s : ℝ) (hs : ((d : ℝ) - 4) / 2 < s) :
    Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
      (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Space d → ℝ) =>
        R ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) φ)
      (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T) := by
  classical
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hsq : MemLp (id : ℝ → ℝ) 2 ν :=
    (ProbabilityTheory.evariance_lt_top_iff_memLp aestronglyMeasurable_id).mp hvar'
  have hsqint : Integrable (fun z : ℝ => z ^ 2) ν :=
    (MeasureTheory.memLp_two_iff_integrable_sq aestronglyMeasurable_id).mp hsq
  have hpos : Integrable (fun z : ℝ => max z 0) ν := integrable_max_zero ν hsq
  refine ⟨?_, dgt4_odometer_tight hGreenHigh hBesov hd ν hsqint hpos T hT s hs⟩
  intro φ hφtest
  obtain ⟨C, L, hC0, hL0, hC, hsupp, hint⟩ := exists_bound_of_isTestFn hφtest
  set P : Measure (Sandpile.Site d → ℝ) := Sandpile.centeredMassLaw d ν with hP
  set q : ℝ → ℝ := fun r => (1 - r / T) ^ κ with hqdef
  have hqc : Continuous q := by
    rw [hqdef]
    exact (Real.continuous_rpow_const hκ).comp
      (continuous_const.sub (continuous_id.div_const T))
  -- the two families
  set O : ℝ → (Sandpile.Site d → ℝ) → ℝ := fun R σ =>
    R ^ (((d : ℝ) - 4) / 2) *
      Sandpile.Continuum.latticePairing R
        (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
          Sandpile.meanOdometer P ⌊R ^ 2 * T⌋₊) φ with hO
  set W : ℝ → (Sandpile.Site d → ℝ) → ℝ := fun R σ =>
    R ^ (((d : ℝ) - 4) / 2) *
      Sandpile.Continuum.latticePairing R
        (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ with hW
  -- square integrability of the two families
  have hOmem : ∀ R : ℝ, MemLp (O R) 2 P := by
    intro R
    refine (memLp_two_latticePairing P R
      (fun σ x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x - Sandpile.meanOdometer P ⌊R ^ 2 * T⌋₊)
      (fun x => (memLp_two_odometer ν hsqint hd1 _ x).sub (memLp_const _)) φ hint
      hsupp).const_mul _
  have hWmem : ∀ R : ℝ, MemLp (W R) 2 P := by
    intro R
    refine (memLp_two_latticePairing P R
      (fun σ x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
        q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x)
      (fun x => memLp_two_weightedField_mass ν hsq hd1 _ _ x) φ hint hsupp).const_mul _
  -- the difference is the pairing of the difference
  have hdiff : ∀ (R : ℝ) (σ : Sandpile.Site d → ℝ),
      O R σ - W R σ = R ^ (((d : ℝ) - 4) / 2) *
        Sandpile.Continuum.latticePairing R
          (fun x => (Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
            Sandpile.meanOdometer P ⌊R ^ 2 * T⌋₊) -
            ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ := by
    intro R σ
    rw [latticePairing_sub R _ _ φ hint hsupp, hO, hW]
    ring
  have hwt : ∀ (R : ℝ) (j : ℕ), q ((j : ℝ) / R ^ 2) = (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ := by
    intro R j
    rw [hqdef]
    simp only
    rw [div_div]
  have hfield : ∀ (R : ℝ) (σ : Sandpile.Site d → ℝ),
      (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
          Sandpile.meanOdometer P ⌊R ^ 2 * T⌋₊ -
          ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x)
        = (fun x => (Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
            Sandpile.meanOdometer P ⌊R ^ 2 * T⌋₊) -
            ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) := by
    intro R σ
    funext x
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [hwt R j]
  have hZlim : Tendsto (fun R : ℝ => ∫ σ, (O R σ - W R σ) ^ 2 ∂P) atTop (𝓝 0) := by
    refine (hLin φ hφtest).congr fun R => ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    show (R ^ (((d : ℝ) - 4) / 2) *
        Sandpile.Continuum.latticePairing R
          (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
            Sandpile.meanOdometer P ⌊R ^ 2 * T⌋₊ -
            ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ *
                (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
      = (O R σ - W R σ) ^ 2
    rw [hdiff R σ, hfield R σ]
  have hOW : ∀ R : ℝ, MemLp (fun σ => O R σ - W R σ) 2 P := fun R => (hOmem R).sub (hWmem R)
  have hZint : ∀ R : ℝ, Integrable (fun σ => (O R σ - W R σ) ^ 2) P := fun R =>
    (MeasureTheory.memLp_two_iff_integrable_sq (hOW R).aestronglyMeasurable).mp (hOW R)
  have heL : Tendsto (fun R : ℝ => eLpNorm (fun σ => O R σ - W R σ) 2 P) atTop (𝓝 0) :=
    tendsto_eLpNorm_of_tendsto_integral_sq P (fun R σ => O R σ - W R σ)
      (fun R => (hOW R).aestronglyMeasurable) hZint hZlim
  have hmeasure : TendstoInMeasure P (fun R => O R - W R) atTop 0 := by
    refine MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (fun R => (hOW R).aestronglyMeasurable) aestronglyMeasurable_zero ?_
    simp only [sub_zero]
    exact heL
  have hWlim := (Sandpile.Frozen.weighted_membrane_limit
    d hd hBesov T hT q hqc.continuousOn ν hmean hvar hvar' s hs).1 φ hφtest
  exact MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub O (id : ℝ → ℝ)
    hWlim hmeasure (fun R => (hOmem R).aestronglyMeasurable.aemeasurable)

end Sandpile.Support
