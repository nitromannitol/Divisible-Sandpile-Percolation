import Sandpile.Support.LinJacobianIntegrableInputs
import Sandpile.Support.LinTestedPairing
import Sandpile.Support.ContWeightedLimit

/-!
# The `L²` linearization limit for a nonnegative test function

This file assembles the `L²` linearization limit for the odometer field tested against a
nonnegative test function `φ`: with the derivative-variance limit, the mean-gradient
approximation, the uniform coefficient bound, and the three square-integrability hypotheses as
inputs, Step 2 gives the vanishing `L²` norm of the tested field minus its linear approximation.
Nonnegativity of `φ` is what makes the tested field convex in each coordinate of the scenery,
which is the hypothesis Step 2 needs; a signed test function is handled elsewhere as the
difference of its positive and negative parts. The limits may be taken along any real-scale
filter below `atTop`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- The positive part of the one-site law is integrable when its square is. -/
theorem integrable_posPart_of_sq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) : Integrable (fun z => max z 0) ν := by
  have h2 : MemLp (id : ℝ → ℝ) 2 ν :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq
  have hid : Integrable (id : ℝ → ℝ) ν := h2.integrable (by norm_num)
  refine Integrable.mono' hid.abs
    ((measurable_id.max measurable_const).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  rcases le_total 0 z with hz | hz
  · rw [max_eq_left hz]; exact le_rfl
  · rw [max_eq_right hz, abs_zero]; exact abs_nonneg _

/-- **`eq:dgt4-linearization-from-paths` for a nonnegative test function.** -/
theorem tendsto_l2_frozen_of_nonneg {l : Filter ℝ} [NeZero d] (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hmean : ∫ z, z ∂ν = 0) (hsqν : Integrable (fun z => z ^ 2) ν)
    (φ : Space d → ℝ) (hφsq : Integrable (fun z => φ z ^ 2))
    (hφ : ∀ z, 0 ≤ φ z) (Cφ L : ℝ) (hCφ : 0 ≤ Cφ) (hL : 0 ≤ L)
    (hb : ∀ z, |φ z| ≤ Cφ) (hint : Integrable φ)
    (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L)
    (T : ℝ) (hT : 0 < T) (q : ℝ → ℕ → ℝ) (C : ℝ)
    (hsurv : Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, survivalInd σ ⌊R ^ 2 * T⌋₊ j X ∂(Sandpile.centeredMassLaw d ν)) - q R j|
            ∂(walkLaw d 0)) l (𝓝 0))
    (hcov : ∀ δ : ℝ, δ ∈ Set.Ioo 0 T →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun l (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * R ^ 2 →
          (j : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Site d,
            Frozen.DGT4PathSurvival.IsNNPath i X →
            Frozen.DGT4PathSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.survivalInd σ ⌊R ^ 2 * T⌋₊ i X *
                  Sandpile.survivalInd σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν)) -
                (∫ σ, Sandpile.survivalInd σ ⌊R ^ 2 * T⌋₊ i X
                  ∂(Sandpile.centeredMassLaw d ν)) *
                (∫ σ, Sandpile.survivalInd σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν))| ≤
              C / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun R)
    (hl : l ≤ atTop := by exact le_rfl) :
    Tendsto (fun R : ℝ =>
        ∫ σ, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
          (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
            Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
            ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
          ∂(Sandpile.centeredMassLaw d ν)) l (𝓝 0) := by
  classical
  set n : ℝ → ℕ := fun R => ⌊R ^ 2 * T⌋₊ with hn
  set s : ℝ → Finset (Site d) := fun R => Sandpile.Support.supportBox d R L with hsdef
  set a : ℝ → Site d → ℝ := fun R => testedWeightCut d R L φ with hadef
  set coef : ℝ → Site d → ℝ := fun R v =>
    ∑ x ∈ s R, a R x * ∑ j ∈ Finset.range (n R), q R j * heatKernel d j x v with hcoefdef
  obtain ⟨B₀, hB₀⟩ := exists_sum_testedGreenWeight_sq_le hd hGreen φ hφ Cφ L hCφ hL hb hint n
  have hstep2 := tendsto_l2_testedField_jacobian ν hmean hsqν s a n
    (fun R x => testedWeightCut_nonneg R L hφ x) coef B₀ hB₀
    (tendsto_finset_variance_testedWeight (hl := hl) hd hGreen hInter ν φ hφsq hφ Cφ L hCφ hL hb
      hint n T C hT hcov)
    (tendsto_coef_error_testedWeight (hl := hl) hd ν φ hφsq hint hφ L T q hsurv)
    (fun R => integrable_sq_testedField_sub_linear ν hsqν (s R) (a R) (n R)
      (testedSites (s R) (n R))
      (fun v => ∫ η, (∑ x ∈ s R, a R x * odometerJacobian η (n R) x v)
        ∂(LatticeProb.iidLaw d ν))
      (∫ η, testedField (s R) (a R) (n R) η ∂(LatticeProb.iidLaw d ν)))
    (fun R => integrable_sq_linear_sub_linear ν hsqν (testedSites (s R) (n R))
      (fun v => ∫ η, (∑ x ∈ s R, a R x * odometerJacobian η (n R) x v)
        ∂(LatticeProb.iidLaw d ν)) (coef R))
    (fun R => integrable_sq_testedField_sub_linear ν hsqν (s R) (a R) (n R)
      (testedSites (s R) (n R)) (coef R)
      (∫ η, testedField (s R) (a R) (n R) η ∂(LatticeProb.iidLaw d ν)))
  refine hstep2.congr' ?_
  filter_upwards [(eventually_ge_atTop (1 : ℝ)).filter_mono hl] with R hR
  have hpos : Integrable (fun z => max z 0) ν := integrable_posPart_of_sq ν hsqν
  have hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s R :=
    fun z hz => Sandpile.Support.floor_mem_boxFinset R z (hsupp z hz)
  have hagree : ∀ x ∈ s R, a R x
      = R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x := by
    intro x hx
    have hnn : 0 ≤ Sandpile.Support.cellMass R φ x := by
      rw [Sandpile.Support.cellMass]
      exact integral_nonneg fun w => hφ w
    simp only [hadef]
    rw [testedWeightCut_eq_scaled hR L hφ hx, abs_of_nonneg hnn]
  have hfield : testedField (s R) (a R) (n R)
      = testedField (s R)
          (fun x => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) (n R) := by
    funext ζ
    exact Finset.sum_congr rfl fun x hx => by rw [hagree x hx]
  have hlin : ∀ v : Site d, coef R v
      = ∑ x ∈ s R, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) *
          ∑ j ∈ Finset.range (n R), q R j * heatKernel d j x v := by
    intro v
    exact Finset.sum_congr rfl fun x hx => by rw [hagree x hx]
  rw [integral_sq_frozen_eq_testedField ν (by omega) hpos R (n R) (q R) φ hint hsupp (s R) hs,
    hfield]
  exact congrArg _ (funext fun ζ => by rw [Finset.sum_congr rfl fun v _ => by rw [hlin v]])

end Sandpile
