import Sandpile.Support.LinL2Assembly
import Sandpile.Support.LinPairingSplit

/-! # Frozen First Conjunct

The first conjunct of `lem:dgt4-linearization-from-survival`
(`sandpile.tex:5615-5660`): the `L²` convergence of the frozen integrand, from
the convex-linear bound, the vanishing derivative-variance sum and the vanishing
coefficient replacement.
-/

open MeasureTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- **The first conjunct of `lem:dgt4-linearization-from-survival`** (`sandpile.tex:5615-5660`):
given the convex-linear bound `hbound`, the vanishing coefficient-sum limit `hClim`, and the
stated integrability hypotheses, the rescaled difference between the tested odometer pairing,
its mean, and the linear scenery-average pairing tends to zero in `L²`, for every nonnegative
test function `φ`. -/
theorem frozen_first_conjunct_of_inputs [NeZero d]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ) (q : ℝ → ℕ → ℝ)
    (V η : ℝ → ℝ) (C₀ B₀ : ℝ) (hC₀ : 0 ≤ C₀) (hB₀ : 0 ≤ B₀)
    (hη : Tendsto η atTop (𝓝 0)) (hVlim : Tendsto V atTop (𝓝 0))
    (hbound : ∀ φ : Space d → ℝ, IsTestFn Set.univ φ → ∀ L : ℝ, 0 < L →
      ∀ᶠ R : ℝ in atTop,
        (∫ σ, ((R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
              (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x) φ)
            - (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
              (fun _ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) φ)) ^ 2
          ∂(Sandpile.centeredMassLaw d ν))
        ≤ C₀ * L ^ 2 * V R + C₀ * η L * B₀)
    (hClim : ∀ φ : Space d → ℝ, IsTestFn Set.univ φ →
      Tendsto (fun R : ℝ =>
        ∫ σ, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
            (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
          ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 0))
    (hA : ∀ φ : Space d → ℝ, IsTestFn Set.univ φ → ∀ R : ℝ,
      Integrable (fun σ => (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x) φ
          - R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
            (fun _ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) φ) ^ 2)
        (Sandpile.centeredMassLaw d ν))
    (hCi : ∀ φ : Space d → ℝ, IsTestFn Set.univ φ → ∀ R : ℝ,
      Integrable (fun σ => (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2)
        (Sandpile.centeredMassLaw d ν))
    (hAC : ∀ φ : Space d → ℝ, IsTestFn Set.univ φ → ∀ R : ℝ,
      Integrable (fun σ => ((R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
          (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x) φ)
        - (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
          (fun _ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) φ)
        - (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
          (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)) ^ 2)
        (Sandpile.centeredMassLaw d ν))
    (hL : ∀ φ : Space d → ℝ, IsTestFn Set.univ φ → ∃ L : ℝ, 0 < L ∧
      Integrable φ volume ∧ ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L) :
    ∀ φ : Space d → ℝ, IsTestFn Set.univ φ →
      Tendsto (fun R : ℝ =>
        ∫ σ, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
              ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
                q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
          ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 0) := by
  intro φ hφ
  obtain ⟨L, hLpos, hφint, hsupp⟩ := hL φ hφ
  have hsplit : ∀ R : ℝ,
      (∫ σ, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
          (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
            Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
            ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
        ∂(Sandpile.centeredMassLaw d ν))
      = ∫ σ, ((R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x) φ)
          - (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
            (fun _ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) φ)
          - (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
            (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)) ^ 2
        ∂(Sandpile.centeredMassLaw d ν) := by
    intro R
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    exact Sandpile.frozen_integrand_eq_sub_pairings R σ φ hφint hsupp ⌊R ^ 2 * T⌋₊
      (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊)
      (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
        q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x)
  simpa only [hsplit] using
    Sandpile.tendsto_l2_of_convex_linear_and_replacement (Sandpile.centeredMassLaw d ν)
      (fun R σ => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x) φ)
      (fun R σ => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun _ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) φ)
      (fun R σ => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)
      V η C₀ B₀ hC₀ hB₀
      (hA φ hφ) (hCi φ hφ) (hAC φ hφ)
      (Filter.Eventually.of_forall fun R => integral_nonneg fun σ => sq_nonneg _)
      hη (hbound φ hφ) hVlim (hClim φ hφ)

end Sandpile
