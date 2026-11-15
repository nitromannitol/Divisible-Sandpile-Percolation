import Sandpile.External.RellichKondrachovNegSobolev
import Sandpile.Frozen.DGT4LinearizationFromSurvival
import LatticeProb.Analysis.Sobolev.RellichConvolvedCompact

/-!
# The Rellich-Kondrachov embedding, proved

This module discharges the external input `Sandpile.External.RellichKondrachovNegSobolev`, the
Rellich-Kondrachov compact embedding `H^s(D) → H^{s₀}(D)` for `s₀ < s` on a bounded domain in
finite-`η`-net form, instead of assuming it.

The input is by definition the shared library's `LatticeProb.External.RellichKondrachovNegSobolev`,
and the library proves that statement as `LatticeProb.Sobolev.rellichKondrachovNegSobolev_holds`.
Its proof covers the mollified unit ball of `H^s(D)` by finitely many mollified centres, using
derivative bounds and the compactness of simultaneous jets, and then transfers the centres back to
test functions on `D` through a uniformly chosen mollifier.

The `Prop` and its name are left untouched, so no frozen statement changes.
`Sandpile.dgt4_linearization_from_survival` is `lem:dgt4-linearization-from-survival` without the
hypothesis `Sandpile.External.RellichKondrachovNegSobolev`; the Besov tightness criterion
`Sandpile.External.ContinuumBesovTightness` remains a hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

-- FROZEN-STATEMENT-BEGIN
/-- The Rellich-Kondrachov compact embedding `H^s(D) → H^{s₀}(D)` for `s₀ < s` on a bounded
domain, in the finite-`η`-net form the `H^{-s}_loc` clause of
`lem:dgt4-linearization-from-survival` consumes, proved rather than assumed. -/
theorem Sandpile.External.rellichKondrachovNegSobolev_holds :
    Sandpile.External.RellichKondrachovNegSobolev
-- FROZEN-STATEMENT-END
:= LatticeProb.Sobolev.rellichKondrachovNegSobolev_holds

/-- `lem:dgt4-linearization-from-survival` without the hypothesis
`Sandpile.External.RellichKondrachovNegSobolev`, which
`Sandpile.External.rellichKondrachovNegSobolev_holds` proves. -/
theorem Sandpile.dgt4_linearization_from_survival
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (T : ℝ) (hT : 0 < T) (q : ℝ → ℕ → ℝ)
    (hq : ∀ (R : ℝ) (j : ℕ), j < ⌊R ^ 2 * T⌋₊ → q R j ∈ Set.Icc (0 : ℝ) 1)
    (hsurvival : Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ
                  ⌊R ^ 2 * T⌋₊ j X ∂(Sandpile.centeredMassLaw d ν)) - q R j|
            ∂(Sandpile.walkLaw d 0)) atTop (𝓝 0))
    (hcov : ∃ C : ℝ, ∀ δ : ℝ, δ ∈ Set.Ioo 0 T →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun atTop (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 → (j : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Sandpile.Site d,
            Sandpile.Frozen.DGT4LinearizationFromSurvival.IsNNPath i X →
            Sandpile.Frozen.DGT4LinearizationFromSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ i X *
                  Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν)) -
                (∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ
                    ⌊R ^ 2 * T⌋₊ i X ∂(Sandpile.centeredMassLaw d ν)) *
                (∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ
                    ⌊R ^ 2 * T⌋₊ j Y ∂(Sandpile.centeredMassLaw d ν))| ≤
              C / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun R) :
    (∀ φ : Sandpile.Continuum.Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ →
        Tendsto (fun R : ℝ =>
            ∫ σ, (R ^ (((d : ℝ) - 4) / 2) *
              Sandpile.Continuum.latticePairing R
                (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
                  Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
                  ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
                    q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
              ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 0)) ∧
      ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
        ∀ D : Set (Sandpile.Continuum.Space d), Sandpile.Continuum.IsDomain D →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun R : ℝ =>
                ((Sandpile.centeredMassLaw d ν)
                  {σ | ENNReal.ofReal ε < Sandpile.Continuum.negSobolevNorm d s D
                    (fun φ => R ^ (((d : ℝ) - 4) / 2) *
                      Sandpile.Continuum.latticePairing R
                        (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
                          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
                          ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
                            q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)}).toReal)
              atTop (𝓝 0) :=
  Sandpile.Frozen.dgt4_linearization_from_survival d hd hBesov
    Sandpile.External.rellichKondrachovNegSobolev_holds ν hatom hmean hvar hvar' T hT q hq
    hsurvival hcov
