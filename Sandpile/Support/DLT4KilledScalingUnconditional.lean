import Sandpile.External.CubeStoppingStabilityProved
import Sandpile.External.ContinuumStoppingStabilityProved
import Sandpile.Frozen.DLT4KilledScaling

/-!
# Killed scaling below dimension four

The cube-killed scaling remark below dimension four holds without cited hypotheses: the
continuum and cube-killed stopping stability inputs are both proved.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- `rem:dlt4-killed-scaling` without hypotheses: the continuum and cube-killed stopping
stability inputs are proved by `Sandpile.External.continuumStoppingStability_holds` and
`Sandpile.External.cubeStoppingStability_holds`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.dlt4_killed_scaling_proved
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (hZcont : ∀ᵐ ω ∂PW, Continuous fun q : ℝ × Sandpile.Continuum.Space d =>
      Sandpile.Continuum.gaussianPotential d (variance id ν) W q.1 q.2 ω)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K) (T : ℝ) (hT : 0 < T)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    (∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
        P.map Prod.fst = Sandpile.centeredMassLaw d ν ∧
        P.map Prod.snd = PW ∧
        P {p | ∃ u ∈ K,
            ε < |R ^ (-(2 - (d : ℝ) / 2)) *
                  Sandpile.localizedOdometer (Sandpile.supBox (fun i => ⌊R * u i⌋) R)
                    (Sandpile.scenery d p.1) ⌊T * R ^ 2⌋₊ (fun i => ⌊R * u i⌋)
                - Sandpile.Continuum.brownianValueCube (B u) PB
                    (fun t y => Sandpile.Continuum.gaussianPotential d (variance id ν) W t y p.2)
                    T 1 u|}
          ≤ ENNReal.ofReal δ) ∧
    (∀ᵐ ω ∂PW, ∀ u ∈ K,
      Sandpile.Continuum.brownianValueBall (B u) PB
          (fun t y => Sandpile.Continuum.gaussianPotential d (variance id ν) W t y ω) T 1 u ≤
        Sandpile.Continuum.brownianValueCube (B u) PB
          (fun t y => Sandpile.Continuum.gaussianPotential d (variance id ν) W t y ω) T 1 u) ∧
    (∀ (θ M v : ℝ) (νs : ℕ → Measure ℝ), 0 < θ → 0 < v →
      (∀ k, IsProbabilityMeasure (νs k)) →
      (∀ k, ∫ z, z ∂(νs k) = 0) →
      (∀ k, Integrable (fun z => Real.exp (θ * |z|)) (νs k)) →
      (∀ k, ∫ z, Real.exp (θ * |z|) ∂(νs k) ≤ M) →
      Tendsto (fun k => variance id (νs k)) atTop (𝓝 v) →
      ∃ k₀ : ℕ, ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, R₀ ≤ R →
        ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
          P.map Prod.fst = Sandpile.centeredMassLaw d (νs k) ∧
          P.map Prod.snd = PW ∧
          P {p | ∃ u ∈ K,
              ε < |R ^ (-(2 - (d : ℝ) / 2)) *
                    Sandpile.localizedOdometer (Sandpile.supBox (fun i => ⌊R * u i⌋) R)
                      (Sandpile.scenery d p.1) ⌊T * R ^ 2⌋₊ (fun i => ⌊R * u i⌋)
                  - Sandpile.Continuum.brownianValueCube (B u) PB
                      (fun t y => Sandpile.Continuum.gaussianPotential d v W t y p.2)
                      T 1 u|}
            ≤ ENNReal.ofReal δ) ∧
    (∀ (v : ℝ) (ω : ΩW) (u : Sandpile.Continuum.Space d),
      Sandpile.Continuum.brownianValueCube (B u) PB
          (fun t y => Sandpile.Continuum.gaussianPotential d v W t y ω) T 1 u =
        Real.sqrt v * Sandpile.Continuum.brownianValueCube (B u) PB
          (fun t y => Sandpile.Continuum.gaussianPotential d 1 W t y ω) T 1 u)
-- FROZEN-STATEMENT-END
:=
  Sandpile.Frozen.dlt4_killed_scaling Sandpile.External.continuumStoppingStability_holds
    Sandpile.External.cubeStoppingStability_holds d hd hd3 ν hmean hvar hvar' θ₀ hθ₀ hexp
    ΩW PW W hW hZcont ΩB PB B hB K hK T hT ε δ hε hδ
