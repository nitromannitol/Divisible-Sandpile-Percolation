import Sandpile.External.CubeStoppingStabilityProved
import Sandpile.External.ContinuumStoppingStabilityProved
import Sandpile.External.ContinuumRSW.Consequences
import Sandpile.External.BallOccupationDensityProved
import Sandpile.External.LSSDominationProved
import Sandpile.Frozen.DLT4KilledScaling

/-!
# Consequences of cube-killed stopping stability

Successors of the statements that carry `Sandpile.External.CubeStoppingStability` as a
hypothesis, with that hypothesis discharged by `Sandpile.External.cubeStoppingStability_holds`.

* `Sandpile.dlt4_killed_scaling_proved` is `rem:dlt4-killed-scaling` with no hypothesis left:
  the stopping stability inputs are supplied by `Sandpile.External.continuumStoppingStability_holds`
  and `Sandpile.External.cubeStoppingStability_holds`.
* `Sandpile.percolation_below_criticality_of_planar_rsw_proved` and
  `Sandpile.critical_level_percolation_of_planar_rsw_proved` are Theorems 1.1 and 1.2 with the
  planar RSW input as the only remaining hypothesis.
* `Sandpile.d23_critical_level_percolation_of_continuum_rsw` is
  `thm:d23-critical-level-percolation` with the continuum RSW input as the only remaining
  hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- `rem:dlt4-killed-scaling` without hypotheses: the continuum and cube-killed stopping
stability inputs are proved by `Sandpile.External.continuumStoppingStability_holds` and
`Sandpile.External.cubeStoppingStability_holds`. -/
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
          (fun t y => Sandpile.Continuum.gaussianPotential d 1 W t y ω) T 1 u) :=

  Sandpile.Frozen.dlt4_killed_scaling Sandpile.External.continuumStoppingStability_holds
    Sandpile.External.cubeStoppingStability_holds d hd hd3 ν hmean hvar hvar' θ₀ hθ₀ hexp
    ΩW PW W hW hZcont ΩB PB B hB K hK T hT ε δ hε hδ

/-- **Theorem 1.1** (`thm:main-nontriviality`) with the planar RSW input as the only remaining
hypothesis; the continuum RSW input is derived from it and the cube-killed stopping stability is
proved by `Sandpile.External.cubeStoppingStability_holds`. -/
theorem Sandpile.percolation_below_criticality_of_planar_rsw_proved
    (hRSW : Sandpile.External.PlanarRSW)
    (d : ℕ) (hd : 2 ≤ d) (μ : ℝ → Measure ℝ) (hprob : ∀ ρ, IsProbabilityMeasure (μ ρ))
    (hmean : ∀ ρ ∈ Set.Ioc (0 : ℝ) 1, ∫ s, s ∂(μ ρ) = ρ)
    (ρ₀ ν₀ θ₀ K₀ : ℝ) (hρ₀ : ρ₀ ∈ Set.Ioo (0 : ℝ) 1) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀)
    (hvar : ∀ ρ ∈ Set.Ico ρ₀ 1, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (μ ρ))
    (hexpint : ∀ ρ ∈ Set.Ico ρ₀ 1, Integrable (fun s => Real.exp (θ₀ * |s - ρ|)) (μ ρ))
    (hexp : ∀ ρ ∈ Set.Ico ρ₀ 1, ∫ s, Real.exp (θ₀ * |s - ρ|) ∂(μ ρ) ≤ K₀) :
    ∃ ρPlus ∈ Set.Ico ρ₀ 1, ∀ ρ ∈ Set.Ioo ρPlus 1,
      ∀ᵐ σ ∂(Sandpile.massLaw d (μ ρ)),
        Sandpile.HasInfiniteComponent (Sandpile.toppledSet σ) :=
  Sandpile.percolation_below_criticality_of_planar_rsw hRSW
    Sandpile.External.cubeStoppingStability_holds d hd μ hprob hmean ρ₀ ν₀ θ₀ K₀ hρ₀ hν₀ hθ₀
    hvar hexpint hexp

/-- **Theorem 1.2** (`thm:main-critical-level-percolation`) with the planar RSW input as the
only remaining hypothesis; the continuum RSW input is derived from it and the cube-killed
stopping stability is proved by `Sandpile.External.cubeStoppingStability_holds`. -/
theorem Sandpile.critical_level_percolation_of_planar_rsw_proved
    (hRSW : Sandpile.External.PlanarRSW)
    (d : ℕ) (hd : 2 ≤ d) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.massLaw d μ),
          Sandpile.HasInfiniteComponent
            {x | c * Sandpile.criticalScale d t < Sandpile.odometer σ t x} :=
  Sandpile.critical_level_percolation_of_planar_rsw hRSW
    Sandpile.External.cubeStoppingStability_holds d hd ν₀ θ₀ K₀ hν₀ hθ₀

/-- `thm:d23-critical-level-percolation` with the continuum RSW input as the only remaining
hypothesis; the LSS domination and cube-killed stopping stability inputs are proved by
`Sandpile.External.lssDomination` and `Sandpile.External.cubeStoppingStability_holds`. -/
theorem Sandpile.d23_critical_level_percolation_of_continuum_rsw
    (hRSWc : Sandpile.External.ContinuumRSW)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
          LatticeProb.HasInfiniteComponent
            {z : Sandpile.Site 2 | c * (t : ℝ) ^ ((4 - (d : ℝ)) / 4) <
              Sandpile.odometer σ t (Sandpile.planeSite z)} :=
  Sandpile.d23_critical_level_percolation Sandpile.External.lssDomination hRSWc
    Sandpile.External.cubeStoppingStability_holds d hd ν₀ θ₀ K₀ hν₀ hθ₀
