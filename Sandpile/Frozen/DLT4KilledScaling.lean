import Sandpile.Law
import Sandpile.Support.ExplKilledValue
import Sandpile.External.ContStoppingStability
import Sandpile.Frozen.MeanLocalization
import Sandpile.Support.KillScaling
import Sandpile.Support.ExplKilledSequence
import Sandpile.External.LocalCLTProved

/-!
# The cube-killed scaling limit, frozen

The cube-killed scaling limit of `sandpile.tex:1957-1984` (label `rem:dlt4-killed-scaling`), a
conjunction of three assertions. (1) For a centered scenery law in dimensions at most three, the
rescaled localized odometer can be coupled with the cube-killed Brownian value
`brownianValueCube` so that their uniform distance on each compact set tends to zero in
probability, using the Gaussian heat potential fixed at `sandpile.tex:1019-1021` and
`sandpile.tex:2104`. (2) The comparison `brownianValueBall ≤ brownianValueCube` at radius one,
since the Euclidean unit ball is contained in the cube, holding for almost every white-noise
sample and every point of a compact set `K`. (3) The same coupling for a sequence of mean-zero
i.i.d. laws with a common exponential-moment bound whose variances converge to `v > 0`, uniformly
in the law index and the scale, together with the identity that the cube-killed value at variance
`v` is `√v` times the value at unit variance. The proof of (1) uses the parity local CLT through
heat-potential invariance and cube stopping stability through the killed form of the cited
Coquet-Toldo result, with both realization spaces bound at `Type 0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dlt4_killed_scaling
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (hCube : Sandpile.External.CubeStoppingStability)
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
-- FROZEN-STATEMENT-END
  by
    have _hStab := hStab
    have hσ : 0 < variance id ν := ENNReal.toReal_pos hvar.ne' hvar'.ne
    refine ⟨Sandpile.dlt4_killed_scaling_of_inputs Sandpile.External.localCLT hCube d hd hd3 ν
      hmean hvar hvar' θ₀ hθ₀ hexp ΩW PW W hW hZcont ΩB PB B hB K hK T hT ε δ hε hδ, ?_, ?_, ?_⟩
    · filter_upwards [hZcont] with ω hω u _
      exact Sandpile.Continuum.brownianValueBall_le_brownianValueCube_of_continuous PB (B u) u
        (hB u) _ hω T hT.le
    · intro θ M v νs hθ hv hprob hmeans hexps hMs hvars
      have hZv : ∀ᵐ ω ∂PW, Continuous fun q : ℝ × Sandpile.Continuum.Space d =>
          Sandpile.Continuum.gaussianPotential d v W q.1 q.2 ω := by
        filter_upwards [hZcont] with ω hω
        exact Sandpile.Continuum.continuous_gaussianPotential_of_pos_variance v _ hσ W ω hω
      exact Sandpile.dlt4_killed_scaling_sequence_of_inputs Sandpile.External.localCLT hCube d hd
        hd3 θ M v hθ hv νs hprob hmeans hexps hMs hvars ΩW PW W hW hZv ΩB PB B hB K hK T hT ε δ
        hε hδ
    · intro v ω u
      exact Sandpile.Continuum.brownianValueCube_gaussianPotential_eq_sqrt_mul (B u) PB v W ω T
        1 u
