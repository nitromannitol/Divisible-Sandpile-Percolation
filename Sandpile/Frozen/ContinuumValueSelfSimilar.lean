import Sandpile.Continuum.Stopping
import Sandpile.Law
import Sandpile.Support.MeanAValue
import Sandpile.External.VarianceScale
import Sandpile.External.ContinuumOptimalStopping
import Sandpile.Frozen.BrownianScalingLimit
import Sandpile.Support.ContSelfSimilarFromScaling

/-!
# Self-similarity of the continuum value

`Sandpile.Frozen.continuum_value_self_similar` is `prop:continuum-value-selfsimilar`: the
Brownian stopping value `𝒰(T,x)` of the Gaussian heat potential is equal in law to
`T^{(4-d)/4}𝒰(1,0)`, has a uniform exponential moment across the discrete rescaled odometers
`𝒰_R(1,0)` and in the continuum limit, and its `p`-th moment scales as `T^{p(4-d)/4}` and is
finite and positive.  The proof descends the parabolic scaling limit of the discrete odometer
through the optimal-stopping representation, which realizes the value as a measurable functional
of the field alone and so carries equality in law of the fields to equality in law of the values.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.continuum_value_self_similar
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[PW] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hZgrow : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k)
    {ΩB : Type u} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hOS : Sandpile.External.ContinuumOptimalStopping ΩB)
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (hBc : ∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) :
    (∃ U : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ,
      (∀ T : ℝ, 0 < T → ∀ x : Sandpile.Continuum.Space d,
        Measurable (U T x) ∧
        U T x =ᵐ[PW] fun ω =>
          Sandpile.Continuum.continuumValue d Z B PB T x ω) ∧
      ∀ T : ℝ, 0 < T → ∀ x : Sandpile.Continuum.Space d,
        PW.map (U T x) = PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 0 ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧
      (∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
        Integrable (fun σ => Real.exp (θ *
          Sandpile.Continuum.rescaledOdometer d R 1 0 σ))
          (Sandpile.centeredMassLaw d ν) ∧
        ∫ σ, Real.exp (θ *
          Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
          ∂(Sandpile.centeredMassLaw d ν) ≤ M) ∧
      Integrable (fun ω => Real.exp (θ *
        Sandpile.Continuum.continuumValue d Z B PB 1 0 ω)) PW) ∧
    (∀ T : ℝ, 0 < T → ∀ x : Sandpile.Continuum.Space d, ∀ p : ℝ, 0 < p →
      Integrable (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB T x ω ^ p) PW ∧
      Integrable (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω ^ p) PW ∧
      ∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB T x ω ^ p ∂PW =
        T ^ (p * (4 - (d : ℝ)) / 4) *
          ∫ ω, Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω ^ p ∂PW ∧
      0 < ∫ ω, Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω ^ p ∂PW)
-- FROZEN-STATEMENT-END
:= by
  have _ := hOS
  exact Sandpile.Support.continuum_value_self_similar_of_parabolic_limit
    d hd0 hd ν hvar hvar' θ₀ hθ₀ hexp PW W hW Z hZmod hZcont PB B
    (fun T hT => Sandpile.Frozen.brownian_scaling_limit hStab d hd0 hd ν hmean
      hvar hvar' θ₀ hθ₀ hexp ΩW PW W hW Z hZmod hZcont hZgrow ΩB PB B hB hBc hBm T hT)
