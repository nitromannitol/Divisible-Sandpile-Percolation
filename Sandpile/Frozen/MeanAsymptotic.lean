import Sandpile.Continuum.Stopping
import Sandpile.Law
import Sandpile.External.LocalCLTProved
import Sandpile.Support.MeanACorollary

/-!
# Mean and variance asymptotics from the continuum value, below dimension four

This file proves the frozen statement of `cor:dlt4-mean-asymptotic` (`sandpile.tex:2068-2086`),
for `d ≤ 3` and scenery with mean zero, finite positive variance, and a finite exponential moment.
The rescaled odometer `𝒰_R(T,x) = R^{-(2-d/2)} u_{⌊R²T⌋}(⌊Rx⌋)`
(`Sandpile.Continuum.rescaledOdometer`) has mean and variance converging as `R → ∞` to those of
the continuum stopping value `𝒰 = 𝒰_Z` (`Sandpile.Continuum.continuumValue`) at `(T,x)`, which by
self-similarity equal `T^{(4-d)/4} E 𝒰(1,0)` and `T^{(4-d)/2} Var(𝒰(1,0))` with `Var(𝒰(1,0)) > 0`.
Consequently `E u_t(0) ∼ E 𝒰(1,0) t^{(4-d)/4}` and `Var(u_t(0)) ∼ Var(𝒰(1,0)) t^{(4-d)/2}` as
`t → ∞`. Since Mathlib constructs neither white noise nor Brownian motion, both are quantified
over abstract realization spaces `ΩW` and `ΩB`, and the statement carries the continuum stopping
stability input as an explicit hypothesis together with the square-integrability of all four
limiting quantities, since Mathlib's junk value for a non-integrable mean or an out-of-`L²`
variance is zero.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u


-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dlt4_mean_asymptotic
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
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (T : ℝ) (hT : 0 < T) (x : Sandpile.Continuum.Space d) :
    (∀ R : ℝ, 1 ≤ R →
        MemLp (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ) 2
          (Sandpile.centeredMassLaw d ν)) ∧
      (∀ t : ℕ, MemLp (fun σ => Sandpile.odometer σ t 0) 2 (Sandpile.centeredMassLaw d ν)) ∧
      MemLp (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB T x ω) 2 PW ∧
      MemLp (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω) 2 PW ∧
      Tendsto (fun R : ℝ => ∫ σ, Sandpile.Continuum.rescaledOdometer d R T x σ
          ∂(Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB T x ω ∂PW)) ∧
      (∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB T x ω ∂PW =
        T ^ ((4 - (d : ℝ)) / 4) * ∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB 1 0 ω ∂PW) ∧
      Tendsto (fun R : ℝ => variance
          (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ)
          (Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (T ^ ((4 - (d : ℝ)) / 2) * variance
          (fun ω => Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω) PW)) ∧
      0 < variance (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω) PW ∧
      Tendsto (fun t : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t /
          ((∫ ω, Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω ∂PW) * (t : ℝ) ^ ((4 - (d : ℝ)) / 4)))
        atTop (𝓝 1) ∧
      Tendsto (fun t : ℕ =>
          variance (fun σ => Sandpile.odometer σ t 0) (Sandpile.centeredMassLaw d ν) /
          (variance (fun ω => Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω) PW * (t : ℝ) ^ ((4 - (d : ℝ)) / 2)))
        atTop (𝓝 1)
-- FROZEN-STATEMENT-END
:= by
  have hVarScale : Sandpile.External.VarianceScale := Sandpile.External.varianceScale
  exact Sandpile.Support.dlt4_mean_asymptotic_wired Sandpile.External.localCLT hStab hVarScale
    d hd0 hd ν hmean hvar hvar' θ₀ hθ₀ hexp ΩW PW W hW Z hZmod hZcont hZgrow ΩB PB hOS B hB hBc
    hBm T hT x
