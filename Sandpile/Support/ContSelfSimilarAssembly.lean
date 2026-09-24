/-
The assembly of `prop:continuum-value-selfsimilar` from its residual inputs.
-/
import Sandpile.Support.MeanAValue
import Sandpile.Support.ContClause1
import Sandpile.Support.ContClause3
import Sandpile.Support.ContValueMemLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open Sandpile.Continuum

namespace Sandpile.Support

/-- The three clauses of `prop:continuum-value-selfsimilar` (`sandpile.tex:1961-1980`) from
the residual inputs the continuous modification leaves: the almost-everywhere
measurability of the value in the field's sample point, the law identity of clause 1, the
exponential moment of clause 2, and the moment integrability of clause 3.  Clause 1 is
`clause1_of_continuous`; clause 3 is the power-moment transfer of `ContClause3`; clause 2
is carried through unchanged. -/
theorem continuum_value_self_similar_of_inputs {ΩW ΩB : Type*} [MeasurableSpace ΩW]
    [MeasurableSpace ΩB] (d : ℕ) (ν : Measure ℝ) (ν2 : ℝ)
    (W : (Space d → ℝ) → ΩW → ℝ) (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (hW : IsWhiteNoise d W PW)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (B : Space d → ℝ≥0 → ΩB → Space d) (PB : Measure ΩB)
    (hmeas : ∀ T : ℝ, 0 < T → ∀ x : Space d,
      AEMeasurable (fun ω => continuumValue d Z B PB T x ω) PW)
    (hlaw : ∀ T : ℝ, 0 < T → ∀ x : Space d,
      PW.map (fun ω => continuumValue d Z B PB T x ω)
        = PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * continuumValue d Z B PB 1 0 ω))
    (hexp : ∃ θ : ℝ, 0 < θ ∧
      (∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
        Integrable (fun σ => Real.exp (θ * rescaledOdometer d R 1 0 σ))
          (Sandpile.centeredMassLaw d ν) ∧
        ∫ σ, Real.exp (θ * rescaledOdometer d R 1 0 σ)
          ∂(Sandpile.centeredMassLaw d ν) ≤ M) ∧
      Integrable (fun ω => Real.exp (θ * continuumValue d Z B PB 1 0 ω)) PW)
    (hmom : ∀ T : ℝ, 0 < T → ∀ x : Space d, ∀ p : ℝ, 0 < p →
      Integrable (fun ω => continuumValue d Z B PB T x ω ^ p) PW ∧
      Integrable (fun ω => continuumValue d Z B PB 1 0 ω ^ p) PW ∧
      0 < ∫ ω, continuumValue d Z B PB 1 0 ω ^ p ∂PW) :
    (∃ U : ℝ → Space d → ΩW → ℝ,
      (∀ T : ℝ, 0 < T → ∀ x : Space d,
        Measurable (U T x) ∧
        U T x =ᵐ[PW] fun ω => continuumValue d Z B PB T x ω) ∧
      ∀ T : ℝ, 0 < T → ∀ x : Space d,
        PW.map (U T x) = PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 0 ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧
      (∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
        Integrable (fun σ => Real.exp (θ * rescaledOdometer d R 1 0 σ))
          (Sandpile.centeredMassLaw d ν) ∧
        ∫ σ, Real.exp (θ * rescaledOdometer d R 1 0 σ)
          ∂(Sandpile.centeredMassLaw d ν) ≤ M) ∧
      Integrable (fun ω => Real.exp (θ * continuumValue d Z B PB 1 0 ω)) PW) ∧
    (∀ T : ℝ, 0 < T → ∀ x : Space d, ∀ p : ℝ, 0 < p →
      Integrable (fun ω => continuumValue d Z B PB T x ω ^ p) PW ∧
      Integrable (fun ω => continuumValue d Z B PB 1 0 ω ^ p) PW ∧
      ∫ ω, continuumValue d Z B PB T x ω ^ p ∂PW =
        T ^ (p * (4 - (d : ℝ)) / 4) *
          ∫ ω, continuumValue d Z B PB 1 0 ω ^ p ∂PW ∧
      0 < ∫ ω, continuumValue d Z B PB 1 0 ω ^ p ∂PW) := by
  obtain ⟨θ, hθ, hM, hexp'⟩ := hexp
  refine ⟨clause1_of_continuous d ν2 W PW hW Z hZmod hZcont B PB hmeas hlaw,
    ⟨θ, hθ, hM, hexp'⟩, ?_⟩
  intro T hT x p hp
  obtain ⟨h1, h2, h3⟩ := hmom T hT x p hp
  exact ⟨h1, h2, integral_rpow_scaled_of_map_eq_base PW
    (fun T ω => continuumValue d Z B PB T x ω) (fun ω => continuumValue d Z B PB 1 0 ω) d hT p
    (hmeas T hT x) (hmeas 1 zero_lt_one 0) (hlaw T hT x), h3⟩

end Sandpile.Support
