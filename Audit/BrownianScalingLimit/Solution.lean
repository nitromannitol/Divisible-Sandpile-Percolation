import Mathlib
import Sandpile.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: BrownianScalingLimit

The challenge module `Audit/BrownianScalingLimit/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Sandpile.brownian_scaling_limit` through the bridges in
`Audit/Support/Bridge.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

/-- Theorem 1.3(i)(b) (`thm:main-explosion`). -/
theorem brownian_scaling_limit
    (hLocalCLT : External.LocalCLT)
    (hStab : External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (Continuum.Space d → ℝ) → Ω → ℝ)
    (hW : Continuum.IsWhiteNoise d W P)
    (Z : ℝ → Continuum.Space d → Ω → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Continuum.Space d),
      Z t x =ᵐ[P] fun ω =>
        Continuum.gaussianPotential d (variance id ν) W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × Continuum.Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Continuum.Space d))))
    (hZgrow : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P, ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Continuum.Space d)),
        |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k)
    (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (B : Continuum.Space d → ℝ≥0 → Ω' → Continuum.Space d)
    (hB : ∀ x : Continuum.Space d, Continuum.IsBrownian d x (B x) P')
    (hBc : ∀ (y : Continuum.Space d) (ω : Ω'), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (T : ℝ) (hT : 0 < T) :
    (∀ (m : ℕ) (x : Fin m → Continuum.Space d),
        TendstoInDistribution
          (fun (R : ℝ) (σ : Site d → ℝ) (j : Fin m) =>
            Continuum.multilinearInterp R
              (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) (x j))
          atTop
          (fun (ω : Ω) (j : Fin m) =>
            Continuum.brownianValue (B (x j)) P'
              (fun t y => Z t y ω)
              T (x j))
          (fun _ => centeredMassLaw d ν) P) ∧
      ∀ K : Set (Continuum.Space d), IsCompact K →
        (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
          centeredMassLaw d ν
              {σ | ∃ z ∈ K, M < |Continuum.multilinearInterp R
                (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z|} ≤
            ENNReal.ofReal ε) ∧
        (∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
          centeredMassLaw d ν
              {σ | ∃ z ∈ K, ∃ z' ∈ K, dist z z' < δ ∧
                η < |Continuum.multilinearInterp R
                    (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z -
                  Continuum.multilinearInterp R
                    (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z'|} ≤
            ENNReal.ofReal ε) := by
  rw [Bridge.odometer_eq]
  exact Sandpile.brownian_scaling_limit (Bridge.localCLT hLocalCLT)
    (Bridge.continuumStoppingStability hStab) d hd hd3 ν hmean hvar hvar' θ₀ hθ₀ hexp Ω P W
    (Bridge.isWhiteNoise d W P hW) Z hZmod hZcont hZgrow Ω' P' B
    (fun x => (Bridge.isBrownian_iff _ _ _ _).1 (hB x)) hBc hBm T hT

end SandpileAudit
