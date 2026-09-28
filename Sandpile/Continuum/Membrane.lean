import Sandpile.Continuum.Sobolev
import Mathlib

/-!
# Continuum membrane fields and convergence in negative Sobolev norms

`weightedMembraneCov` is the covariance of the power-weighted continuum membrane field
`ℋ_{κ,T}` of `eq:power-weighted-continuum-membrane`, a real-space double time integral of two
test functions against the Brownian heat kernel; `κ = 0` recovers the finite-time membrane field
`𝒢_{d,T}`.  `membraneCov4` is the Fourier-space covariance of the four-dimensional limit field
`𝒢_4`, obtained by letting `T → ∞` in the same computation, since the real-space kernel diverges
in that limit; `omegaRep` and `omegaMembraneCov4` record the representative of a distribution
modulo additive constants after subtracting a fixed averaging density `ω`.
`TendstoInNegSobolev` packages convergence to a limiting field in `H^{-s}_loc(ℝ^d)` as
convergence in distribution of every finite-dimensional pairing together with tightness of the
`H^{-s}` norms on bounded domains.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal FourierTransform

namespace Sandpile.Continuum

/-- The covariance of the time-weighted continuum membrane field `ℋ_{κ,T}` with
scenery variance `ν2`.  `κ = 0` is the finite-time membrane field `𝒢_{d,T}`. -/
noncomputable def weightedMembraneCov (d : ℕ) (ν2 κ T : ℝ) (φ ψ : Space d → ℝ) : ℝ :=
  ν2 * ∫ x : Space d, ∫ y : Space d, φ x * ψ y *
    (∫ r in (0 : ℝ)..T, ∫ r' in (0 : ℝ)..T,
      (1 - r / T) ^ κ * (1 - r' / T) ^ κ * heatKernelBM d (r + r') x y)

/-- The covariance of the four-dimensional continuum membrane model `𝒢_4`,
modulo additive constants, with scenery variance `ν2`. -/
noncomputable def membraneCov4 (ν2 : ℝ) (φ ψ : Space 4 → ℝ) : ℝ :=
  64 * ν2 * ∫ ξ : Space 4,
    (𝓕 (fun x => (φ x : ℂ)) ξ * (starRingEnd ℂ) (𝓕 (fun x => (ψ x : ℂ)) ξ) /
      ((2 * Real.pi * ‖ξ‖ : ℝ) ^ 4 : ℂ)).re

/-- `F^ω(φ) = F(φ - ω ∫_D φ)`: the representative on `D` of a distribution modulo
constants whose `ω`-average is zero (`eq:d4-omega-representative`). -/
noncomputable def omegaRep {d : ℕ} (D : Set (Space d)) (w : Space d → ℝ)
    (F : (Space d → ℝ) → ℝ) (φ : Space d → ℝ) : ℝ :=
  F (fun x => φ x - w x * ∫ y in D, φ y)

/-- The `ω`-densities of `eq:d4-omega-representative`: `ω ∈ C_c^∞(D)`, `ω ≥ 0`,
`∫_D ω = 1`. -/
def IsAveragingDensity {d : ℕ} (D : Set (Space d)) (w : Space d → ℝ) : Prop :=
  IsTestFn D w ∧ (∀ x, 0 ≤ w x) ∧ ∫ x in D, w x = 1

/-- The family `F R` of random functionals is tight in `H^{-s}_loc(ℝ^d)`. -/
def TightInNegSobolev {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (s : ℝ)
    (P : Measure Ω) (F : ℝ → Ω → (Space d → ℝ) → ℝ) : Prop :=
  ∀ D : Set (Space d), IsDomain D → ∀ ε : ℝ, 0 < ε →
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
      P {ω | M < negSobolevNorm d s D (F R ω)} ≤ ENNReal.ofReal ε

/-- `F R ⟹ 𝔉 in H^{-s}_loc(ℝ^d)`, where `𝔉` is the centred Gaussian random
distribution with covariance `K`: every pairing converges in distribution to the
centred Gaussian of the matching variance, and the norms are tight. -/
def TendstoInNegSobolev {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (s : ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ → Ω → (Space d → ℝ) → ℝ)
    (K : (Space d → ℝ) → (Space d → ℝ) → ℝ) : Prop :=
  (∀ φ : Space d → ℝ, IsTestFn Set.univ φ →
      TendstoInDistribution (fun R : ℝ => fun ω : Ω => F R ω φ) atTop (id : ℝ → ℝ)
        (fun _ => P) (gaussianReal 0 (Real.toNNReal (K φ φ)))) ∧
    TightInNegSobolev d s P F

end Sandpile.Continuum

namespace Sandpile

/-- The covariance of `𝒢_4^ω`, the `ω`-representative of the four-dimensional
continuum membrane model: `Cov(𝒢_4^ω(φ), 𝒢_4^ω(ψ)) = Cov(𝒢_4(φ̃), 𝒢_4(ψ̃))`,
where `φ̃ = φ - ω ∫_D φ` is the shift of `eq:d4-omega-representative`
(`sandpile.tex:3320-3328` and the definition it refers to). -/
noncomputable def omegaMembraneCov4 (D : Set (Sandpile.Continuum.Space 4))
    (w : Sandpile.Continuum.Space 4 → ℝ) (ν2 : ℝ)
    (φ ψ : Sandpile.Continuum.Space 4 → ℝ) : ℝ :=
  Sandpile.Continuum.omegaRep D w
    (fun χ => Sandpile.Continuum.omegaRep D w
      (Sandpile.Continuum.membraneCov4 ν2 χ) ψ) φ

end Sandpile
