/-
The continuum membrane fields of `sandpile.tex`,
`ssec:continuum-membrane-fields` (lines 954-1069), and what convergence to them
means.

  `𝒢_{d,T} = √Var(ζ(0)) ∫_0^T e^{rΔ/(2d)} 𝒲 dr`   (`eq:finite-time-continuum-membrane`)
  `ℋ_{κ,T} = √Var(ζ(0)) ∫_0^T (1 - r/T)^κ e^{rΔ/(2d)} 𝒲 dr`
                                        (`eq:power-weighted-continuum-membrane`)

Both are mean-zero Gaussian random distributions, so their laws are determined
by their covariances, and that is how they enter here.  Pairing the field with a
test function and using the semigroup identity
`∫ (e^{rΔ/(2d)}φ)(z)(e^{r'Δ/(2d)}ψ)(z) dz = ∫∫ φ(x) ψ(y) p^{BM}_{r+r'}(x,y) dx dy`
turns the covariance into `weightedMembraneCov`, a real-space double time
integral against the Brownian heat kernel.  Taking `κ = 0` gives `𝒢_{d,T}`.

For the four-dimensional membrane model `𝒢_4`, defined modulo additive
constants as the `T → ∞` limit, the same computation gives `membraneCov4`, in
Fourier form because the real-space kernel diverges: with `m_T(ξ) → 2d/|ξ|² = 8/|ξ|²`
in `eq:dgt4-finite-time-membrane-covariance`,

  `Cov(𝒢_4(φ), 𝒢_4(ψ)) = Var(ζ(0)) (2π)^{-4} ∫ φ̂(ξ) conj(ψ̂(ξ)) (8/|ξ|²)² dξ`.

Mathlib's `𝓕` uses the character `e^{-2πi⟪x,ξ⟫}`, so the paper's frequency is
`2π` times Mathlib's; substituting gives the form written below.

Convergence to such a field in `H^{-s}_loc(ℝ^d)` is recorded as two clauses:
convergence in distribution of every single pairing to the matching centred
Gaussian, and tightness of the `H^{-s}(D)` norms on every bounded domain.  The
fields are linear in the test function and the limit is Gaussian, so by the
Cramér-Wold device the first clause is exactly convergence of all
finite-dimensional laws; with the second it is exactly weak convergence in
`H^{-s}_loc(ℝ^d)`.
-/
import Sandpile.Continuum.Sobolev
import Mathlib

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
