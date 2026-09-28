import Sandpile.Support.ManyLStep3

/-!
# The band parameters and the four Step-1 estimates

Step 1 of the proof of `thm:dgt4-many-limits` (`sandpile.tex:5930-6051`), named. The paper
constructs a one-site law with a band structure: parameters `ℓ_0 < ℓ_1 < 1`, `1/ℓ_1 < λ_0 <
1/ℓ_0`, `A > 1` with `1 - λ_0 ℓ_1 + (λ_0 - 1)/A < 0`, exponents `ϑ_k ∈ [1,2]` with
subsequential limit set `[1,2]`, levels `a_k = A^k`, weights `ω_k = c_0 e^{-a_k}`, and variables
`B_k ∈ [ℓ_1,1]` with `P(B_k > y) = ((1-y)/(1-ℓ_1))^{ϑ_k}`. The law `ζ(0) = μ + η + Γ` of
`eq:dgt4-band-law` is a mixture of the atoms `-a_k B_k` with weights `ω_k` plus a `Γ` with
density proportional to `e^{-x^4}`, shifted to mean zero. `BandParameters` packages the constants
and hypotheses, with `BandParameters.level` and `BandParameters.weight` giving `a_k` and `ω_k`.

Step 1 establishes, for this law, the tail order `eq:dgt4-band-tail-order` (`BandProfile`), the
density bound `eq:dgt4-band-density` (`BandDensity`), and the two isolation estimates
`eq:dgt4-band-upper-isolation` (`BandUpperIsolation`) and `eq:dgt4-band-lower-isolation`
(`BandLowerIsolation`), bundled as `BandLawProfile`. Step 2 (`sandpile.tex:6051-6275`) then adds
the origin-fixed concentration `eq:dgt4-band-origin-fixed-concentration` and the origin-fixed
lower tail `eq:dgt4-band-origin-fixed-lower-tail`, and derives the two band limits.

`BandLawProfile` is a statement about the constructed law only, so it is the honest interface
between Step 1 and the rest of the proof: later files consume the four estimates through this
predicate without depending on the mixture construction itself.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile

/-- The band parameters of Step 1 of `thm:dgt4-many-limits`
(`sandpile.tex:5925-5960`): the levels `a_k = A^k`, the weights
`ω_k = c_0 e^{-a_k}`, the exponents `ϑ_k ∈ [1,2]`, and the constants
`ℓ_1 ∈ (0,1)`, `λ_0 > 0`. -/
structure BandParameters where
  /-- the level ratio `A > 1` -/
  A : ℝ
  /-- the weight constant `c_0 > 0` -/
  c0 : ℝ
  /-- the lower band edge `ℓ_1 ∈ (0,1)` -/
  l1 : ℝ
  /-- the exponential rate `λ_0 > 0` -/
  lam0 : ℝ
  /-- the exponents `ϑ_k ∈ [1,2]` -/
  theta : ℕ → ℝ
  hA : 1 < A
  hc0 : 0 < c0
  hl1 : l1 ∈ Set.Ioo (0 : ℝ) 1
  hlam0 : 0 < lam0
  htheta : ∀ k : ℕ, theta k ∈ Set.Icc (1 : ℝ) 2

/-- The level `a_k = A^k` of `sandpile.tex:5941`. -/
noncomputable def BandParameters.level (P : BandParameters) (k : ℕ) : ℝ := P.A ^ k

/-- The weight `ω_k = c_0 e^{-a_k}` of `sandpile.tex:5942`. -/
noncomputable def BandParameters.weight (P : BandParameters) (k : ℕ) : ℝ :=
  P.c0 * Real.exp (-(P.level k))

/-- The band profile `eq:dgt4-band-profile` (`sandpile.tex:6003-6010`): uniformly
over `0 ≤ r ≤ 1`, the tail of `-ζ(0)` at the level `a_k - (1-ℓ_1)a_k r` is
`ω_k r^{ϑ_k}` to leading order. -/
def BandProfile (P : BandParameters) (ν : Measure ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 →
    |(ν {z | -(z) > P.level k - (1 - P.l1) * P.level k * r}).toReal / P.weight k -
      r ^ P.theta k| ≤ η

/-- The density bound `eq:dgt4-band-density` (`sandpile.tex:6012-6021`): the
density of `-ζ(0)` is at most `C ω_k/a_k` on the band `(ℓ_1 a_k, a_k]`.

The law `ν` is the law of `ζ(0)`, so the mass that `-ζ(0)` puts on `[t,t+ε]` is
`ν [-(t+ε),-t]`; the bound on the difference quotients of `t ↦ P(-ζ(0) ≤ t)`
over the band is therefore the bound below.  Bounding difference quotients
rather than a derivative avoids assuming that `ν` has a density. -/
def BandDensity (P : BandParameters) (ν : Measure ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop, ∀ t : ℝ,
    P.l1 * P.level k < t → t ≤ P.level k →
      ∀ ε : ℝ, 0 < ε →
        (ν (Set.Icc (-(t + ε)) (-t))).toReal / ε ≤ C * P.weight k / P.level k

/-- The upper isolation `eq:dgt4-band-upper-isolation` (`sandpile.tex:6023-6030`):
the mass above `a_k` and the excess above `a_k` are both `o(ω_k)`. -/
def BandUpperIsolation (P : BandParameters) (ν : Measure ℝ) : Prop :=
  Tendsto (fun k : ℕ => (ν {z | -(z) > P.level k}).toReal / P.weight k) atTop (𝓝 0) ∧
  Tendsto (fun k : ℕ =>
      (∫ z, max (-(z) - P.level k) 0 ∂ν) / (P.weight k * (1 - P.l1) * P.level k))
    atTop (𝓝 0)

/-- The lower isolation `eq:dgt4-band-lower-isolation` (`sandpile.tex:6032-6045`):
the exponentially weighted mass below `ℓ_1 a_k` is `o(ω_k)`. -/
def BandLowerIsolation (P : BandParameters) (ν : Measure ℝ) : Prop :=
  Tendsto (fun k : ℕ =>
      Real.exp (-(P.lam0 * P.l1 * P.level k)) *
        (∫ z, Real.exp (-(P.lam0 * z)) *
          Set.indicator {z | -(z) ≤ P.l1 * P.level k} (fun _ => (1 : ℝ)) z ∂ν) /
        P.weight k) atTop (𝓝 0)

/-- The Step-1 output of `thm:dgt4-many-limits` (`sandpile.tex:5925-6046`): a law
with the band structure and the four estimates. -/
def BandLawProfile (P : BandParameters) (ν : Measure ℝ) : Prop :=
  BandProfile P ν ∧ BandDensity P ν ∧ BandUpperIsolation P ν ∧ BandLowerIsolation P ν

end Sandpile.Support
