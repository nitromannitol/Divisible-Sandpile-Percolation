/-
Theorem 1.1 of sandpile.tex, frozen.  `sandpile.tex:95-103`
(label `thm:main-nontriviality`):

  "Let $d\geq2$, let $(\mu_\rho)_{\rho\in(0,1]}$ be a family of laws with mean
   $\E_{\mu_\rho}\sigma(0)=\rho$, and let the masses be i.i.d. with law
   $\mu_\rho$.  Suppose there are $\rho_0\in(0,1)$, $\nu_0>0$, $\theta_0>0$, and
   $K_0<\infty$ such that [uniform variance and exponential-moment bounds].
   Then there is $\rho_+\in[\rho_0,1)$ such that $\mathcal T^{(\rho)}$ contains
   an infinite nearest-neighbor component almost surely for every
   $\rho\in(\rho_+,1)$."

The threshold `ρ₊` is bound after the family, so it is a genuine constant of
the model and not a function of `ρ`.  The exponential-moment bound is stated
together with the integrability of the exponential, as the paper's `K₀ < ∞`
requires: the Bochner integral of a non-integrable nonnegative function is zero,
so the bound alone would hold for every law with no exponential moment.

The proof reduces to Theorem 1.2, whose own proof carries the cited inputs
`PlanarRSW`, `LSSDomination` and `ExteriorBoundaryConnected`; those three inputs
are hypotheses here.

The threshold `ρ₊`.  The paper writes `ρ₊ = ρ₊(d,(μ_ρ)) ∈ [ρ₀,1)`, and the two
halves of that phrase pull in different directions: the annotation names `d` and
the family, while the membership `ρ₀ ≤ ρ₊` ties the threshold to the witness
`ρ₀`, since for a valid witness above a witness-independent `ρ₊` the membership
would fail.  The threshold is therefore bound here after `ρ₀`, `ν₀`, `θ₀` and
`K₀`, which is the reading under which both halves hold.  What the theorem's
content rests on is the other side of the binding, and it is what this statement
asserts: `ρ₊` is fixed before the density `ρ`, so one threshold serves every
`ρ ∈ (ρ₊,1)`.
-/
import Sandpile.Law
import Sandpile.External.BallGreenBounds
import Sandpile.External.PlanarRSW
import Sandpile.External.LSSDomination
import Sandpile.External.ExteriorBoundaryConnected
import Sandpile.External.GreenBoundsHighProved
import Sandpile.External.VarianceScaleProved
import Sandpile.Support.ExplNontriviality

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.percolation_below_criticality
    (hRSW : Sandpile.External.PlanarRSW)
    (hLSS : Sandpile.External.LSSDomination)
    (hBoundary : Sandpile.External.ExteriorBoundaryConnected)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hOcc : Sandpile.External.BallOccupationDensity)
    (hCube : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (μ : ℝ → Measure ℝ) (hprob : ∀ ρ, IsProbabilityMeasure (μ ρ))
    (hmean : ∀ ρ ∈ Set.Ioc (0 : ℝ) 1, ∫ s, s ∂(μ ρ) = ρ)
    (ρ₀ ν₀ θ₀ K₀ : ℝ) (hρ₀ : ρ₀ ∈ Set.Ioo (0 : ℝ) 1) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀)
    (hvar : ∀ ρ ∈ Set.Ico ρ₀ 1, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (μ ρ))
    (hexpint : ∀ ρ ∈ Set.Ico ρ₀ 1, Integrable (fun s => Real.exp (θ₀ * |s - ρ|)) (μ ρ))
    (hexp : ∀ ρ ∈ Set.Ico ρ₀ 1, ∫ s, Real.exp (θ₀ * |s - ρ|) ∂(μ ρ) ≤ K₀) :
    ∃ ρPlus ∈ Set.Ico ρ₀ 1, ∀ ρ ∈ Set.Ioo ρPlus 1,
      ∀ᵐ σ ∂(Sandpile.massLaw d (μ ρ)),
        Sandpile.HasInfiniteComponent (Sandpile.toppledSet σ)
-- FROZEN-STATEMENT-END
:= by
  exact Sandpile.Support.percolation_below_criticality_of_critical_levels d hd μ hprob hmean
    ρ₀ ν₀ θ₀ K₀ hρ₀ hθ₀ hvar hexpint hexp
    (Sandpile.Frozen.critical_level_percolation hRSW hLSS hBoundary
      hRSWc hPitt hOcc hCube d hd ν₀ θ₀ K₀ hν₀ hθ₀)
