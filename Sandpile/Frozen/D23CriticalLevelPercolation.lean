import Sandpile.Law
import Sandpile.External.LocalCLTProved
import Sandpile.Support.D23PlaneSite
import Sandpile.Support.D23Final

/-! # Critical Level-Set Percolation in Dimensions 2 and 3

Theorem of Section 4 of sandpile.tex, frozen.  `sandpile.tex:2596-2611`
(label `thm:d23-critical-level-percolation`):

  "[Critical level-set percolation]  Fix $d\in\{2,3\}$, $\nu_{0}>0$,
   $\theta_{0}>0$, and $K_{0}<\infty$.  There are
   $c=c(d,\nu_{0},\theta_{0},K_{0})>0$ and
   $t_0=t_0(d,\nu_{0},\theta_{0},K_{0})<\infty$ such that, for every mean-zero
   i.i.d.\ field $(\zeta(x))_{x\in\Z^d}$ satisfying $\Var(\zeta(0))\geq\nu_{0}^2$,
   $\E e^{\theta_{0}|\zeta(0)|}\leq K_{0}$, and every $t\geq t_0$, the planar set
   $\{x:u_t(x)>c t^{(4-d)/4}\}$ contains an infinite nearest-neighbor component
   almost surely, where $x$ ranges over $\Z^2$ if $d=2$, and over
   $\Z^2\times\{0\}$ if $d=3$."

The scenery `ζ` is carried by its one-site law `ν`, and the field itself by
`centeredMassLaw d ν`, the law of `σ = 1 + 2dζ`.  `c` and `t₀` are bound after
`d, ν₀, θ₀, K₀` and before the law, as the paper orders them, so they are
uniform over every law satisfying the two bounds.

The component is a component of the plane, not of `ℤ^d`: for `d = 3` the paper
asks for an infinite nearest-neighbour component of the level set inside the
slab `ℤ² × {0}`, which is a stronger statement than an infinite component of
the level set in `ℤ³`.  So the level set is pulled back along `planeSite`, the
embedding `ℤ² → ℤ^d` sending `(z₀, z₁)` to the site with those first two
coordinates and all remaining coordinates zero, and the conclusion is
`HasInfiniteComponent` of a subset of `Site 2`, whose edges are the
nearest-neighbour edges of `ℤ²`.  For `d = 2` the embedding is the identity, so
the single statement covers both dimensions.

The exponential-moment bound is stated together with the integrability of the
exponential, as the paper's `K₀ < ∞` requires: the Bochner integral of a
non-integrable nonnegative function is zero, so the bound alone would hold for
every law with no exponential moment.
-/

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d23_critical_level_percolation
    (hLSS : Sandpile.External.LSSDomination)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hOcc : Sandpile.External.BallOccupationDensity)
    (hCube : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
          LatticeProb.HasInfiniteComponent
            {z : Sandpile.Site 2 | c * (t : ℝ) ^ ((4 - (d : ℝ)) / 4) <
              Sandpile.odometer σ t (Sandpile.planeSite z)}
-- FROZEN-STATEMENT-END
:=
  Sandpile.Support.d23_critical_level_percolation_assembled d hd hLSS hRSWc hPitt hOcc
    Sandpile.External.localCLT hCube ν₀ θ₀ K₀ hν₀ hθ₀
