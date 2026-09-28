import Sandpile.Law
import Sandpile.Support.Crit23Scale
import Sandpile.External.BallGreenBounds
import Sandpile.External.BallGreenBoundsProved
import Sandpile.External.GreenBoundsHighProved
import Sandpile.External.VarianceScaleProved
import Sandpile.External.PlanarRSW
import Sandpile.External.LSSDomination
import Sandpile.External.ExteriorBoundaryConnected
import Sandpile.External.LocalCLTProved
import Sandpile.Support.Crit23MainAssembly

/-!
# Critical-level percolation

Theorem 1.2 of sandpile.tex, frozen.  `sandpile.tex:113-126`
(label `thm:main-critical-level-percolation`):

  "Let $d\geq2$ and let $\nu_0>0$, $\theta_0>0$, and $K_0<\infty$.  There are
   $c=c(d,\nu_0,\theta_0,K_0)>0$ and $t_0=t_0(d,\nu_0,\theta_0,K_0)<\infty$ such
   that the following holds.  Suppose $(\sigma(x))_{x\in\Z^d}$ are i.i.d. with
   mean one, $\Var(\sigma(0))\geq\nu_0^2$ and $\E e^{\theta_0|\sigma(0)-1|}\leq K_0$.
   Then for every $t\geq t_0$ the level set $\{x : u_t(x) > c\,h(t)\}$, with
   $h(t)=t^{(4-d)/4}$ for $d\in\{2,3\}$, $\log t$ for $d=4$ and $(\log t)^{2/d}$
   for $d\geq5$, contains an infinite nearest-neighbor component almost surely."

`c` and `t₀` are bound after `d, ν₀, θ₀, K₀` and before the law, as the paper
orders them, so they are uniform over every law satisfying the hypotheses.  The
exponential-moment bound is stated together with the integrability of the
exponential, as the paper's `K₀ < ∞` requires: the Bochner integral of a
non-integrable nonnegative function is zero, so the bound alone would hold for
every law with no exponential moment.

The proof reduces to the three regime theorems of the paper, which carry the
cited inputs `PlanarRSW` and `LSSDomination` (dimensions two, three and four)
and `ExteriorBoundaryConnected` (dimensions five and higher); those three
inputs are hypotheses here, as the paper's proof reaches them through its
citations.  The `d ≥ 5` Green estimates and the variance-scale input are also
cited, but each is proved unconditionally in this repository
(`Sandpile.External.greenBoundsHigh`, `Sandpile.External.varianceScale`), so
neither is carried here as an explicit hypothesis.
-/

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.critical_level_percolation
    (hRSW : Sandpile.External.PlanarRSW)
    (hLSS : Sandpile.External.LSSDomination)
    (hBoundary : Sandpile.External.ExteriorBoundaryConnected)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hOcc : Sandpile.External.BallOccupationDensity)
    (hCube : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.massLaw d μ),
          Sandpile.HasInfiniteComponent
            {x | c * Sandpile.criticalScale d t < Sandpile.odometer σ t x}
-- FROZEN-STATEMENT-END
:= by
  exact critical_level_percolation_assembly Sandpile.External.ballGreenBounds
    Sandpile.External.greenBoundsHigh
    Sandpile.External.varianceScale hRSW hLSS
    hBoundary hRSWc hPitt hOcc Sandpile.External.localCLT hCube d hd ν₀ θ₀ K₀ hν₀ hθ₀
