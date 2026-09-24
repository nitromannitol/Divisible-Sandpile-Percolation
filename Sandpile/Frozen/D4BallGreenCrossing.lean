/-
Theorem of Section 5 of sandpile.tex, frozen.  `sandpile.tex:3548-3569`
(label `thm:d4-ball-green-crossing`):

  "[Uniform ball-killed Green crossing estimate]  Fix $\nu_{0}>0$,
   $\theta_{0}>0$, $K_{0}<\infty$, and $\vartheta\geq1$.  For every
   $\varepsilon>0$ there are
   $\gamma=\gamma(\varepsilon,\vartheta,\nu_{0},\theta_{0},K_{0})>0$,
   $C=C(\varepsilon,\vartheta,\nu_{0},\theta_{0},K_{0})<\infty$, and
   $r_0=r_0(\varepsilon,\vartheta,\nu_{0},\theta_{0},K_{0})<\infty$ such that,
   for every mean-zero i.i.d.\ law satisfying
   $\Var(\zeta(0))\geq\nu_{0}^2$, $\E e^{\theta_{0}|\zeta(0)|}\leq K_{0}$,
   and every integer $r\geq r_0$,
   \[
     \sup_{x\in\Z^4}\P\left(\{z\in R_{\vartheta,r}(x):
     \mathcal B_r(z)\leq-\varepsilon\log r\}\ \textup{contains a
     $\ast$-connected top-bottom crossing of }R_{\vartheta,r}(x)\right)
     \leq C(\log r)^3r^{-\gamma}\, .
   \]"

Modelling.  The statement is about the scenery alone, so the field is
`LatticeProb.iidLaw 4 ν` with one-site law `ν`; `Var(ζ(0)) ≥ ν₀²` is written
with `evariance` in `ℝ≥0∞`, and the exponential moment as an integral bound.

The objects of the running text are transcribed in
`Sandpile/Support/BallCrossingDefinitions.lean`:

- `ballCube x L` is `Q(x,L) = {y ∈ ℤ⁴ : max_i |y_i - x_i| ≤ L}`
  (`sandpile.tex:680-682`).
- `ballGreenField r ζ z` is `𝓑_r(z) = ∑_{u∈ℤ⁴} g^{Q(0,r)}(0,u) ζ(z+u)` of
  `eq:d4-ball-green-field` (`sandpile.tex:3423-3426`), with `g^D` the killed
  Green kernel `Sandpile.killedGreen` of `eq:killed-walk-notation`.  The sum is
  a `tsum`, and no junk value is reached: `g^{Q(0,r)}(0,·)` vanishes off the
  finite set `Q(0,r)`, so the family is finitely supported and summable.
- `ballRect ϑ r x` is
  `R_{ϑ,r}(x) = {x+(i,j,0,0) : 0 ≤ i ≤ ⌊ϑr⌋, 0 ≤ j ≤ r}`
  (`sandpile.tex:3436-3440`), written as the set of `z ∈ ℤ⁴` whose last two
  coordinates agree with those of `x` and whose first two lie in the stated
  ranges relative to `x`.

`∗`-connectivity is `starGraph`: distinct sites of `ℤ⁴` which agree in the last
two coordinates and differ by at most one in each of the first two, that is
`|z-w|_∞ = 1` inside a common translate `x+Π` of the coordinate plane
`Π = ℤ²×{0}²` of `eq:d4-coordinate-plane` (`sandpile.tex:3432-3440`).  The
condition that the last two coordinates agree confines the graph to the
translates of `Π`, which is the paper's vertex set.

A `∗`-connected top-bottom crossing of `R_{ϑ,r}(x)` inside a set `S` is
`HasStarTopBottomCrossing`: a nonempty list of sites, every one of them in both
`S` and `R_{ϑ,r}(x)`, consecutive entries `∗`-adjacent, the first entry on the
top edge `j = r` and the last on the bottom edge `j = 0`.  Repetitions are not
forbidden, since a walk from the top edge to the bottom edge inside a set
contains a repetition-free one, so the two readings define the same event.

Quantifier order is the paper's: `ν₀, θ₀, K₀, ϑ` first, then `ε`, then
`γ, C, r₀` depending on all of them, then the law, then `r ≥ r₀`.  The
supremum over `x` is written as a universally quantified `x` inside the bound,
the same statement without an `sSup` junk value.  The threshold `r₀` is a
natural number, which is the paper's "every integer `r ≥ r_0`" and keeps
`log r` and `r^{-γ}` away from their values at `r = 0`.

The exponential-moment bound is stated together with the integrability of the
exponential, as the paper's `K₀ < ∞` requires: the Bochner integral of a
non-integrable nonnegative function is zero, so the bound alone would hold for
every law with no exponential moment.

The proof uses the planar RSW theorem of Kohler-Schindler–Tassion (cited at
`sandpile.tex:400,2064,2218,2235`; dimensions two through four are placed in the
RSW framework at `sandpile.tex:661-663`) for the rectangle extension of the
Gaussian far field, so it enters as the explicit hypothesis `hRSW`.
-/
import Sandpile.Support.BallCrossingDefinitions
import Sandpile.Support.D4CrossingAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal



-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_ball_green_crossing
    (hBallGreen : Sandpile.External.BallGreenBounds)
    (hRSW : Sandpile.External.PlanarRSW)
    (ν₀ θ₀ K₀ ϑ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) (hϑ : 1 ≤ ϑ) :
    ∀ ε : ℝ, 0 < ε → ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∃ r₀ : ℕ,
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ r : ℕ, r₀ ≤ r → ∀ x : Sandpile.Site 4,
          LatticeProb.iidLaw 4 ν
              {ζ | Sandpile.HasStarTopBottomCrossing ϑ r x
                {z | Sandpile.ballGreenField r ζ z ≤ -(ε * Real.log r)}} ≤
            ENNReal.ofReal (C * (Real.log r) ^ 3 * (r : ℝ) ^ (-γ))
-- FROZEN-STATEMENT-END
:= by
  exact d4_ball_green_crossing_of_rsw hBallGreen hRSW ν₀ θ₀ K₀ ϑ hν₀ hθ₀ hϑ
