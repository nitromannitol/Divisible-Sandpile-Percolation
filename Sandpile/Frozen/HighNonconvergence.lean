/-
Theorem 1.3(iii)(d) of sandpile.tex, frozen.  `sandpile.tex:286-293`
(label `thm:main-explosion`, part (iii)(d)):

  "There is an i.i.d.\ scenery $(\zeta(x))_{x\in\Z^d}$ whose one-site law has
   mean zero, variance one, a strictly positive smooth density, and an
   exponential moment such that, for every $T>0$ and $s>(d-4)/2$, the rescaled
   fluctuations
   $R^{(d-4)/2}\left(u_{\lfloor TR^2\rfloor}-\E u_{\lfloor TR^2\rfloor}(0)\right)^{(R)}$
   have uncountably many distinct subsequential limits in $H^{-s}_{\rm loc}(\R^d)$
   as $R\to\infty$; in particular they do not converge."

Modelling choices.  The scenery law is produced by the existential, so it
carries no exponential-moment hypothesis: the preamble of Theorem 1.3 assumes
that moment only in parts (i), (ii), and (iii)(a)-(b), and here it is part of the
conclusion.  A strictly positive smooth density is a smooth everywhere-positive
`p` with `ν` the volume measure weighted by `p`.  The rescaled fluctuation
functional is `diffusiveFluctuation`.  Every subsequential limit produced by
`thm:dgt4-many-limits` is a centred Gaussian random distribution, hence
determined by its covariance, so "uncountably many distinct subsequential limits"
is transcribed as: an uncountable index set `I`, an assignment `K` of a
covariance to each index, and, for each index, a sequence `R_k\to\infty` along
which every pairing converges in distribution to the centred Gaussian of the
matching variance, together with the clause that distinct indices give distinct
limits, namely that for `\kappa\ne\kappa'` in `I` there is a test function `\phi`
at which the two limit laws `gaussianReal 0 (K \kappa \phi \phi)^+` and
`gaussianReal 0 (K \kappa' \phi \phi)^+` are different measures.  Distinctness
is stated of the limit laws themselves, which is what the paper counts: a limit
reads `K \kappa` only through `Real.toNNReal (K \kappa \phi \phi)` at test
functions, so it is those values, and not the covariance functions, that decide
whether two indices carry the same limit.  Tightness of the norms, the second clause of
`TendstoInNegSobolev`, holds for the whole family and is stated once.  The
sharper `thm:dgt4-many-limits` identifies `I=[3/2,2]` and
`K \kappa = weightedMembraneCov d 1 \kappa T`, but Theorem 1.3 asserts only
existence, so `I` and `K` are existentially quantified here.  The final clause is
the paper's "in particular they do not converge", the negation of
`TendstoInNegSobolev` for any covariance.  The instance binder
`∀ [_ : IsProbabilityMeasure ν]` after the positive conjunct
`IsProbabilityMeasure ν` only makes that same fact available to the elaborator
inside the body, where `centeredMassLaw d ν` must be known to be a probability
measure; it adds no hypothesis and removes none.
-/
import Sandpile.Law
import Sandpile.Continuum.Membrane
import Sandpile.Support.ExplFluctuation
import Sandpile.External.ContinuumBesovTightness
import Sandpile.External.LocalCLT
import Sandpile.Support.Dgt4AManyLimitsAssembly
import Sandpile.Support.ExplHighNonconvergence
import Sandpile.External.GreenBoundsHighProved
import Sandpile.External.HeatKernelBoundsProved
import Sandpile.External.IntersectionSecondMomentProved

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.high_nonconvergence
    (hLocalCLT : Sandpile.External.LocalCLT)
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ)) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ [_i : IsProbabilityMeasure ν],
      (∫ z, z ∂ν = 0) ∧ variance id ν = 1 ∧
      (∃ p : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ (∀ z : ℝ, 0 < p z) ∧
        ν = volume.withDensity fun z => ENNReal.ofReal (p z)) ∧
      (∃ θ₀ : ℝ, 0 < θ₀ ∧ Integrable (fun z => Real.exp (θ₀ * |z|)) ν) ∧
      ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
        Sandpile.Continuum.TightInNegSobolev d s (Sandpile.centeredMassLaw d ν)
            (Sandpile.Continuum.diffusiveFluctuation (Sandpile.centeredMassLaw d ν) T) ∧
          (∃ (I : Set ℝ) (K : ℝ → (Sandpile.Continuum.Space d → ℝ) →
              (Sandpile.Continuum.Space d → ℝ) → ℝ),
            ¬ I.Countable ∧
              (∀ κ ∈ I, ∀ κ' ∈ I, κ ≠ κ' →
                ∃ φ : Sandpile.Continuum.Space d → ℝ,
                  Sandpile.Continuum.IsTestFn Set.univ φ ∧
                    gaussianReal 0 (Real.toNNReal (K κ φ φ)) ≠
                      gaussianReal 0 (Real.toNNReal (K κ' φ φ))) ∧
              ∀ κ ∈ I, ∃ Rs : ℕ → ℝ, Tendsto Rs atTop atTop ∧
                ∀ φ : Sandpile.Continuum.Space d → ℝ,
                  Sandpile.Continuum.IsTestFn Set.univ φ →
                    TendstoInDistribution
                      (fun (k : ℕ) (σ : Sandpile.Site d → ℝ) =>
                        Sandpile.Continuum.diffusiveFluctuation
                          (Sandpile.centeredMassLaw d ν) T (Rs k) σ φ)
                      atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
                      (gaussianReal 0 (Real.toNNReal (K κ φ φ)))) ∧
          ¬ ∃ K : (Sandpile.Continuum.Space d → ℝ) →
              (Sandpile.Continuum.Space d → ℝ) → ℝ,
            Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
              (Sandpile.Continuum.diffusiveFluctuation (Sandpile.centeredMassLaw d ν) T) K
-- FROZEN-STATEMENT-END
:=
  Sandpile.Support.high_nonconvergence_of_many_limits Sandpile.External.heatKernelBounds
    Sandpile.External.greenBoundsHigh hLocalCLT hBesov hd
    (Sandpile.Support.dgt4_many_limits_assembled d hd Sandpile.External.greenBoundsHigh
      Sandpile.External.intersectionSecondMoment
      Sandpile.External.heatKernelBounds hLocalCLT hBesov)
