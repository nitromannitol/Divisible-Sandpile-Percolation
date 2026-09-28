import Sandpile.Law
import Sandpile.Continuum.Membrane
import Sandpile.Support.ExplFluctuation
import Sandpile.External.ContinuumBesovTightness
import Sandpile.External.LocalCLT
import Sandpile.External.LocalCLTProved
import Sandpile.Support.Dgt4AManyLimitsAssembly
import Sandpile.Support.ExplHighNonconvergence
import Sandpile.External.GreenBoundsHighProved
import Sandpile.External.HeatKernelBoundsProved
import Sandpile.External.IntersectionSecondMomentProved

/-!
# High-dimensional non-convergence, frozen

Theorem 1.3(iii)(d) of `sandpile.tex`, frozen (`sandpile.tex:286-293`, label
`thm:main-explosion`, part (iii)(d)): there is an i.i.d. scenery whose one-site law has mean
zero, variance one, a strictly positive smooth density, and an exponential moment such that, for
every `T > 0` and `s > (d-4)/2`, the rescaled fluctuations
`R^{(d-4)/2}(u_{⌊TR²⌋} - E u_{⌊TR²⌋}(0))^{(R)}` have uncountably many distinct subsequential
limits in `H^{-s}_loc(ℝ^d)` as `R → ∞`, and in particular do not converge. The rescaled
fluctuation functional is `diffusiveFluctuation`; since every subsequential limit is a centred
Gaussian random distribution determined by its covariance, "uncountably many distinct limits" is
transcribed as an uncountable index set `I`, a covariance assignment `K`, convergence along a
sequence `R_k → ∞` for each index, and distinctness of the limit laws `gaussianReal 0 (K κ φ φ)⁺`
across indices at some test function. The sharper `thm:dgt4-many-limits` identifies `I = [3/2,2]`
and `K κ = weightedMembraneCov d 1 κ T`, but this existence statement leaves `I` and `K`
existentially quantified, and the final clause negates `TendstoInNegSobolev` for every covariance.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.high_nonconvergence
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
    Sandpile.External.greenBoundsHigh Sandpile.External.localCLT hBesov hd
    (Sandpile.Support.dgt4_many_limits_assembled d hd Sandpile.External.greenBoundsHigh
      Sandpile.External.intersectionSecondMoment
      Sandpile.External.heatKernelBounds Sandpile.External.localCLT hBesov)
