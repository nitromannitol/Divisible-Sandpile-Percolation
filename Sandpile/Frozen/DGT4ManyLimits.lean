/-
Theorem 1.3(iii)(d) of sandpile.tex in sharper form, frozen.
`sandpile.tex:5971-5999` (label `thm:dgt4-many-limits`):

  "Let $d\geq5$.  There exists an i.i.d.\ scenery $(\zeta(x))_{x\in\Z^d}$ whose
   one-site law has mean zero, variance one, a strictly positive $C^\infty$
   density, and
     $\E e^{\theta|\zeta(0)|}<\infty$, $cr\leq-\log\P(\zeta(0)\leq-r)\leq Cr$
   for some $c,C,\theta>0$ and every sufficiently large $r$.
   There is a sequence $R_k\uparrow\infty$ such that, for every
   $\kappa\in[3/2,2]$, there are indices $k_\ell\uparrow\infty$ such that, for
   all $T>0$ and $s>(d-4)/2$,
     $R_{k_\ell}^{(d-4)/2}\left(u_{\lfloor TR_{k_\ell}^2\rfloor}
      -\E u_{\lfloor TR_{k_\ell}^2\rfloor}(0)\right)^{(R_{k_\ell})}
      \Longrightarrow\mathcal H_{\kappa,T}$ in $H^{-s}_{\rm loc}(\R^d)$.
   For $T>0$, the fields $\mathcal H_{\kappa,T}$ with $\kappa\in[3/2,2]$ have
   pairwise distinct laws."

Modelling decisions.

The scenery is produced, not quantified over: the whole statement is one
existential in the one-site law `ν`, followed by an existential in the sequence
`R_k` and, for each `κ`, in the extraction `k_ℓ`.  The order matters and is the
paper's: `R_k` is chosen before `κ`, and `k_ℓ` after it, so a single sequence
carries every subsequential limit.  `R_k ↑ ∞` is `StrictMono` together with
`Tendsto … atTop atTop`; `k_ℓ ↑ ∞` for a sequence of naturals is `StrictMono`,
which already forces divergence.

"A strictly positive `C^∞` density" is an explicit `f : ℝ → ℝ` with `0 < f z`
everywhere, `ContDiff ℝ ⊤ f`, and `ν = volume.withDensity (ofReal ∘ f)`.  "Mean
zero" and "variance one" are `∫ z, z ∂ν = 0` and `variance id ν = 1`.  The
exponential moment is `Integrable (fun z => exp (θ|z|)) ν` and the two-sided
linear log-tail bound is stated for all large `r` as `∀ᶠ r in atTop`, matching
"for every sufficiently large $r$"; the constants `c, C, θ` are bound by a
single existential inside the existential in `ν`, as the paper's "for some
$c,C,\theta>0$" requires.  `-log P(ζ(0) ≤ -r)` is `-Real.log` of the `toReal` of
the measure of `Set.Iic (-r)`; the bound `c r ≤ …` with `c > 0` and `r → ∞`
excludes the junk value `Real.log 0 = 0` from satisfying it vacuously.

Convergence along the subsequence is expressed by reparametrizing the family
`Sandpile.Continuum.TendstoInNegSobolev` expects: the family is indexed by a
real `L`, and its value at `L` is the rescaled odometer at `R_{k_{⌊L⌋}}`.  Since
the reindexed family is constant on each interval `[ℓ, ℓ+1)` and `⌊L⌋ → ∞` as
`L → ∞`, convergence along the `atTop` filter on `ℝ` is exactly convergence
along `ℓ → ∞`, so this is the paper's subsequential convergence and nothing
more; the tightness clause of `TendstoInNegSobolev` likewise ranges over the
subsequence only.

`ℋ_{κ,T}` enters through its covariance
`Sandpile.Continuum.weightedMembraneCov d (Var ζ(0)) κ T`, since it is a centred
Gaussian random distribution; `Var(ζ(0)) = 1` here.  Pairwise distinctness of the
laws is therefore stated as distinctness of the covariances: for `κ ≠ κ'` in
`[3/2,2]` there is a test function on which the two variances differ.  This is
what `sandpile.tex:983-987` proves, "for every $T>0$ and every nonzero
nonnegative test function $\varphi$, $\Var(\mathcal H_{\kappa,T}(\varphi))$ is
strictly decreasing in $\kappa$", and it is equivalent to distinctness of the
laws for centred Gaussian random distributions.

The scenery is written in the mass normalization: the integration variable is
`σ` with law `Sandpile.centeredMassLaw d ν`, so `ζ = (σ-1)/(2d)` has one-site
law `ν` and `u_n` is `Sandpile.odometer σ n`; `E u_n(0)` is
`Sandpile.meanOdometer`.
-/
import Sandpile.Law
import Sandpile.Walk
import Sandpile.Continuum.Membrane
import Sandpile.External.GreenBoundsHigh
import Sandpile.External.LocalCLT
import Sandpile.External.LocalCLTProved
import Sandpile.External.IntersectionSecondMomentProved
import Sandpile.Support.Dgt4AManyLimitsAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_many_limits
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ)) :
    ∃ ν : Measure ℝ, ∃ _ : IsProbabilityMeasure ν,
      ∫ z, z ∂ν = 0 ∧ variance (id : ℝ → ℝ) ν = 1 ∧
      (∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
        ν = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z)) ∧
      (∃ c C θ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ ∧
        Integrable (fun z => Real.exp (θ * |z|)) ν ∧
        ∀ᶠ r : ℝ in atTop,
          c * r ≤ -Real.log (ν (Set.Iic (-r))).toReal ∧
            -Real.log (ν (Set.Iic (-r))).toReal ≤ C * r) ∧
      (∃ Rseq : ℕ → ℝ, StrictMono Rseq ∧ Tendsto Rseq atTop atTop ∧
        ∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
          ∃ kl : ℕ → ℕ, StrictMono kl ∧
            ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
              Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
                (fun (L : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
                  Rseq (kl ⌊L⌋₊) ^ (((d : ℝ) - 4) / 2) *
                    Sandpile.Continuum.latticePairing (Rseq (kl ⌊L⌋₊))
                      (fun x => Sandpile.odometer σ ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊ x -
                        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν)
                          ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊) φ)
                (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T)) ∧
      ∀ T : ℝ, 0 < T → ∀ κ κ' : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
        κ' ∈ Set.Icc ((3 : ℝ) / 2) 2 → κ ≠ κ' →
        ∃ φ : Sandpile.Continuum.Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ ∧
          Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T φ φ ≠
            Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ' T φ φ
-- FROZEN-STATEMENT-END
:= by
  have hInter : Sandpile.External.IntersectionSecondMoment :=
    Sandpile.External.intersectionSecondMoment
  have hHeat : Sandpile.External.HeatKernelBounds := Sandpile.External.heatKernelBounds
  have hGreenHigh : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
  obtain ⟨ν, hprob, hmean, hvar, hdens, htail, hstep3, hdistinct⟩ :=
    Sandpile.Support.dgt4_many_limits_assembled d hd hGreenHigh hInter hHeat
      Sandpile.External.localCLT hBesov
  exact ⟨ν, hprob, hmean, hvar, hdens, htail, hstep3, hdistinct⟩
