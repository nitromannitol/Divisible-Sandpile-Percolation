/-
Proposition of sandpile.tex, frozen.  `sandpile.tex:4763-4774`
(label `prop:weighted-membrane-limit`):

  "Let $d\geq5$ and $T>0$, let $q:[0,T]\to\R$ be continuous, and suppose that
   $(\zeta(x))_{x\in\Z^d}$ are i.i.d.\ with mean zero and finite positive
   variance.  For every $s>(d-4)/2$, as $R\to\infty$,
     $R^{(d-4)/2}\left(\sum_{j=0}^{\lfloor R^2T\rfloor-1}q(j/R^2)P^j\zeta\right)^{(R)}
      \Longrightarrow
      \sqrt{\Var(\zeta(0))}\int_0^Tq(r)e^{r\Delta/(2d)}\mathcal W\,dr$
   in $H^{-s}_{\rm loc}(\R^d)$."

Modelling decisions.

The limit field is a general-weight version of `ℋ_{κ,T}`, so the covariance
`Sandpile.Continuum.weightedMembraneCov`, which hard-codes the weight
`(1-r/T)^κ`, is not general enough; `generalWeightedMembraneCov` below replaces
the two powers by `q r * q r'` and is derived exactly as that one is.  Both
limit fields are centred Gaussian random distributions, so their laws are
determined by their covariances, and no space carrying white noise is quantified
over: the white noise has been integrated out of the covariance.

`P^j ζ` is `Sandpile.avg^[j] ζ`, the `j`-fold iterate of the averaging operator,
and the sum `∑_{j=0}^{⌊R^2T⌋-1}` is `Finset.range ⌊R^2 T⌋₊`.  The rescaling
`(·)^{(R)}` paired with a test function is
`Sandpile.Continuum.latticePairing R`, and convergence in `H^{-s}_{loc}(ℝ^d)` is
`Sandpile.Continuum.TendstoInNegSobolev`.

The scenery is written in the mass normalization: the integration variable is
`σ` with law `Sandpile.centeredMassLaw d ν`, so `ζ = Sandpile.scenery d σ` has
one-site law `ν`.  This is the convention of the other frozen files, and
`centeredMassLaw` carries the `IsProbabilityMeasure` instance that
`TendstoInNegSobolev` needs.

`q` is a function on all of `ℝ`, continuous on `[0,T]`; only its values on
`[0,T]` are used, since `j/R^2 < T` for `j < ⌊R^2T⌋` and the time integral in
the covariance runs over `[0,T]`.

Cited inputs (standing convention R1).  The proof of the first clause is the local
central limit theorem of `eq:lclt-parity` followed by a Riemann-sum argument
(`sandpile.tex:4724-4729`), so `Sandpile.External.LocalCLT` enters, and the
uniform bound that dominated convergence needs is the Gaussian upper bound
`eq:rw-gaussian-upper`, so `Sandpile.External.HeatKernelBounds` enters.  The
proof of the second clause is the tightness criterion of `lem:sobolev-tightness`
applied to the covariance decay of `eq:dgt4-intersection-first-moment`, so
`Sandpile.External.GreenBoundsHigh` and
`Sandpile.External.ContinuumBesovTightness` enter.  The last of these is the
hypothesis `hBesov` added at version 3.
-/
import Sandpile.Law
import Sandpile.Walk
import Sandpile.Continuum.Membrane
import Sandpile.External.GreenBoundsHigh
import Sandpile.External.GreenBoundsHighProved
import Sandpile.External.HeatKernelBounds
import Sandpile.External.HeatKernelBoundsProved
import Sandpile.External.LocalCLT
import Sandpile.External.LocalCLTProved
import Sandpile.External.ContinuumBesovTightness
import Sandpile.Support.ContVarianceLimit
import Sandpile.Support.TightWeightedMembrane
import Sandpile.Support.ContSeqCLT

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Frozen.WeightedMembraneLimit

/-- The covariance of `√Var(ζ(0)) ∫_0^T q(r) e^{rΔ/(2d)} 𝒲 dr`, the limit field of
`sandpile.tex:4694-4696`, with scenery variance `ν2`.  The field is a mean-zero
Gaussian random distribution, so its law is determined by this covariance.
Pairing with test functions and using the semigroup identity
`∫ (e^{rΔ/(2d)}φ)(z)(e^{r'Δ/(2d)}ψ)(z) dz = ∫∫ φ(x) ψ(y) p^{BM}_{r+r'}(x,y) dx dy`
turns the covariance into a real-space double time integral against the Brownian
heat kernel, exactly as for `Sandpile.Continuum.weightedMembraneCov`, with
`q r * q r'` in place of `(1-r/T)^κ (1-r'/T)^κ`. -/
noncomputable def generalWeightedMembraneCov (d : ℕ) (ν2 T : ℝ) (q : ℝ → ℝ)
    (φ ψ : Sandpile.Continuum.Space d → ℝ) : ℝ :=
  ν2 * ∫ x : Sandpile.Continuum.Space d, ∫ y : Sandpile.Continuum.Space d, φ x * ψ y *
    (∫ r in (0 : ℝ)..T, ∫ r' in (0 : ℝ)..T,
      q r * q r' * Sandpile.Continuum.heatKernelBM d (r + r') x y)

end Sandpile.Frozen.WeightedMembraneLimit

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.weighted_membrane_limit
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (T : ℝ) (hT : 0 < T)
    (q : ℝ → ℝ) (hq : ContinuousOn q (Set.Icc 0 T))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (s : ℝ) (hs : ((d : ℝ) - 4) / 2 < s) :
    Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
      (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
        R ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing R
            (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)
      (Sandpile.Frozen.WeightedMembraneLimit.generalWeightedMembraneCov d
        (variance (id : ℝ → ℝ) ν) T q)
-- FROZEN-STATEMENT-END
:= by
  classical
  have hHeatKernel : Sandpile.External.HeatKernelBounds := Sandpile.External.heatKernelBounds
  have hGreenHigh : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
  have _ := hvar
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hsq : MemLp (id : ℝ → ℝ) 2 ν :=
    (ProbabilityTheory.evariance_lt_top_iff_memLp aestronglyMeasurable_id).mp hvar'
  obtain ⟨q', Q, hq'c, hQ0, hQ, hqq⟩ :=
    Sandpile.Support.exists_continuous_extension_bdd hT.le q hq
  have hQicc : ∀ r ∈ Set.Icc (0:ℝ) T, |q r| ≤ Q := by
    intro r hr
    rw [← hqq r hr]
    exact hQ r
  have hfun : ∀ (R : ℝ) (σ : Sandpile.Site d → ℝ),
      (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x)
        = (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          q' ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) := by
    intro R σ
    funext x
    refine Finset.sum_congr rfl fun j hj => ?_
    rcases eq_or_ne R 0 with hR | hR
    · rw [hR] at hj
      simp at hj
    · have hR2 : (0:ℝ) < R ^ 2 := by positivity
      have hjlt : ((j : ℕ) : ℝ) < R ^ 2 * T := by
        have h1 : j < ⌊R ^ 2 * T⌋₊ := Finset.mem_range.mp hj
        have h2 : ((j : ℕ) : ℝ) < ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
        exact lt_of_lt_of_le h2 (Nat.floor_le (by positivity))
      rw [hqq ((j : ℝ) / R ^ 2) ⟨by positivity, by rw [div_le_iff₀ hR2]; linarith⟩]
  refine ⟨?_, ?_⟩
  · intro φ hφtest
    obtain ⟨C, L, hC0, hL0, hC, hsupp, hint⟩ :=
      Sandpile.Support.exists_bound_of_isTestFn hφtest
    have hcov : Filter.Tendsto (fun R : ℝ => ∑ z ∈ Sandpile.Support.coeffBox d R L T,
        Sandpile.Support.scaledCoeff d R L T q' φ z ^ 2) Filter.atTop
        (nhds (∫ x : Sandpile.Continuum.Space d, ∫ y : Sandpile.Continuum.Space d, φ x * φ y *
          (∫ r in (0:ℝ)..T, ∫ r' in (0:ℝ)..T,
            q r * q r' * Sandpile.Continuum.heatKernelBM d (r + r') x y))) := by
      refine (Sandpile.Support.tendsto_sum_scaledCoeff_sq Sandpile.External.localCLT hHeatKernel
        hd1 hT q hq φ hint hC hsupp).congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with R hR
      exact (Sandpile.Support.sum_scaledCoeff_sq_congr hR L hT.le q q' hqq φ).symm
    have hmain := Sandpile.Support.weighted_pairing_tendsto_of_covariance' hd1 hT.le ν hsq hmean
      q' Q hQ0 hQ φ C L hC0 hC hsupp hint _ hcov
    have hEq : (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) =>
        R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
          (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)
      = (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) =>
        R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
          (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            q' ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) := by
      funext R σ
      rw [hfun R σ]
    show TendstoInDistribution
      (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) =>
        R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
          (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)
      Filter.atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
      (gaussianReal 0 (Real.toNNReal
        (Sandpile.Frozen.WeightedMembraneLimit.generalWeightedMembraneCov d
          (variance (id : ℝ → ℝ) ν) T q φ φ)))
    rw [hEq]
    exact hmain
  · exact Sandpile.Support.weighted_membrane_tight hGreenHigh hBesov hd ν hsq hmean T hT q Q
      hQ0 hQicc s hs
