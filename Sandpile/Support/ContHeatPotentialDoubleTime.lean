import Sandpile.Support.ContGreenFubini
import Sandpile.Support.ContHeatPotentialCoeff
import Sandpile.Support.ContBMGreenIdentity

/-!
# The Finite-Dimensional Clause Reduced to Double Time Convergence

The finite-dimensional clause of `prop:dlt4-heat-potential-invariance`
(`sandpile.tex:1841-1848`) in dimensions one to three, reduced to a single
convergence statement.

Four of the five inputs the clause needed are now theorems.  The Lindeberg
smallness of the coefficients is `interp_hsmall`, the square integrability of the
Brownian Green kernels is `memLp_greenTimeBM`, the sums of squares of the
coefficients are exactly a finite combination of rescaled double time sums of
transition probabilities (`sum_interp_sq_eq`, through the lattice Fubini identity
`tsum_greenTime_mul_greenTime`), and the `L²` pairing of the Brownian Green
kernels on the continuum side is exactly the matching matrix of double time
integrals of the heat kernel (`integral_sum_greenTimeBM_sq_eq`, through the
continuum Green identity).

So what is left is the comparison of the two, one pair of mesh points at a time:

  `R^{d-4} ∑_{a<⌊R^2 r⌋} ∑_{b<⌊R^2 r'⌋} p_{a+b}(⌊Rw⌋, ⌊Rw'⌋)
      → ∫_0^{r} ∫_0^{r'} p^{BM}_{s+s'}(w, w') ds' ds`,

which is the local central limit theorem of `ssec:green-estimates` together with
the Riemann-sum convergence, and nothing else.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- The doubled coefficient sum of two mesh points, written out: the interpolation
weights against the rescaled double time sums of transition probabilities. -/
noncomputable def interpDoubleTimeSum (d : ℕ) (R r r' : ℝ) (w w' : Space d) : ℝ :=
  ∑ p : (Fin d → Bool) × Bool, ∑ q : (Fin d → Bool) × Bool,
    interpTermWeight d R r w p * interpTermWeight d R r' w' q *
      (R ^ ((d : ℝ) - 4) *
        ∑ a ∈ Finset.range (timeIndex R r p.2), ∑ b ∈ Finset.range (timeIndex R r' q.2),
          Sandpile.heatKernel d (a + b) (cornerSite d R w p.1) (cornerSite d R w' q.1))

/-- `sum_interp_sq_eq` restated in terms of `interpDoubleTimeSum`: the sum over
the interpolation box of the square of a linear combination `∑ i, t i * interpCoeff ...`
of coefficient values equals the double sum of `t i * t j * interpDoubleTimeSum`
at the corresponding pair of mesh points. -/
theorem sum_interp_sq_eq' (d : ℕ) {R : ℝ} (hR : 0 < R) (L : ℝ) {m : ℕ} (r : Fin m → ℝ)
    (w : Fin m → Space d) (hw : ∀ i, ‖w i‖ ≤ L) (t : Fin m → ℝ) :
    ∑ k : Fin (interpBox d R L r).card,
        (∑ i, t i * interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k)) ^ 2
      = ∑ i, ∑ j, t i * t j * interpDoubleTimeSum d R (r i) (r j) (w i) (w j) :=
  sum_interp_sq_eq d hR L r w hw t

/-- **The finite-dimensional clause of `prop:dlt4-heat-potential-invariance` in
dimensions one to three, from one convergence statement.**  Everything else in the
clause is now a theorem: the Lindeberg smallness of the coefficients, the square
integrability of the Brownian Green kernels, the exact lattice Fubini identity for
the doubled coefficient sums, and the continuum Green identity for their limit.  What
remains is the local central limit theorem in the form of `ssec:green-estimates`: the
rescaled double time sums of transition probabilities converge to the double time
integrals of the Brownian heat kernel. -/
theorem heat_potential_fd_of_double_time (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    {m : ℕ} (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) (w : Fin m → Space d) (L : ℝ)
    (hw : ∀ i, ‖w i‖ ≤ L)
    (hconv : ∀ i j : Fin m,
      Tendsto (fun R : ℝ => interpDoubleTimeSum d R (r i) (r j) (w i) (w j)) atTop
        (𝓝 (∫ s in (0 : ℝ)..(r i), ∫ u in (0 : ℝ)..(r j),
          Sandpile.Continuum.heatKernelBM d (s + u) (w i) (w j)))) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site d → ℝ) (i : Fin m) =>
        Sandpile.Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) (r i) (w i))
      atTop
      (fun (ω : ΩW) (i : Fin m) =>
        Sandpile.Continuum.gaussianPotential d (variance (id : ℝ → ℝ) ν) W (r i) (w i) ω)
      (fun _ => Sandpile.centeredMassLaw d ν) PW := by
  classical
  refine heat_potential_fd_of_coeff hd hd3 ν hsq hmean PW W hW r hr w L hw
    (fun t => ∑ i, ∑ j, t i * t j *
      ∫ s in (0 : ℝ)..(r i), ∫ u in (0 : ℝ)..(r j),
        Sandpile.Continuum.heatKernelBM d (s + u) (w i) (w j)) ?_ ?_
  · intro t
    have heq : ∀ᶠ R : ℝ in atTop,
        (∑ i, ∑ j, t i * t j * interpDoubleTimeSum d R (r i) (r j) (w i) (w j))
          = ∑ k : Fin (interpBox d R L r).card,
            (∑ i, t i * interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k)) ^ 2 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact (sum_interp_sq_eq' d hR L r w hw t).symm
    refine Tendsto.congr' heq ?_
    exact tendsto_finsetSum _ fun i _ =>
      tendsto_finsetSum _ fun j _ => (hconv i j).const_mul (t i * t j)
  · intro t
    have hvar : ∫ z, z ^ 2 ∂ν = variance (id : ℝ → ℝ) ν := by
      rw [ProbabilityTheory.variance_eq_sub hsq]
      have h1 : ∫ z, ((id : ℝ → ℝ) ^ 2) z ∂ν = ∫ z, z ^ 2 ∂ν := rfl
      have h2 : ∫ z, (id : ℝ → ℝ) z ∂ν = 0 := hmean
      rw [h1, h2]
      ring
    have hnn : (0 : ℝ) ≤ variance (id : ℝ → ℝ) ν := variance_nonneg _ _
    rw [integral_sum_greenTimeBM_sq_eq hd hd3 r hr w t (Real.sqrt (variance (id : ℝ → ℝ) ν)),
      hvar, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsq2 : Real.sqrt (variance (id : ℝ → ℝ) ν) * Real.sqrt (variance (id : ℝ → ℝ) ν)
        = variance (id : ℝ → ℝ) ν := Real.mul_self_sqrt hnn
    linear_combination (-(t i * t j * (∫ s in (0 : ℝ)..(r i), ∫ u in (0 : ℝ)..(r j),
      Sandpile.Continuum.heatKernelBM d (s + u) (w i) (w j)))) * hsq2

end Sandpile.Support
