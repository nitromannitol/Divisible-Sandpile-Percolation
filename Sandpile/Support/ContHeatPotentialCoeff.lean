/-
The finite-dimensional clause of `prop:dlt4-heat-potential-invariance`
(`sandpile.tex:1841-1848`), reduced to the two Riemann-sum statements about the
coefficients of the rescaled linear field.

`heat_potential_fd_of` asked for four inputs: square integrability of the
Brownian Green kernels, Lindeberg's smallness of the combined coefficients, the
convergence of their sums of squares, and the identification of the limit with
the `L²` inner product.  In dimensions one to three the first two are now
theorems, `memLp_greenTimeBM` and `interp_hsmall`, so the clause rests on the
last two alone: the sums of squares converge, and their limit is the `L²` inner
product of the Brownian Green kernels.  Those are the local central limit
theorem and the Riemann-sum convergence of `ssec:green-estimates`.
-/
import Sandpile.Support.ContInterpSmall
import Sandpile.Support.ContBMSquare

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- **The finite-dimensional convergence of the rescaled linear field in
dimensions one to three, from the coefficient asymptotics alone.** -/
theorem heat_potential_fd_of_coeff (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    {m : ℕ} (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) (w : Fin m → Space d) (L : ℝ)
    (hw : ∀ i, ‖w i‖ ≤ L) (Q : (Fin m → ℝ) → ℝ)
    (hQlim : ∀ t : Fin m → ℝ, Tendsto (fun R : ℝ => ∑ k : Fin (interpBox d R L r).card,
      (∑ i, t i * interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k)) ^ 2)
      atTop (𝓝 (Q t)))
    (hQvar : ∀ t : Fin m → ℝ, (∫ z, z ^ 2 ∂ν) * Q t
      = ∫ y : Space d,
          (∑ i, t i * (Real.sqrt (variance (id : ℝ → ℝ) ν) *
            Sandpile.Continuum.greenTimeBM d (r i) (w i) y)) *
          ∑ i, t i * (Real.sqrt (variance (id : ℝ → ℝ) ν) *
            Sandpile.Continuum.greenTimeBM d (r i) (w i) y)) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site d → ℝ) (i : Fin m) =>
        Sandpile.Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) (r i) (w i))
      atTop
      (fun (ω : ΩW) (i : Fin m) =>
        Sandpile.Continuum.gaussianPotential d (variance (id : ℝ → ℝ) ν) W (r i) (w i) ω)
      (fun _ => Sandpile.centeredMassLaw d ν) PW :=
  heat_potential_fd_of hd ν hsq hmean PW W hW r w L hw
    (fun i => memLp_greenTimeBM hd hd3 (hr i) (w i)) Q
    (fun t δ hδ => interp_hsmall hd hd3 r hr w L t δ hδ) hQlim hQvar

end Sandpile.Support
