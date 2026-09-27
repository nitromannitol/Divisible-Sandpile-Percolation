/-
Proposition of Section 4 of sandpile.tex, frozen.  `sandpile.tex:1869-1876`
(label `prop:dlt4-heat-potential-invariance`):

  "[Invariance of the heat potential]  Fix $0<T<\infty$.  Then
   \[
     Z_R^{\rm lin}\Longrightarrow Z
   \]
   locally uniformly on $[0,T]\times\R^d$."

The rescaled linear field is defined in the running text just above,
`sandpile.tex:1833-1839`: "The rescaled linear field is defined by
\[
  Z_R(r,w)\coloneqq R^{d/2-2}\sum_{z\in\Z^d} g_{\lfloor R^2r\rfloor}(\lfloor Rw\rfloor,z)\zeta(z)\, .
\]
Write $Z_R^{\rm lin}$ for the standard interpolation of $Z_R$ from the mesh
$R^{-2}\Z_+\times R^{-1}\Z^d$."  The limit `Z` is the Gaussian heat potential of
`eq:dlt4-linear-gaussian-potential`.  The standing hypotheses are those of
`sandpile.tex:1810-1814`: `d ≤ 3`, `E ζ(0) = 0`, `0 < Var(ζ(0)) < ∞`, and
`E e^{θ₀|ζ(0)|} < ∞` for some `θ₀ > 0`.

Modelling choices.

"The standard interpolation from the parabolic mesh" is read as multilinear
interpolation on the cells of that mesh: `linInterp` below writes the value at
`(r,w)` as the multilinear combination of the `2^{d+1}` mesh values at the
corners of the cell containing `(r,w)`, with the weights given by the
fractional parts of `R^2 r` and of the coordinates of `R w`.  On the mesh the
fractional parts vanish and `linInterp` returns `Z_R` itself, and off the mesh
it is the unique function affine in each variable separately on each cell.  The
paper does not write this formula out, and a different interpolation with the
same mesh values would give a different, though equivalent-in-the-limit,
statement; this is the one modelling choice in the file that a reader could
dispute on grounds other than notation.

Weak convergence in `C_{\rm loc}([0,T]\times\R^d)`, with `C_{\rm loc}(U)` the
continuous functions with the topology of uniform convergence on compact
subsets (`sandpile.tex:726-728`), is not available as a `TendstoInDistribution`
here: it would need `Z_R^{\rm lin}` as a term of a space of continuous
functions, hence a proof of its continuity inside the statement.  It is
therefore written, exactly as `TendstoInNegSobolev` writes convergence of
random distributions, as the pair of clauses that is equivalent to it:
convergence of every finite-dimensional law, and tightness of the laws in
`C(K)` for every compact `K ⊆ [0,T]×ℝ^d`.  By the Arzelà-Ascoli criterion,
tightness in `C(K)` is tightness of the uniform norm on `K` together with
tightness of the modulus of continuity on `K`, and both clauses are stated;
the uniform-norm clause alone would not be tightness in `C(K)`.

Finite-dimensional convergence is stated for vectors, as convergence in
distribution of the `ℝ^m`-valued random variable at `m` prescribed points of
`[0,T]×ℝ^d`; no Cramér-Wold reduction is used.

Mathlib 4.32 has no construction of white noise, so the limit is carried by a
space `ΩW` quantified over.  The scenery is carried by its one-site law `ν`
through `centeredMassLaw d ν`, the law of `σ = 1 + 2dζ`, and `ζ` is recovered
from the integration variable as `Sandpile.scenery d σ`; the variance of the
scenery, which is the `Var(ζ(0))` appearing in `Z`, is `variance id ν`.

`R → ∞` is `atTop` on `ℝ`.  The lattice sum defining `Z_R` is a `tsum` over
`ℤ^d`, which is a finite sum in disguise, since `g_k(z,·)` is finitely
supported; no junk value arises.  `⌊R^2 r⌋` is `Nat.floor`, which agrees with
the paper's floor on the range `r ≥ 0` where it is used.
-/
import Sandpile.Continuum.WhiteNoise
import Sandpile.Walk
import Sandpile.Law
import Sandpile.External.LocalCLT
import Sandpile.External.LocalCLTProved
import Sandpile.Support.HeatPotentialDefs
import Sandpile.Support.HeatPotentialClauses

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.heat_potential_invariance
    (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (T : ℝ) (hT : 0 < T) :
    (∀ (m : ℕ) (r : Fin m → ℝ) (w : Fin m → Sandpile.Continuum.Space d),
        (∀ i, r i ∈ Set.Icc (0 : ℝ) T) →
        TendstoInDistribution
          (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (i : Fin m) =>
            Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
              (Sandpile.scenery d σ) (r i) (w i))
          atTop
          (fun (ω : ΩW) (i : Fin m) =>
            Sandpile.Continuum.gaussianPotential d (variance id ν) W (r i) (w i) ω)
          (fun _ => Sandpile.centeredMassLaw d ν) PW) ∧
      (∀ K : Set (ℝ × Sandpile.Continuum.Space d), IsCompact K →
        K ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) →
        (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
          (Sandpile.centeredMassLaw d ν)
              {σ | ∃ p ∈ K, M < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                (Sandpile.scenery d σ) p.1 p.2|} ≤ ENNReal.ofReal ε) ∧
        (∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
          (Sandpile.centeredMassLaw d ν)
              {σ | ∃ p ∈ K, ∃ q ∈ K, dist p q < δ ∧
                η < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                    (Sandpile.scenery d σ) p.1 p.2 -
                  Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                    (Sandpile.scenery d σ) q.1 q.2|} ≤ ENNReal.ofReal ε))
-- FROZEN-STATEMENT-END
:= Sandpile.Support.heat_potential_invariance_of_clauses Sandpile.External.localCLT d hd0 hd ν
    hmean hvar hvar' θ₀ hθ₀ hexp PW W hW T hT
