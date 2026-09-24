/-
Theorem 1.3(i)(b) of sandpile.tex, frozen.  `sandpile.tex:216-236`
(label `thm:main-explosion`, part (i)(b)):

  "The parabolic scaling limit is a Brownian optimal-stopping value.  Let
   $\mathcal W$ be white noise on $\R^d$, let
   $Z(t,x)\coloneqq\sqrt{\Var(\zeta(0))}\int_{\R^d}g_t^{\rm BM}(x,y)\mathcal W(dy)$,
   with $g_t^{\rm BM}$ the finite-time Green kernel of Brownian motion, and let
   $\mathcal U(T,x)\coloneqq\sup_{\tau\leq T}\mathbf E_x^{\rm BM}
   [Z(T,x)-Z(T-\tau,B_\tau)]$, where the supremum is over stopping times for
   Brownian motion.  Then, for every $T>0$,
   $R^{-(2-d/2)}u^{(R)}_{\lfloor TR^2\rfloor}\Longrightarrow\mathcal U(T,\cdot)$
   in $C_{\rm loc}(\R^d)$, where the field on the left denotes the multilinear
   interpolation from $R^{-1}\Z^d$ of the values
   $x/R\mapsto R^{-(2-d/2)}u_{\lfloor TR^2\rfloor}(x)$."

Modelling choices.  The field on the left is the multilinear interpolation
`multilinearInterp`, not the piecewise-constant `Sandpile.Continuum.embed`,
because this clause is the one exception the paper flags before the theorem.
Mathlib 4.32 constructs neither white noise nor Brownian motion, so both are
predicates and the statement is quantified over a probability space carrying
white noise and, on a second space, over a family of Brownian motions indexed by
their starting point; the two spaces realize the paper's independence of `B` and
`\mathcal W`, and holding the white noise fixed inside the stopping value is
exactly what the paper prescribes.  `\Var(\zeta(0))` is `variance id ν`, and
`\mathcal U(T,x)` is `brownianValue` with the deterministic reward
`h = Z(\cdot,\cdot)(\omega)`, which is `\mathcal U_Z` of
`eq:continuum-membrane-stopping-value`.  The potential `Z` is the continuous
version fixed at `sandpile.tex:1019-1021` and `sandpile.tex:2104`: a
modification of `eq:dlt4-linear-gaussian-potential`, almost surely continuous on
each strip `[0,T] \times \R^d` and of polynomial growth there.  Continuity and
growth are what make the supremum over the Brownian stopping rules a supremum
over a bounded set of reals, so that `\mathcal U(T,x)` is the value of
`eq:continuum-membrane-stopping-value` and not the junk value of an unbounded
supremum; they are the binders `prop:continuum-value-selfsimilar` carries, in
the same form and the same position.  Weak convergence in `C_{\rm loc}(\R^d)`
is written as the pair the paper's proof produces: convergence of every
finite-dimensional law, jointly at finitely many points, together with tightness
of the field on every compact set.  The tightness clause is phrased through the
event `∃ z ∈ K, M < |·|` rather than a supremum, so that the junk value of an
unbounded `sSup` cannot make it vacuously true.

Weak convergence in `C_loc(ℝ^d)` is recorded by its two clauses: convergence of
the finite-dimensional laws, and tightness in `C(K)` on every compact `K`.  The
second is stated in full Arzelà-Ascoli form, tightness of the uniform norm
together with tightness of the modulus of continuity; the uniform-norm clause
alone is not tightness in `C(K)` and the pair would then be weaker than the
paper's assertion.

Path regularity.  The motion carries the two binders `lem:brownian-ball-localization`
carries beside its `IsBrownian`, continuity of EVERY path and strong measurability
of the value at each time, because the reward `Z` is unbounded on the strip and the
supremum defining `\mathcal U(T,x)` is over a bounded set of reals only through an
envelope built from the maximal displacement of the path; the paper's Brownian
motion is the standard one, which has them.  The Brownian realization space names
its universe, `Type u`, because the cited stability input is a hypothesis about a
realization space and must be taken at the universe where the motion lives.

The heat-potential invariance step carries `Sandpile.External.LocalCLT`
from `sandpile.tex:1145-1161`.

Cited input.  The paper's proof of this part (`sandpile.tex:1900-1907`) invokes the
stability of optimal-stopping values under uniform convergence of bounded rewards
together with the invariance principle for the stopped walk, citing Coquet and
Toldo, Theorem 3 and Corollary 4, and announces the same use at `sandpile.tex:649`.
That result is registered as `Sandpile.External.ContinuumStoppingStability` and is
carried here as the explicit hypothesis `hStab`; nothing else about it is assumed,
and the conclusion is unchanged.
-/
import Sandpile.Support.MainExplScaling
import Sandpile.Law
import Sandpile.Continuum.Stopping
import Sandpile.Support.ExplInterp
import Sandpile.External.ContStoppingStability

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.brownian_scaling_limit
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W P)
    (Z : ℝ → Sandpile.Continuum.Space d → Ω → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[P] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hZgrow : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P, ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k)
    (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω' → Sandpile.Continuum.Space d)
    (hB : ∀ x : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d x (B x) P')
    (hBc : ∀ (y : Sandpile.Continuum.Space d) (ω : Ω'), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (T : ℝ) (hT : 0 < T) :
    (∀ (m : ℕ) (x : Fin m → Sandpile.Continuum.Space d),
        TendstoInDistribution
          (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (j : Fin m) =>
            Sandpile.Continuum.multilinearInterp R
              (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) (x j))
          atTop
          (fun (ω : Ω) (j : Fin m) =>
            Sandpile.Continuum.brownianValue (B (x j)) P'
              (fun t y => Z t y ω)
              T (x j))
          (fun _ => Sandpile.centeredMassLaw d ν) P) ∧
      ∀ K : Set (Sandpile.Continuum.Space d), IsCompact K →
        (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
          Sandpile.centeredMassLaw d ν
              {σ | ∃ z ∈ K, M < |Sandpile.Continuum.multilinearInterp R
                (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z|} ≤
            ENNReal.ofReal ε) ∧
        (∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
          Sandpile.centeredMassLaw d ν
              {σ | ∃ z ∈ K, ∃ z' ∈ K, dist z z' < δ ∧
                η < |Sandpile.Continuum.multilinearInterp R
                    (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z -
                  Sandpile.Continuum.multilinearInterp R
                    (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z'|} ≤
            ENNReal.ofReal ε)
-- FROZEN-STATEMENT-END
:= by
  exact Sandpile.brownian_scaling_limit_of_localCLT hLocalCLT hStab d hd hd3 ν
    hmean hvar hvar' θ₀ hθ₀ hexp Ω P W hW Z hZmod hZcont hZgrow Ω' P' B hB hBc hBm T hT
