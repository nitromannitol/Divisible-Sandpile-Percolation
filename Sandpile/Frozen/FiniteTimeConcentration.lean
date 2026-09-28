import Sandpile.Support.Concentration

/-!
# Concentration at the fluctuation scale

Proposition "Concentration at the fluctuation scale" of sandpile.tex, frozen.
`sandpile.tex:1462-1487` (label `prop:finite-time-concentration-scale`):

  "Assume that $(\zeta(z))_{z\in\Z^d}$ are i.i.d.  For each $x$ and $t$, the map
   $\zeta\mapsto u_t(x)$ is convex and satisfies
   \[
     |u_t(x;\zeta)-u_t(x;\eta)|
     \leq\left(\sum_{z\in\Z^d}g_t(x,z)^2\right)^{1/2}
     \|\zeta-\eta\|_{\ell^2(\Z^d)}\, .
   \]
   For every $p\geq2$ with $\E|\zeta(0)|^p<\infty$ there is
   $C=C(p,\mathcal L(\zeta(0)))<\infty$ such that
   $\E|u_t(x)-\E u_t(x)|^p\leq C\Var(V_t(0))^{p/2}$.
   ...
   If $0<\Var(\zeta(0))<\infty$, then, for every $m,n\geq0$ and $x,y\in\Z^d$,
   \[
     0\leq\Cov(u_n(x),u_m(y))
     \leq 2\Var(\zeta(0))\sum_{z\in\Z^d}g_n(x,z)g_m(y,z)\, .
   \]"

Modelling.  The scenery is the i.i.d. field with one-site law `ν` and law
`LatticeProb.iidLaw d ν` on `Site d → ℝ`; the odometer in the scenery language
is `Sandpile.odometerOf ζ t x` and the membrane field is
`Sandpile.membrane ζ t 0`, so `Var(V_t(0))` is written as the variance of
`ζ ↦ membrane ζ t 0` under that law and is not replaced by the formula
`Var(ζ(0)) ∑_z g_t(0,z)^2` of `sandpile.tex:1178-1182`.  `Var(ζ(0))` in the
covariance clause is `variance id ν`.

Convexity is stated on the whole vector space `Site d → ℝ`, that is
`ConvexOn ℝ Set.univ`, rather than only along the finitely supported directions
in which the paper perturbs the scenery: the odometer is a supremum of
functionals of `ζ` that are linear with finitely supported coefficients, so it
is convex on the whole space and the stronger form is the honest one.

The `ℓ²` Lipschitz bound uses two unconditional sums.  The coefficient sum
`∑_z g_t(x,z)^2` is a `tsum` of a finitely supported function, since
`greenTime d t x z = 0` once `|z-x| > t`.  The scenery difference
`‖ζ-η‖_{ℓ²}` is a `tsum` that is meaningless for a non square summable
difference, where it would take the junk value `0` and make the inequality
false rather than vacuous, so square summability of `ζ - η` is a hypothesis of
that clause.

Quantifier order.  The one-site law is the only theorem parameter; the dimension
is bound inside each of the four clauses.  That is what puts the moment clause's
constant where the paper puts it: `C = C(p, \mathcal L(\zeta(0)))` is chosen
after `p` and after the law and before everything else, so nothing else is in
scope for it to depend on.  The paper's convention (`sandpile.tex:781-782`)
writes out a constant's dependence, as in `C = C(d)`, and this constant is
written with no `d`, so one constant must serve every dimension.  Were the
dimension a theorem parameter instead, it would be in scope at the existential
and the statement would permit a different constant in each dimension.  The
covariance clause carries the paper's extra hypothesis `0 < Var(\zeta(0))`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.finite_time_concentration_scale
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) :
    (∀ (d : ℕ), 1 ≤ d → ∀ (t : ℕ) (x : Sandpile.Site d),
      ConvexOn ℝ (Set.univ : Set (Sandpile.Site d → ℝ))
        fun ζ => Sandpile.odometerOf ζ t x) ∧
    (∀ (d : ℕ), 1 ≤ d → ∀ (t : ℕ) (x : Sandpile.Site d) (ζ η : Sandpile.Site d → ℝ),
      Summable (fun z => (ζ z - η z) ^ 2) →
      |Sandpile.odometerOf ζ t x - Sandpile.odometerOf η t x| ≤
        Real.sqrt (∑' z : Sandpile.Site d, Sandpile.greenTime d t x z ^ 2) *
          Real.sqrt (∑' z : Sandpile.Site d, (ζ z - η z) ^ 2)) ∧
    (∀ p : ℝ, 2 ≤ p → Integrable (fun z => |z| ^ p) ν → ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (t : ℕ) (x : Sandpile.Site d),
        ∫ ζ, |Sandpile.odometerOf ζ t x -
            ∫ η, Sandpile.odometerOf η t x ∂(LatticeProb.iidLaw d ν)| ^ p
              ∂(LatticeProb.iidLaw d ν) ≤
          C * variance (fun ζ => Sandpile.membrane ζ t 0) (LatticeProb.iidLaw d ν) ^ (p / 2)) ∧
    (∀ (d : ℕ), 1 ≤ d → 0 < variance id ν → Integrable (fun z => z ^ 2) ν →
      ∀ (m n : ℕ) (x y : Sandpile.Site d),
        0 ≤ covariance (fun ζ => Sandpile.odometerOf ζ n x)
            (fun ζ => Sandpile.odometerOf ζ m y) (LatticeProb.iidLaw d ν) ∧
          covariance (fun ζ => Sandpile.odometerOf ζ n x)
              (fun ζ => Sandpile.odometerOf ζ m y) (LatticeProb.iidLaw d ν) ≤
            2 * variance id ν *
              ∑' z : Sandpile.Site d, Sandpile.greenTime d n x z * Sandpile.greenTime d m y z)
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  refine ⟨fun _d _hd t x => Sandpile.odometerOf_convexOn t x, ?_, ?_, ?_⟩
  · intro _d _hd t x ζ η hsum
    exact Sandpile.abs_odometerOf_sub_le_l2 t x ζ η hsum
  · intro p hp hmom
    obtain ⟨C, hC, hb⟩ := Sandpile.exists_odometer_moment_variance_uniform ν hp hmom
    exact ⟨C, hC, fun d _hd t x => hb d t x⟩
  · intro _d _hd _hvar hsq m n x y
    exact ⟨Sandpile.covariance_odometerOf_nonneg ν hsq n m x y,
      Sandpile.covariance_odometerOf_le ν hsq n m x y⟩
