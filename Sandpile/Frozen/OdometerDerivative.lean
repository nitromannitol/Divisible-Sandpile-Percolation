/-
Lemma of sandpile.tex giving the derivative of the odometer in one coordinate of
the scenery, frozen.  `sandpile.tex:868-881` (label `lem:odometer-derivative`):

  "Suppose $(\zeta(x))_{x\in\Z^d}$ are independent and atomless. Then,
   $\P$-almost surely, for every $n\geq1$ and $x,z\in\Z^d$,
   $\partial_{\zeta(z)}u_n(x)
    = \mathbf E_x\sum_{j=0}^{n-1}\one_{\{X_j=z\}}
      \prod_{i=0}^j\one_{\{u_{n-i}(X_i)>0\}}
    = \mathbf E_x\sum_{j=0}^{n-1}\one_{\{X_j=z\}}\one_{\{\tau_n^*>j\}}$."

The scenery is independent and atomless, and, as in the paper, the coordinates are
not assumed identically distributed.  The law of the scenery is therefore the product
measure `Measure.infinitePi ν` of an arbitrary family `ν : Site d → Measure ℝ` of
one-site laws, one for each site, each a probability measure, and atomlessness of the
law at a site is `NullSingletonClass (ν x)`.  The identically distributed field is the
constant family, `LatticeProb.iidLaw d ν = Measure.infinitePi fun _ => ν`.  Independence
is carried by the product structure and atomlessness is what excludes ties, which is
proved one coordinate at a time.  The partial derivative in the single coordinate `ζ(z)` is `HasDerivAt` of
`h ↦ u_n(x)` computed from the field `Function.update ζ z h`, at the point
`ζ z`.  Both right-hand sides of the paper's chain are transcribed: the first
uses only `Sandpile.odometerOf`, and the second uses `Sandpile.optimalStop`, the
`τ_n^*` of `thm:RW`, which is why this file imports `Sandpile.External.BPSH`
for that definition alone and not for its assumed statement.  Indicators are
`Set.indicator` of the corresponding path sets, so no decidability instance
enters the statement.  In `u_{n-i}` the index is a truncated subtraction, which
agrees with the paper because `i ≤ j ≤ n - 1`.

The paper's proof reads the second right-hand side off the optimal-stopping
representation, which is a cited result rather than a theorem of the paper.  It
is proved unconditionally in this repository, `Sandpile.External.optimalStopping`
(`Sandpile/External/BPSHProved.lean`), so it is no longer carried here as an
explicit hypothesis, exactly as in the frozen `thm:RW`.
-/
import Sandpile.External.BPSHProved
import Sandpile.Support.OdometerPathDerivative

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.odometer_derivative
    (d : ℕ) (hd : 1 ≤ d) (ν : Sandpile.Site d → Measure ℝ)
    (hprob : ∀ x, IsProbabilityMeasure (ν x))
    (hatom : ∀ x, NullSingletonClass (ν x)) :
    ∀ᵐ ζ ∂(MeasureTheory.Measure.infinitePi ν), ∀ n : ℕ, 1 ≤ n → ∀ x z : Sandpile.Site d,
      HasDerivAt (fun h : ℝ => Sandpile.odometerOf (Function.update ζ z h) n x)
          (∫ X, ∑ j ∈ Finset.range n,
              Set.indicator {Y : ℕ → Sandpile.Site d | Y j = z} (fun _ => (1 : ℝ)) X *
                ∏ i ∈ Finset.range (j + 1),
                  Set.indicator {Y : ℕ → Sandpile.Site d | 0 < Sandpile.odometerOf ζ (n - i) (Y i)}
                    (fun _ => (1 : ℝ)) X
            ∂(Sandpile.walkLaw d x)) (ζ z) ∧
        ∫ X, ∑ j ∈ Finset.range n,
            Set.indicator {Y : ℕ → Sandpile.Site d | Y j = z} (fun _ => (1 : ℝ)) X *
              ∏ i ∈ Finset.range (j + 1),
                Set.indicator {Y : ℕ → Sandpile.Site d | 0 < Sandpile.odometerOf ζ (n - i) (Y i)}
                  (fun _ => (1 : ℝ)) X
          ∂(Sandpile.walkLaw d x) =
        ∫ X, ∑ j ∈ Finset.range n,
            Set.indicator {Y : ℕ → Sandpile.Site d | Y j = z} (fun _ => (1 : ℝ)) X *
              Set.indicator {Y : ℕ → Sandpile.Site d | j < Sandpile.optimalStop ζ n Y}
                (fun _ => (1 : ℝ)) X
          ∂(Sandpile.walkLaw d x)
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI : ∀ x, IsProbabilityMeasure (ν x) := hprob
  haveI : ∀ x, NullSingletonClass (ν x) := hatom
  filter_upwards [Sandpile.ae_odometer_preactivation_ne_zero_pi (d := d) ν] with ζ hζ
  intro n _hn x z
  simp only [Set.indicator, Set.mem_setOf_eq]
  have hI : (∫ X, ∑ j ∈ Finset.range n,
      (if X j = z then (1 : ℝ) else 0) *
        ∏ i ∈ Finset.range (j + 1),
          (if 0 < Sandpile.odometerOf ζ (n - i) (X i) then 1 else 0)
      ∂Sandpile.walkLaw d x) = Sandpile.odometerJacobian ζ n x z := by
    simpa only [Sandpile.pathOdometerDerivative_eq_sum] using
      Sandpile.integral_pathOdometerDerivative hd ζ n x z
  constructor
  · rw [hI]
    exact Sandpile.hasDerivAt_odometerOf ζ hζ n x z
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro X
    apply Finset.sum_congr rfl
    intro j hj
    rw [Sandpile.active_product_eq_optimalStop_indicator
      Sandpile.External.optimalStopping hd ζ n j
      (Nat.le_of_lt (Finset.mem_range.mp hj)) X]
