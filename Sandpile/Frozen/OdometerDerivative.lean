import Sandpile.External.BPSHProved
import Sandpile.Support.OdometerPathDerivative

/-!
# The odometer derivative in one scenery coordinate, frozen

Lemma of `sandpile.tex` giving the derivative of the odometer in one coordinate of the scenery,
frozen (`sandpile.tex:868-881`, label `lem:odometer-derivative`): for independent, atomless
scenery, almost surely, for every `n ≥ 1` and `x, z ∈ ℤ^d`, the partial derivative
`∂_{ζ(z)} u_n(x)` equals the walk expectation `E_x ∑_j 1_{X_j=z} ∏_i 1_{u_{n-i}(X_i)>0}`, which in
turn equals `E_x ∑_j 1_{X_j=z} 1_{τ_n^* > j}` via the optimal-stopping time `τ_n^*`. Since the
paper's scenery coordinates need not be identically distributed, the law is the product measure
`Measure.infinitePi ν` over an arbitrary family of one-site laws, with atomlessness at a site
recorded as `NullSingletonClass (ν x)`; the derivative itself is `HasDerivAt` of `h ↦ u_n(x)`
computed from `Function.update ζ z h` at the point `ζ z`. The second equality reads off the
optimal-stopping representation of the odometer, a cited result now proved unconditionally as
`Sandpile.External.optimalStopping`, so it is no longer carried as an explicit hypothesis.
-/

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
