/-
Coordinate derivatives of the finite-time odometer. Independent atomless scenery
excludes all preactivation ties, and the derivative obeys the linear recursion on
active sites.

The scenery is an independent field, that is the product measure over a family of
one-site laws `ν : Site d → Measure ℝ` that need not be identical, and the only
hypothesis on the laws is that the law at each site is an atomless probability
measure.  The exclusion of ties is proved one coordinate at a time by splicing a
fresh value into that coordinate, which uses the law of that coordinate alone, so it
does not require the coordinates to share a law.  The identically distributed field
is the constant family, recorded as a corollary.  The derivative recursion
`hasDerivAt_odometerOf` is pathwise and does not mention a law.
-/
import Sandpile.Support.OriginKilled
import Sandpile.Support.Concentration
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

/-- **A strictly monotone coordinate avoids every value, almost surely.**  If the value
of a measurable functional of the field is an injective function of the coordinate `i`
with the rest of the field held fixed, then under the product of a family of
probability measures whose `i`-th member has no atoms, the functional almost surely
differs from any given level.  Only the law at `i` is used. -/
theorem ae_ne_of_update_injective {ι : Type*} [DecidableEq ι]
    (ν : ι → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (i : ι) [NullSingletonClass (ν i)]
    {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    (hupdate : ∀ ξ, Function.Injective (fun z => F (Function.update ξ i z))) (c : ℝ) :
    ∀ᵐ ξ ∂Measure.infinitePi ν, F ξ ≠ c := by
  set P := Measure.infinitePi ν
  have hup := LatticeProb.measurePreserving_update_infinitePi ν i
  have hset : MeasurableSet {ξ : ι → ℝ | F ξ = c} :=
    measurableSet_eq_fun hF measurable_const
  rw [ae_iff]
  change P {ξ : ι → ℝ | ¬ F ξ ≠ c} = 0
  simp only [not_not]
  rw [← hup.measure_preimage hset.nullMeasurableSet,
    Measure.prod_apply (hup.measurable hset)]
  have hf (ξ : ι → ℝ) : ν i {z : ℝ | F (Function.update ξ i z) = c} = 0 := by
    apply Set.Subsingleton.measure_zero
    intro a ha b hb
    exact hupdate ξ (ha.trans hb.symm)
  change (∫⁻ ξ, ν i {z : ℝ | F (Function.update ξ i z) = c} ∂P) = 0
  simp only [hf, lintegral_zero]

/-- The preactivation `ζ x + avg u_n x` is a measurable function of the scenery. -/
theorem measurable_odometer_preactivation {d : ℕ} (n : ℕ) (x : Site d) :
    Measurable (fun ζ : Site d → ℝ => ζ x + avg (odometerOf ζ n) x) := by
  apply (measurable_pi_apply x).add
  unfold avg LatticeProb.walkOp
  exact (Finset.measurable_sum _ fun i _ =>
    (measurable_odometerOf n (x + unit i)).add
      (measurable_odometerOf n (x - unit i))).div_const _

/-- **No preactivation tie, for independent atomless scenery.**  Under the product of
a family of atomless probability laws, one for each site, almost surely no site has
its preactivation `ζ x + avg u_n x` exactly at the activation threshold `0`, at any
time `n`. -/
theorem ae_odometer_preactivation_ne_zero_pi {d : ℕ}
    (ν : Site d → Measure ℝ) [∀ x, IsProbabilityMeasure (ν x)]
    [∀ x, NullSingletonClass (ν x)] :
    ∀ᵐ ζ ∂Measure.infinitePi ν, ∀ n : ℕ, ∀ x : Site d,
      ζ x + avg (odometerOf ζ n) x ≠ 0 := by
  rw [ae_all_iff]
  intro n
  rw [ae_all_iff]
  intro x
  apply ae_ne_of_update_injective ν x (measurable_odometer_preactivation n x)
  intro ζ
  apply StrictMono.injective
  intro a b hab
  simp only [Function.update_self]
  apply add_lt_add_of_lt_of_le hab
  apply avg_mono_le
  intro y
  apply odometerOf_mono
  intro w
  by_cases hw : w = x
  · subst w; simpa only [Function.update_self] using hab.le
  · simp only [Function.update_of_ne hw, le_refl]

/-- The identically distributed case of `ae_odometer_preactivation_ne_zero_pi`: the
constant family of one-site laws. -/
theorem ae_odometer_preactivation_ne_zero {d : ℕ}
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    ∀ᵐ ζ ∂LatticeProb.iidLaw d ν, ∀ n : ℕ, ∀ x : Site d,
      ζ x + avg (odometerOf ζ n) x ≠ 0 :=
  ae_odometer_preactivation_ne_zero_pi (fun _ : Site d => ν)

/-- The Jacobian of the finite-time odometer in the coordinate `ζ(z)`, defined by the
linear recursion on active sites. -/
noncomputable def odometerJacobian {d : ℕ} (ζ : Site d → ℝ) : ℕ → Site d → Site d → ℝ
  | 0, _, _ => 0
  | n + 1, x, z => if 0 < odometerOf ζ (n + 1) x then
      (if x = z then 1 else 0) + avg (fun y => odometerJacobian ζ n y z) x else 0

/-- **Pathwise derivative of the odometer.**  For any scenery with no preactivation tie,
the odometer at time `n` and site `x` is differentiable in the single coordinate `ζ(z)`
with derivative `odometerJacobian ζ n x z`.  No law of the scenery enters. -/
theorem hasDerivAt_odometerOf {d : ℕ} (ζ : Site d → ℝ)
    (hζ : ∀ n : ℕ, ∀ x : Site d, ζ x + avg (odometerOf ζ n) x ≠ 0) :
    ∀ n : ℕ, ∀ x z : Site d,
      HasDerivAt (fun h : ℝ => odometerOf (Function.update ζ z h) n x)
        (odometerJacobian ζ n x z) (ζ z) := by
  intro n
  induction n with
  | zero => intro x z; exact hasDerivAt_const _ _
  | succ n ih =>
    intro x z
    let f (h : ℝ) := Function.update ζ z h x + avg (odometerOf (Function.update ζ z h) n) x
    have hcoord : HasDerivAt (fun h : ℝ => Function.update ζ z h x)
        (if x = z then 1 else 0) (ζ z) := by
      by_cases hx : x = z
      · subst x; simpa using hasDerivAt_id' (ζ z)
      · simpa only [Function.update_of_ne hx, if_neg hx] using hasDerivAt_const (ζ z) (ζ x)
    have havg : HasDerivAt (fun h => avg (odometerOf (Function.update ζ z h) n) x)
        (avg (fun y => odometerJacobian ζ n y z) x) (ζ z) := by
      unfold avg LatticeProb.walkOp
      exact (HasDerivAt.fun_sum fun i _ => (ih (x + unit i) z).add (ih (x - unit i) z)).div_const _
    have hf : HasDerivAt f ((if x = z then 1 else 0) +
        avg (fun y => odometerJacobian ζ n y z) x) (ζ z) := hcoord.add havg
    have hfv : f (ζ z) = ζ x + avg (odometerOf ζ n) x := by simp [f]
    rcases lt_or_gt_of_ne (hζ n x) with hn | hp
    · have hfn : f (ζ z) < 0 := by simpa only [hfv] using hn
      have hact : ¬ 0 < odometerOf ζ (n + 1) x := by
        change ¬ 0 < max 0 (ζ x + avg (odometerOf ζ n) x)
        rw [max_eq_left hn.le]
        exact lt_irrefl _
      simp only [odometerJacobian, if_neg hact]
      apply (hasDerivAt_const (ζ z) (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [hf.continuousAt (gt_mem_nhds hfn)] with h hh
      exact max_eq_left hh.le
    · have hfp : 0 < f (ζ z) := by simpa only [hfv] using hp
      have hact : 0 < odometerOf ζ (n + 1) x := hp.trans_le (le_max_right _ _)
      simp only [odometerJacobian, if_pos hact]
      apply hf.congr_of_eventuallyEq
      filter_upwards [hf.continuousAt (lt_mem_nhds hfp)] with h hh
      exact max_eq_right hh.le

end Sandpile
