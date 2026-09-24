/-
The parts of case (b) of `prop:dgt4-contact-asymptotics` that the shared
probability library now supplies, and the reduction of its threshold asymptotic
to one statement that it does not.

Case (b) has `\kappa=1-1/\alpha` and threshold field `J=-G(0,0)\zeta`
(`sandpile.tex:5454-5455`), so its threshold probability is the one-site lower
tail `\P(-\zeta(0)>\E u_n(0)/G(0,0))` (`Support/Dgt4CaseB.lean`).  The passage
from the two estimates of `sandpile.tex:5318-5326` to the proposition runs, at
`sandpile.tex:5328-5336`, through

  `\E(-\zeta(0)-t)_+\sim t\P(-\zeta(0)>t)/(\alpha-1)`, Karamata for the
  integrated tail, and
  `\P(-\zeta(0)>t)\int_0^t dr/\E(-\zeta(0)-r)_+\to1-1/\alpha`, Karamata at the
  origin,

and then "summing over $n$", which is the Stolz-Cesaro theorem already in
`Support/Dgt4ThresholdChain.lean`.  The first is the library's
`karamata_integrated_tail`; the second is not in the library and is carried here
as `KaramataOriginTail`.
-/
import Sandpile.Support.Dgt4CaseB
import LatticeProb.Prob.Karamata

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

/-- `eq:dgt4-frechet-integrated-tail` (`sandpile.tex:5307-5309`):
`\E(-\zeta(0)-t)_+\sim t\P(-\zeta(0)>t)/(\alpha-1)`.  This is Karamata's theorem for the
integrated tail, proved in the shared library. -/
theorem frechet_integrated_tail (ν : Measure ℝ) [IsProbabilityMeasure ν] {α : ℝ} (hα : 1 < α)
    (hrv : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun r : ℝ => (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
        atTop (𝓝 (lam ^ (-α)))) :
    Tendsto (fun t : ℝ => (∫ z, max (-z - t) 0 ∂ν) / (t * (ν (Set.Iio (-t))).toReal))
      atTop (𝓝 (1 / (α - 1))) :=
  LatticeProb.karamata_integrated_tail hα hrv

/-- The Karamata statement at the ORIGIN that `sandpile.tex:5323` uses:
"$\P(-\zeta(0)>t)\int_0^t dr/\E(-\zeta(0)-r)_+\to1-1/\alpha$".  It is the direct half of
Karamata's theorem for `1/I`, which is regularly varying of index `\alpha-1`; the library's
`karamata_tail_integral` integrates to infinity and does not give it. -/
def KaramataOriginTail (ν : Measure ℝ) (κ : ℝ) : Prop :=
  Tendsto (fun t : ℝ => (ν (Set.Iio (-t))).toReal *
      ∫ r in Set.Ioc 0 t, (∫ z, max (-z - r) 0 ∂ν)⁻¹) atTop (𝓝 κ)

/-- Case (b), "summing over `n`" (`sandpile.tex:5323-5331`): the threshold asymptotic
`\P(-G(0,0)\zeta(0)>\E u_n(0))\sim G(0,0)\kappa/n` from the increments of
`\int_0^{\E u_n(0)/G(0,0)}dr/\E(-\zeta(0)-r)_+` and the Karamata statement at the origin.
The Stolz-Cesaro step is `tendsto_div_nat_of_tendsto_sub`. -/
theorem thresholdTailAsymptotics_linear_of_karamata
    (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    (hG : 0 < Sandpile.green d 0 0) {κ : ℝ}
    (hinf : Tendsto (fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
      atTop atTop)
    (hkar : KaramataOriginTail ν κ)
    (hincr : Tendsto (fun n : ℕ =>
        (∫ r in Set.Ioc 0 (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n + 1) /
            Sandpile.green d 0 0), (∫ z, max (-z - r) 0 ∂ν)⁻¹) -
          ∫ r in Set.Ioc 0 (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0), (∫ z, max (-z - r) 0 ∂ν)⁻¹)
      atTop (𝓝 (Sandpile.green d 0 0)⁻¹)) :
    ThresholdTailAsymptotics d ν
      (fun σ x => -(Sandpile.green d 0 0 * Sandpile.scenery d σ x)) κ := by
  set r : ℕ → ℝ := fun n =>
    Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0 with hrdef
  set A : ℝ → ℝ := fun t => ∫ s in Set.Ioc 0 t, (∫ z, max (-z - s) 0 ∂ν)⁻¹ with hAdef
  have hstolz : Tendsto (fun n : ℕ => A (r n) / (n : ℝ)) atTop (𝓝 (Sandpile.green d 0 0)⁻¹) :=
    tendsto_div_nat_of_tendsto_sub hincr
  have hprod : Tendsto (fun n : ℕ => (ν (Set.Iio (-(r n)))).toReal * A (r n)) atTop (𝓝 κ) := by
    simpa [Function.comp_def] using hkar.comp hinf
  have hne : (Sandpile.green d 0 0)⁻¹ ≠ 0 := inv_ne_zero hG.ne'
  have hdiv := hprod.div hstolz hne
  have hfin : κ / (Sandpile.green d 0 0)⁻¹ = Sandpile.green d 0 0 * κ := by
    rw [div_eq_mul_inv, inv_inv, mul_comm]
  rw [hfin] at hdiv
  have hpos : ∀ᶠ n : ℕ in atTop, A (r n) / (n : ℝ) ≠ 0 :=
    hstolz.eventually_ne hne
  refine (thresholdTailAsymptotics_linear_iff d ν hd hG κ).mpr ?_
  refine hdiv.congr' ?_
  filter_upwards [hpos, Filter.eventually_gt_atTop 0] with n hn hn0
  simp only [Pi.div_apply]
  have hAne : A (r n) ≠ 0 := by
    intro h
    apply hn
    rw [h, zero_div]
  have hnne : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
  field_simp
  ring

end Sandpile
