import Sandpile.Support.Dgt4ABandIndependence
import Sandpile.Support.OriginKilled

/-!
# The increment replacement at the sandpile law

`eq:dgt4-band-increment-replacement` at the sandpile law (`sandpile.tex:6171-6181`), assembled
into `meanOdometer_increment_sub_frozen_le`. The one-step mean increment of the odometer at the
origin is the mean overshoot of the scenery above the ORIGIN-FROZEN average `W_n`
(`Sandpile.origin_frozen_identities`), that average is independent of the scenery value at the
origin (`integral_posPart_eq_integral_scenery`), and replacing the random level `W_n` by the
frozen mean level `b_n` costs what `integral_abs_posPart_sub_le` says it costs. Putting the
three together gives

  `|E u_{n+1}(0) - E u_n(0) - E(ξ - b_n)_+| ≤ (below-band term) + (level term)`,

which is the paper's increment replacement, with the level term carrying `E|W_n - b_n|` and not
any identification of the two levels. `measure_contact_symmDiff_le` gives the analogous contact
error `eq:dgt4-band-contact-error`, bounding the symmetric difference between the contact event
at the origin and the threshold event at the frozen level `b`.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile

/-- **The increment replacement at the sandpile law.**  The one-step mean
increment of the odometer differs from the mean overshoot above the frozen level
`b` by at most the exponentially weighted term below the band plus `E|W_n - b|`
times the mass above the bottom of the band. -/
theorem meanOdometer_increment_sub_frozen_le
    (P : BandParameters) (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0) (hint : Integrable id ν)
    {lam : ℝ} (hlam : 0 < lam) (k n : ℕ) {b : ℝ} (hb : P.l1 * P.level k ≤ b)
    (hposν : Integrable (fun z : ℝ => max (-z) 0) ν)
    (hνw : ∀ w : ℝ, Integrable (fun z : ℝ => max (-z - w) 0) ν)
    (hWiid : Integrable (fun ζ : Site d → ℝ => avg (originOdometer ζ n) 0)
      (LatticeProb.iidLaw d ν))
    (hWexp : Integrable (fun σ =>
        Real.exp (-(lam * avg (originOdometer (scenery d σ) n) 0)))
      (centeredMassLaw d ν))
    (hFint : Integrable
      (fun σ => ∫ z, max (-z - avg (originOdometer (scenery d σ) n) 0) 0 ∂ν)
      (centeredMassLaw d ν))
    (hDint : Integrable
      (fun σ => |(∫ z, max (-z - avg (originOdometer (scenery d σ) n) 0) 0 ∂ν)
        - ∫ z, max (-z - b) 0 ∂ν|) (centeredMassLaw d ν))
    (hWabs : Integrable
      (fun σ => |avg (originOdometer (scenery d σ) n) 0 - b|) (centeredMassLaw d ν)) :
    |(meanOdometer (centeredMassLaw d ν) (n + 1) - meanOdometer (centeredMassLaw d ν) n)
        - ∫ z, max (-z - b) 0 ∂ν|
      ≤ (∫ σ, Real.exp (-(lam * avg (originOdometer (scenery d σ) n) 0))
            ∂(centeredMassLaw d ν)) / (lam * Real.exp 1) *
          (∫ z, expWeightBelow lam (P.l1 * P.level k) z ∂ν)
        + (∫ σ, |avg (originOdometer (scenery d σ) n) 0 - b| ∂(centeredMassLaw d ν)) *
          (ν {z : ℝ | -(z) > P.l1 * P.level k}).toReal := by
  have hid := (origin_frozen_identities hd ν hatom hint hmean n).2.2
  have hid' : meanOdometer (centeredMassLaw d ν) (n + 1)
        - meanOdometer (centeredMassLaw d ν) n
      = ∫ σ, max (-(scenery d σ 0) - avg (originOdometer (scenery d σ) n) 0) 0
          ∂(centeredMassLaw d ν) := by
    rw [hid]
    exact integral_congr_ae (Filter.Eventually.of_forall fun σ => max_comm _ _)
  have hsplit := integral_posPart_eq_integral_scenery d hd ν n hposν hWiid
  rw [hid', hsplit]
  have hc : ∫ _σ : Site d → ℝ, (∫ z, max (-z - b) 0 ∂ν) ∂(centeredMassLaw d ν)
      = ∫ z, max (-z - b) 0 ∂ν := by
    simp
  have hsub : (∫ σ, (∫ z, max (-z - avg (originOdometer (scenery d σ) n) 0) 0 ∂ν)
        ∂(centeredMassLaw d ν)) - ∫ z, max (-z - b) 0 ∂ν
      = ∫ σ, ((∫ z, max (-z - avg (originOdometer (scenery d σ) n) 0) 0 ∂ν)
          - ∫ z, max (-z - b) 0 ∂ν) ∂(centeredMassLaw d ν) := by
    rw [integral_sub hFint (integrable_const _), hc]
  rw [hsub]
  refine le_trans abs_integral_le_integral_abs ?_
  exact integral_abs_posPart_sub_le P ν hlam k (centeredMassLaw d ν)
    (fun σ => avg (originOdometer (scenery d σ) n) 0) hb hνw hWexp hDint hWabs

/-- **The contact error at the sandpile law.**  The contact event
`{u_{n+1}(0) = 0}` is, almost surely, the threshold event at the origin-frozen
average `W_n` (`Sandpile.origin_frozen_identities`, first clause), so the
symmetric difference between it and the threshold event at the frozen level `b`
is controlled by exactly the bound `integral_measure_symmDiff_le` gives, with the
level entering only through `E|W_n - b|`.  This is the paper's
`eq:dgt4-band-contact-error`. -/
theorem measure_contact_symmDiff_le
    (P : BandParameters) (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0) (hint : Integrable id ν)
    (k n : ℕ) {C : ℝ} (hC : 0 < C)
    (hdens : ∀ t : ℝ, P.l1 * P.level k < t → t ≤ P.level k → ∀ ε : ℝ, 0 < ε →
      (ν (Icc (-(t + ε)) (-t))).toReal / ε ≤ C * P.weight k / P.level k)
    {b lam : ℝ} (hlam : 0 < lam) (hb : P.l1 * P.level k ≤ b)
    (hWexp : Integrable (fun σ =>
        Real.exp (-(lam * avg (originOdometer (scenery d σ) n) 0)))
      (centeredMassLaw d ν))
    (hSint : Integrable (fun σ =>
        (ν (symmDiff {z : ℝ | -(z) > avg (originOdometer (scenery d σ) n) 0}
          {z : ℝ | -(z) > b})).toReal) (centeredMassLaw d ν))
    (hS1int : Integrable (fun σ =>
        (ν {z : ℝ | avg (originOdometer (scenery d σ) n) 0 < -z ∧
          -z ≤ P.l1 * P.level k}).toReal) (centeredMassLaw d ν))
    (hWabs : Integrable
      (fun σ => |avg (originOdometer (scenery d σ) n) 0 - b|) (centeredMassLaw d ν)) :
    ((centeredMassLaw d ν) (symmDiff
        {σ : Site d → ℝ | odometer σ (n + 1) 0 = 0}
        {σ : Site d → ℝ | -(scenery d σ 0) > b})).toReal
      ≤ (∫ σ, Real.exp (-(lam * avg (originOdometer (scenery d σ) n) 0))
            ∂(centeredMassLaw d ν)) *
          (∫ z, expWeightBelow lam (P.l1 * P.level k) z ∂ν)
        + C * P.weight k / P.level k *
          ∫ σ, |avg (originOdometer (scenery d σ) n) 0 - b| ∂(centeredMassLaw d ν)
        + (ν {z : ℝ | -(z) > P.level k}).toReal := by
  have hcontact : (∀ᵐ σ ∂centeredMassLaw d ν,
      odometer σ (n + 1) 0 = 0 ↔
        avg (originOdometer (scenery d σ) n) 0 < -scenery d σ 0) :=
    (origin_frozen_identities hd ν hatom hint hmean n).1
  have hset : {σ : Site d → ℝ | odometer σ (n + 1) 0 = 0}
      =ᵐ[centeredMassLaw d ν]
      {σ : Site d → ℝ | -(scenery d σ 0) > avg (originOdometer (scenery d σ) n) 0} :=
    Filter.eventuallyEq_set.mpr (hcontact.mono fun σ hσ => hσ)
  have hmeas : (centeredMassLaw d ν) (symmDiff
        {σ : Site d → ℝ | odometer σ (n + 1) 0 = 0}
        {σ : Site d → ℝ | -(scenery d σ 0) > b})
      = (centeredMassLaw d ν) (symmDiff
        {σ : Site d → ℝ | -(scenery d σ 0) > avg (originOdometer (scenery d σ) n) 0}
        {σ : Site d → ℝ | -(scenery d σ 0) > b}) :=
    measure_congr (hset.symmDiff (Filter.EventuallyEq.refl _ _))
  rw [hmeas, measure_symmDiff_threshold_eq_integral_scenery d hd ν n b]
  exact integral_measure_symmDiff_le P ν k hC hdens (centeredMassLaw d ν)
    (fun σ => avg (originOdometer (scenery d σ) n) 0) hlam hb hWexp hSint hS1int hWabs

end Sandpile.Support
