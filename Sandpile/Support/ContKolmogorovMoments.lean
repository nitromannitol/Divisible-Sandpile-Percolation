/-
Measurability and integrability of the interpolated rescaled field, the two
hypotheses the corrected quantitative Kolmogorov criterion asks of a process.

The criterion of `ContKolmogorovAssembly` is stated for a process indexed by a
compact box of `ℝ^k`; its two statements ask that every coordinate be measurable
and that the `p`-th moment of every increment be integrable, because a Bochner
integral of a non-integrable function is the junk value zero and the moment
bound would otherwise be vacuous.  This module supplies both for the
interpolated field `piField` of `ContKolmogorovAssembly`, uniformly in the
scale: the field is a finite linear functional of the scenery on a box
(`linInterp_eq_sum`), so it is measurable, and its `p`-th moment is integrable
as soon as the one-site law has a `p`-th moment, by the coordinate-Lipschitz
moment lemma `integrable_rpow_of_lip_fam` transported along the reading of the
sites (`measurePreserving_scenery_pick`).
-/
import Sandpile.Support.ContLinMoment
import Sandpile.Support.ContHeatPotentialFD

open MeasureTheory ProbabilityTheory
open Sandpile.Frozen.HeatPotentialInvariance

namespace Sandpile.Support

variable {d : ℕ}

/-- **The interpolated rescaled field is a measurable function of the
scenery.**  It is a finite linear functional of the scenery on the box the
interpolation reads (`linInterp_eq_sum`). -/
theorem integrable_linInterp_sub_rpow (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {p : ℝ} (hp : 1 ≤ p) (hint : Integrable (fun z => |z| ^ p) ν)
    (R r r' : ℝ) (w w' : Sandpile.Continuum.Space d) (s : Finset (Site d))
    (hps : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * r⌋₊ + 1) ⊆ s)
    (hqs : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w' i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * r'⌋₊ + 1) ⊆ s) :
    Integrable (fun σ : Site d → ℝ =>
      |linInterp d R (Sandpile.scenery d σ) r w
        - linInterp d R (Sandpile.scenery d σ) r' w'| ^ p)
      (Sandpile.centeredMassLaw d ν) := by
  classical
  haveI := ‹IsProbabilityMeasure ν›
  have hrep : ∀ σ : Site d → ℝ,
      linInterp d R (Sandpile.scenery d σ) r w
        - linInterp d R (Sandpile.scenery d σ) r' w'
      = ∑ i, (interpCoeff d R r w (Sandpile.siteEnum s i)
          - interpCoeff d R r' w' (Sandpile.siteEnum s i))
          * Sandpile.scenery d σ (Sandpile.siteEnum s i) := by
    intro σ
    rw [linInterp_eq_sum R r (Sandpile.scenery d σ) w hps,
      linInterp_eq_sum R r' (Sandpile.scenery d σ) w' hqs, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmeasF : Measurable (fun ξ : Fin s.card → ℝ =>
      ∑ i, (interpCoeff d R r w (Sandpile.siteEnum s i)
          - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * ξ i) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have hmeas : Measurable (fun ξ : Fin s.card → ℝ =>
      |∑ i, (interpCoeff d R r w (Sandpile.siteEnum s i)
          - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * ξ i| ^ p) :=
    hmeasF.abs.pow_const p
  have htarget : Integrable (fun ξ : Fin s.card → ℝ =>
      |∑ i, (interpCoeff d R r w (Sandpile.siteEnum s i)
          - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * ξ i| ^ p)
      (Measure.pi fun _ : Fin s.card => ν) :=
    LatticeProb.integrable_rpow_of_lip_fam (fun _ : Fin s.card => ν) hp
      (fun _ => hint) _ hmeasF _ (fun i => abs_nonneg _)
      (fun ξ i y => LatticeProb.abs_linear_sub_update_le _ _ i y)
  have hmp := measurePreserving_scenery_pick ν hd (Sandpile.siteEnum s)
    (Sandpile.siteEnum_injective s)
  refine (LatticeProb.integrable_comp_mp hmp _ hmeas.aestronglyMeasurable htarget).congr ?_
  filter_upwards with σ
  rw [hrep σ]

/-- **The `p`-th power of the field itself is integrable**, for `p ≥ 1`, as soon
as the one-site law has a `p`-th moment. -/
theorem integrable_linInterp_rpow (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {p : ℝ} (hp : 1 ≤ p) (hint : Integrable (fun z => |z| ^ p) ν)
    (R r : ℝ) (w : Sandpile.Continuum.Space d) (s : Finset (Site d))
    (hps : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * r⌋₊ + 1) ⊆ s) :
    Integrable (fun σ : Site d → ℝ =>
      |linInterp d R (Sandpile.scenery d σ) r w| ^ p)
      (Sandpile.centeredMassLaw d ν) := by
  classical
  haveI := ‹IsProbabilityMeasure ν›
  have hrep : ∀ σ : Site d → ℝ,
      linInterp d R (Sandpile.scenery d σ) r w
      = ∑ i, interpCoeff d R r w (Sandpile.siteEnum s i)
          * Sandpile.scenery d σ (Sandpile.siteEnum s i) := by
    intro σ
    rw [linInterp_eq_sum R r (Sandpile.scenery d σ) w hps]
  have hmeasF : Measurable (fun ξ : Fin s.card → ℝ =>
      ∑ i, interpCoeff d R r w (Sandpile.siteEnum s i) * ξ i) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have hmeas : Measurable (fun ξ : Fin s.card → ℝ =>
      |∑ i, interpCoeff d R r w (Sandpile.siteEnum s i) * ξ i| ^ p) :=
    hmeasF.abs.pow_const p
  have htarget : Integrable (fun ξ : Fin s.card → ℝ =>
      |∑ i, interpCoeff d R r w (Sandpile.siteEnum s i) * ξ i| ^ p)
      (Measure.pi fun _ : Fin s.card => ν) :=
    LatticeProb.integrable_rpow_of_lip_fam (fun _ : Fin s.card => ν) hp
      (fun _ => hint) _ hmeasF _ (fun i => abs_nonneg _)
      (fun ξ i y => LatticeProb.abs_linear_sub_update_le _ _ i y)
  have hmp := measurePreserving_scenery_pick ν hd (Sandpile.siteEnum s)
    (Sandpile.siteEnum_injective s)
  refine (LatticeProb.integrable_comp_mp hmp _ hmeas.aestronglyMeasurable htarget).congr ?_
  filter_upwards with σ
  rw [hrep σ]

end Sandpile.Support
