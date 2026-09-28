import Sandpile.Support.Localization
import Sandpile.Support.ExitAverage
import Sandpile.Support.OriginKilled
import Sandpile.Support.StoppedOdometer
import Sandpile.Support.Stationary
import Sandpile.Support.ExitPayoffMeas

/-!
# Integrability of the exit payoff on the scenery-walk product

The exit payoff reads off the localized odometer at the site where a walk `X` stopped before
`stopBeforeExit D N (fun _ => N) X` first leaves `D`, paying `0` if it never left. This module
proves `integrable_uncurry_exit_payoff`: this payoff is integrable jointly in the scenery `ζ`
and the walk `X`, against the product of the i.i.d. scenery law `LatticeProb.iidLaw d ν` and the
walk law `walkLaw d x`. The argument uses `MeasureTheory.integrable_prod_iff`: the payoff is
integrable in `X` for every fixed `ζ` by `integrable_exitAverage_payoff`, and the resulting
`ζ`-indexed integral of the norm is bounded, uniformly in a full-measure set of scenery paths
of speed at most linear (`ae_prod_boxDist`), by the finite sum `∑ z ∈ boxFinset x N, odometerOf
ζ m z`, which is itself integrable by `integrable_odometerOf`.
-/

open MeasureTheory Filter Topology
open scoped Classical

namespace Sandpile

variable {d : ℕ}

/-- Integrability of the exit payoff over the product of the scenery law and
the walk law: the stopped localized odometer is integrable in the pair. -/
theorem integrable_uncurry_exit_payoff (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) (x : Site d) (ν : Measure ℝ)
    (hprob : IsProbabilityMeasure ν) (hpos : Integrable (fun z => max z 0) ν) :
    Integrable (fun p : (Site d → ℝ) × (ℕ → Site d) =>
      if p.2 (stopBeforeExit D N (fun _ => N) p.2) ∈ D then 0
      else localizedOdometer (E (p.2 (stopBeforeExit D N (fun _ => N) p.2))) p.1 m
        (p.2 (stopBeforeExit D N (fun _ => N) p.2)))
      ((LatticeProb.iidLaw d ν).prod (walkLaw d x)) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  have hmeas : AEStronglyMeasurable (fun p : (Site d → ℝ) × (ℕ → Site d) =>
      if p.2 (stopBeforeExit D N (fun _ => N) p.2) ∈ D then 0
      else localizedOdometer (E (p.2 (stopBeforeExit D N (fun _ => N) p.2))) p.1 m
        (p.2 (stopBeforeExit D N (fun _ => N) p.2)))
      ((LatticeProb.iidLaw d ν).prod (walkLaw d x)) :=
    (measurable_uncurry_exit_payoff hd D N E m).aestronglyMeasurable
  have hae : ∀ᵐ ζ ∂(LatticeProb.iidLaw d ν), Integrable (fun X : ℕ → Site d =>
      if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
      else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
        (X (stopBeforeExit D N (fun _ => N) X))) (walkLaw d x) :=
    Filter.Eventually.of_forall fun ζ =>
      integrable_exitAverage_payoff hd D N (fun w => localizedOdometer (E w) ζ m w) x
  have hτstop : IsWalkStopping (stopBeforeExit D N (fun _ => N)) :=
    isWalkStopping_stopBeforeExit (D := D) (isWalkStopping_const N) (fun _ => le_rfl)
  have hτt : ∀ X, stopBeforeExit D N (fun _ => N) X ≤ N + m := fun X =>
    (stopBeforeExit_le (fun _ : ℕ → Site d => le_refl N) X).trans (Nat.le_add_right _ _)
  have hH : Integrable (fun ζ : Site d → ℝ => ∑ z ∈ boxFinset x N, odometerOf ζ m z)
      (LatticeProb.iidLaw d ν) :=
    integrable_finsetSum _ fun z _ => integrable_odometerOf d ν hpos m z
  refine (MeasureTheory.integrable_prod_iff hmeas).mpr ⟨hae, ?_⟩
  have hmeas2 : StronglyMeasurable
      (fun p : (Site d → ℝ) × (ℕ → Site d) =>
        ‖if p.2 (stopBeforeExit D N (fun _ => N) p.2) ∈ D then 0
          else localizedOdometer (E (p.2 (stopBeforeExit D N (fun _ => N) p.2))) p.1 m
            (p.2 (stopBeforeExit D N (fun _ => N) p.2))‖) :=
    (measurable_uncurry_exit_payoff hd D N E m).norm.stronglyMeasurable
  have hmeas3 : StronglyMeasurable
      (fun ζ : Site d → ℝ => ∫ X : ℕ → Site d,
        ‖if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
          else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
            (X (stopBeforeExit D N (fun _ => N) X))‖ ∂walkLaw d x) :=
    StronglyMeasurable.integral_prod_right
      (f := fun (ζ : Site d → ℝ) (X : ℕ → Site d) =>
        ‖if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
          else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
            (X (stopBeforeExit D N (fun _ => N) X))‖) hmeas2
  have haeζ : ∀ᵐ ζ ∂(LatticeProb.iidLaw d ν),
      ∀ᵐ X ∂(walkLaw d x), ∀ n : ℕ, boxDist x (X n) ≤ n :=
    Measure.ae_ae_of_ae_prod (ae_prod_boxDist hd (LatticeProb.iidLaw d ν) x)
  have hptw : ∀ (ζ : Site d → ℝ) (X : ℕ → Site d), (∀ n : ℕ, boxDist x (X n) ≤ n) →
      (‖if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
      else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
        (X (stopBeforeExit D N (fun _ => N) X))‖)
        ≤ ∑ z ∈ boxFinset x N, odometerOf ζ m z := by
    intro ζ X hX
    by_cases hmem : X (stopBeforeExit D N (fun _ => N) X) ∈ D
    · simp only [if_pos hmem, norm_zero]
      exact Finset.sum_nonneg fun z _ => odometerOf_nonneg ζ m z
    · have hw := hX (stopBeforeExit D N (fun _ => N) X)
      have hle := stopBeforeExit_le (D := D) (t := N) (τ := fun x => N) (by simp) X
      have hmem2 : X (stopBeforeExit D N (fun _ => N) X) ∈ boxFinset x N :=
        mem_boxFinset (le_trans hw hle)
      have hbound := localizedOdometer_le_full hd
        (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
        (X (stopBeforeExit D N (fun _ => N) X))
      rw [if_neg hmem, Real.norm_eq_abs,
        abs_of_nonneg (localizedOdometer_nonneg hd
          (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m _)]
      exact le_trans hbound
        (Finset.single_le_sum (fun z _ => odometerOf_nonneg ζ m z) hmem2)
  refine Integrable.mono' hH hmeas3.aestronglyMeasurable ?_
  filter_upwards [haeζ] with ζ hXζ
  have hinteg : Integrable (fun X : ℕ → Site d =>
      if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
      else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
        (X (stopBeforeExit D N (fun _ => N) X))) (walkLaw d x) :=
    integrable_exitAverage_payoff hd D N
      (fun w => localizedOdometer (E w) ζ m w) x
  have hptae : ∀ᵐ X ∂(walkLaw d x),
      (‖if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
      else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
        (X (stopBeforeExit D N (fun _ => N) X))‖)
        ≤ ∑ z ∈ boxFinset x N, odometerOf ζ m z := hXζ.mono (hptw ζ)
  have hint : ∫ X : ℕ → Site d, ‖if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
      else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
        (X (stopBeforeExit D N (fun _ => N) X))‖ ∂walkLaw d x
      ≤ ∑ z ∈ boxFinset x N, odometerOf ζ m z := by
    calc ∫ X : ℕ → Site d, ‖if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
        else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
          (X (stopBeforeExit D N (fun _ => N) X))‖ ∂walkLaw d x
        ≤ ∫ X : ℕ → Site d, ∑ z ∈ boxFinset x N, odometerOf ζ m z ∂walkLaw d x :=
            integral_mono_of_nonneg (ae_of_all _ fun X => norm_nonneg _)
              (integrable_const _) hptae
      _ = ∑ z ∈ boxFinset x N, odometerOf ζ m z := by
            rw [integral_const]
            simp
  calc ‖∫ X : ℕ → Site d, ‖if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
        else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
          (X (stopBeforeExit D N (fun _ => N) X))‖ ∂walkLaw d x‖
      ≤ ∫ X : ℕ → Site d, ‖(‖if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
        else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
          (X (stopBeforeExit D N (fun _ => N) X))‖)‖ ∂walkLaw d x :=
          norm_integral_le_integral_norm _
    _ = ∫ X : ℕ → Site d, ‖if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
        else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
          (X (stopBeforeExit D N (fun _ => N) X))‖ ∂walkLaw d x :=
          integral_congr_ae (ae_of_all _ fun X => norm_norm _)
    _ ≤ ∑ z ∈ boxFinset x N, odometerOf ζ m z := hint

end Sandpile
