import Sandpile.Support.ExitValueSwap
import Sandpile.Support.PayoffSplit
import Sandpile.Support.D4CritCube

/-!
# Step 1a of the dimension-four critical-level percolation proof

Step 1a of the dimension-four critical-level percolation proof
(`sandpile.tex:4008-4020`): the mean of the localized exit value `Y_r(z)` is at
least the localized mean odometer times the probability that the walk has left
the box `Q(z,r)` by time `A_ex r²`.  The walk average and the scenery average
are exchanged by the Fubini swap of `localizedExitAverage_expectation_swap`, and
on the exit event the inner scenery average is the localized mean of
`cor:mean-localization` at the exit site.
-/

open MeasureTheory

noncomputable section
namespace Sandpile

/-- Step 1a: the exit value has mean at least `(1 - p) m`, where `m` is a lower
bound for the localized mean odometer at every site and `p` bounds the
probability that the walk has not left `Q(z,r)` by time `A_ex r²`. -/
theorem exit_value_mean_lower
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hpos : Integrable (fun z : ℝ => max z 0) ν)
    (Aex : ℕ) (Aloc : ℝ) (r : ℕ) (z : Site 4) (m p : ℝ) (hm : 0 ≤ m) (hp0 : 0 ≤ p)
    (hloc : ∀ w : Site 4,
      m ≤ ∫ ζ, localizedOdometer (eaCube w (Aloc * r)) ζ (r ^ 2) w
        ∂(LatticeProb.iidLaw 4 ν))
    (hexit : (walkLaw 4 z) {X : ℕ → Site 4 |
        ¬ (exitNat (eaCube z (r : ℝ)) (Aex * r ^ 2) X ≤ Aex * r ^ 2)} ≤ ENNReal.ofReal p) :
    (1 - p) * m ≤ ∫ ζ, eaExitValue Aex Aloc r ζ z ∂(LatticeProb.iidLaw 4 ν) := by
  classical
  haveI := hν
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  haveI : IsProbabilityMeasure (walkLaw 4 z) := walkLaw_isProbabilityMeasure 4 z
  set P := LatticeProb.iidLaw 4 ν with hP
  set D : Set (Site 4) := eaCube z (r : ℝ) with hD
  set N : ℕ := Aex * r ^ 2 with hN
  set E : Site 4 → Set (Site 4) := fun w => eaCube w (Aloc * r) with hE
  set τ := stopBeforeExit D N (fun _ => N) with hτ
  set f : Site 4 → ℝ := fun w => ∫ ζ, localizedOdometer (E w) ζ (r ^ 2) w ∂P with hf
  -- the exit value is the localized exit average
  have he : ∀ ζ : Site 4 → ℝ,
      eaExitValue Aex Aloc r ζ z = localizedExitAverage D N E (r ^ 2) ζ z := by
    intro ζ
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun X =>
      (localizedExitPayoff_eq_indicator D N E (r ^ 2) ζ X).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall he),
    localizedExitAverage_expectation_swap (by norm_num) D N E (r ^ 2) z ν hν hpos]
  -- the payoff vanishes off the exit event, and is at least `m` on it
  set A : Set (ℕ → Site 4) := {X : ℕ → Site 4 | exitNat D N X ≤ N} with hA
  have hAmeas : MeasurableSet A := measurableSet_exited D N
  have hpay : ∀ X, (if X (τ X) ∈ D then 0 else f (X (τ X))) =
      Set.indicator A (fun X => if X (τ X) ∈ D then 0 else f (X (τ X))) X := by
    intro X
    by_cases hX : X ∈ A
    · rw [Set.indicator_of_mem hX]
    · rw [Set.indicator_of_notMem hX, if_pos]
      by_contra hc
      exact hX (notMem_stopBeforeExit_iff D N X |>.mp hc)
  have hint : Integrable (fun X : ℕ → Site 4 => if X (τ X) ∈ D then 0 else f (X (τ X)))
      (walkLaw 4 z) := integrable_exitAverage_payoff (by norm_num) D N f z
  have hge : ∀ X ∈ A, m ≤ (if X (τ X) ∈ D then 0 else f (X (τ X))) := by
    intro X hX
    rw [if_neg ((notMem_stopBeforeExit_iff D N X).mpr hX)]
    exact hloc _
  have hsplit := Sandpile.Support.PayoffSplit.payoff_split (walkLaw 4 z)
    (fun X : ℕ → Site 4 => if X (τ X) ∈ D then 0 else f (X (τ X))) m A hAmeas hm hge
    (measure_lt_top _ _) hint
  -- the exit event has probability at least `1 - p`
  have hcompl : Aᶜ = {X : ℕ → Site 4 | ¬ (exitNat D N X ≤ N)} := rfl
  have hpc : ((walkLaw 4 z) Aᶜ).toReal ≤ p := by
    rw [hcompl]
    exact ENNReal.toReal_le_of_le_ofReal hp0 hexit
  have hAprob : 1 - p ≤ ((walkLaw 4 z) A).toReal := by
    have hsum := measure_add_measure_compl (μ := walkLaw 4 z) hAmeas
    have h1 : ((walkLaw 4 z) A).toReal + ((walkLaw 4 z) Aᶜ).toReal = 1 := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum]
      simp
    linarith
  have hfin : ∫ X in A, (if X (τ X) ∈ D then 0 else f (X (τ X))) ∂(walkLaw 4 z)
      = ∫ X, (if X (τ X) ∈ D then 0 else f (X (τ X))) ∂(walkLaw 4 z) := by
    rw [← integral_indicator hAmeas]
    exact integral_congr_ae (Filter.Eventually.of_forall fun X => (hpay X).symm)
  rw [hfin] at hsplit
  calc (1 - p) * m ≤ ((walkLaw 4 z) A).toReal * m :=
        mul_le_mul_of_nonneg_right hAprob hm
    _ = m * ((walkLaw 4 z) A).toReal := by ring
    _ ≤ _ := hsplit

end Sandpile
