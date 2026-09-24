/-
The odometer dominates a stopped scenery sum and a localized continuation
at the exit.  The remaining-time odometer is a supermartingale after adding
the accumulated scenery, which gives the finite-range lower bound.
-/
import Sandpile.Support.OriginKilled
import Sandpile.Support.KilledWalk

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- The stopped one-step martingale identity for an arbitrary deterministic field. -/
theorem integral_stopped_field_increment (hd : 1 ≤ d) (x : Site d) (f : Site d → ℝ) (n : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) :
    Integrable (fun ξ => (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
        (f (walkPath x ξ (n + 1)) - avg f (walkPath x ξ n)))
        (Measure.infinitePi fun _ : ℕ => stepLaw d) ∧
      (∫ ξ, (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
        (f (walkPath x ξ (n + 1)) - avg f (walkPath x ξ n))
        ∂(Measure.infinitePi fun _ : ℕ => stepLaw d)) = 0 := by
  have h := integral_increment_zero hd x f (n + 2) n hτ
  have he : membrane f ((n + 2) - n - 1) = f := by
    funext y
    simp [membrane, avg, LatticeProb.walkOp, LatticeProb.nbrSum]
  rw [he] at h
  exact h

theorem odometer_stopped_telescope_le (ζ : Site d → ℝ) (t : ℕ) (X : ℕ → Site d)
    (N : ℕ) (hN : N ≤ t) :
    sceneryPartialSum ζ N X + odometerOf ζ (t - N) (X N) ≤
      odometerOf ζ t (X 0) + ∑ n ∈ Finset.range t,
        (if n < N then (1 : ℝ) else 0) *
          (odometerOf ζ (t - n - 1) (X (n + 1)) - avg (odometerOf ζ (t - n - 1)) (X n)) := by
  classical
  set a := fun n => sceneryPartialSum ζ n X + odometerOf ζ (t - n) (X n)
  have ha := telescope_stopped a hN
  have h0 : a 0 = odometerOf ζ t (X 0) := by simp [a, sceneryPartialSum]
  rw [h0] at ha
  change a N ≤ _
  rw [ha]
  gcongr with n hn
  by_cases hnN : n < N
  · rw [if_pos hnN, if_pos hnN, one_mul]
    have hnt : n < t := Finset.mem_range.mp hn
    have he : t - n = (t - n - 1) + 1 := by omega
    have he' : t - (n + 1) = t - n - 1 := by omega
    have hsp : sceneryPartialSum ζ (n + 1) X = sceneryPartialSum ζ n X + ζ (X n) := by
      simp only [sceneryPartialSum, Finset.sum_range_succ]
    dsimp [a]
    rw [hsp, he', he, odometerOf]
    simp only [Nat.add_sub_cancel]
    linarith [le_max_right 0 (ζ (X n) + avg (odometerOf ζ (t - n - 1)) (X n))]
  · rw [if_neg hnN, if_neg hnN, zero_mul]

theorem measurable_stopped_value (t : ℕ) (F : ℕ → Site d → ℝ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    Measurable (fun X : ℕ → Site d => F (τ X) (X (τ X))) := by
  refine measurable_of_dependsOn t _ fun X Y hXY => ?_
  have ht := isWalkStopping_dependsOn hτ hτt X Y hXY
  rw [← ht, hXY _ (hτt X)]

theorem integrable_stopped_value (hd : 1 ≤ d) (x : Site d) (t : ℕ) (F : ℕ → Site d → ℝ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    Integrable (fun X : ℕ → Site d => F (τ X) (X (τ X))) (walkLaw d x) := by
  haveI : NeZero d := ⟨by omega⟩
  refine (integrable_const (∑ j ∈ Finset.range (t + 1), ∑ z ∈ boxFinset x t, |F j z|)).mono'
    (measurable_stopped_value t F hτ hτt).aestronglyMeasurable ?_
  filter_upwards [ae_boxDist_walk hd x] with X hX
  rw [Real.norm_eq_abs]
  have ha : |F (τ X) (X (τ X))| ≤ ∑ z ∈ boxFinset x t, |F (τ X) z| :=
    Finset.single_le_sum (f := fun z => |F (τ X) z|) (fun _ _ => abs_nonneg _)
      (mem_boxFinset ((hX _).trans (hτt X)))
  have hb : (∑ z ∈ boxFinset x t, |F (τ X) z|) ≤
      ∑ j ∈ Finset.range (t + 1), ∑ z ∈ boxFinset x t, |F j z| :=
    Finset.single_le_sum (f := fun j => ∑ z ∈ boxFinset x t, |F j z|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hτt X)))
  exact ha.trans hb

/-- The odometer dominates scenery collected until a bounded stopping time,
plus the odometer for the remaining number of updates at the stopped site. -/
theorem integral_stopped_odometer_le (hd : 1 ≤ d) (x : Site d) (ζ : Site d → ℝ) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    (∫ X, sceneryPartialSum ζ (τ X) X + odometerOf ζ (t - τ X) (X (τ X)) ∂walkLaw d x) ≤
      odometerOf ζ t x := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  set P := Measure.infinitePi (fun _ : ℕ => stepLaw d)
  have hpay : Integrable (fun X => sceneryPartialSum ζ (τ X) X +
      odometerOf ζ (t - τ X) (X (τ X))) (walkLaw d x) :=
    (integrable_stoppedScenery_walk hd x ζ t hτ hτt).add
    (integrable_stopped_value hd x t (fun j => odometerOf ζ (t - j)) hτ hτt)
  have hmp : MeasurePreserving (walkPath x) P (walkLaw d x) := ⟨measurable_walkPath x, rfl⟩
  have hI : Integrable (fun ξ => sceneryPartialSum ζ (τ (walkPath x ξ)) (walkPath x ξ) +
      odometerOf ζ (t - τ (walkPath x ξ)) (walkPath x ξ (τ (walkPath x ξ)))) P :=
    hmp.integrable_comp_of_integrable hpay
  have hinc := fun n => integral_stopped_field_increment hd x (odometerOf ζ (t - n - 1)) n hτ
  have hsum : Integrable (fun ξ : ℕ → Site d => ∑ n ∈ Finset.range t,
      (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
        (odometerOf ζ (t - n - 1) (walkPath x ξ (n + 1)) -
          avg (odometerOf ζ (t - n - 1)) (walkPath x ξ n))) P :=
    integrable_finsetSum _ fun n _ => (hinc n).1
  have h := integral_mono hI ((integrable_const (odometerOf ζ t x)).add hsum) fun ξ => by
    have h := odometer_stopped_telescope_le ζ t (walkPath x ξ) (τ (walkPath x ξ)) (hτt _)
    rw [walkPath_zero] at h
    change _ ≤ odometerOf ζ t x + _
    exact h
  change (∫ ξ, sceneryPartialSum ζ (τ (walkPath x ξ)) (walkPath x ξ) +
    odometerOf ζ (t - τ (walkPath x ξ)) (walkPath x ξ (τ (walkPath x ξ))) ∂P) ≤
    ∫ ξ, odometerOf ζ t x + ∑ n ∈ Finset.range t,
      (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
        (odometerOf ζ (t - n - 1) (walkPath x ξ (n + 1)) -
          avg (odometerOf ζ (t - n - 1)) (walkPath x ξ n)) ∂P at h
  rw [integral_add (integrable_const _) hsum, integral_const,
    integral_finsetSum (Finset.range t) (fun n _ => (hinc n).1)] at h
  have hzero : ∀ n ∈ Finset.range t, (∫ ξ, (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
      (odometerOf ζ (t - n - 1) (walkPath x ξ (n + 1)) -
        avg (odometerOf ζ (t - n - 1)) (walkPath x ξ n)) ∂P) = 0 := fun n _ => (hinc n).2
  dsimp only [P] at hzero
  rw [Finset.sum_congr rfl hzero] at h
  simp only [Finset.sum_const_zero, add_zero, probReal_univ, one_smul] at h
  rw [integral_walkLaw x hpay.aestronglyMeasurable]
  exact h

noncomputable def localizedExitPayoff (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) (ζ : Site d → ℝ) (X : ℕ → Site d) : ℝ := by
  classical
  let τ := stopBeforeExit D N (fun _ => N)
  exact if X (τ X) ∈ D then 0 else localizedOdometer (E (X (τ X))) ζ m (X (τ X))

theorem localizedExitPayoff_eq_indicator (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) (ζ : Site d → ℝ) (X : ℕ → Site d) :
    localizedExitPayoff D N E m ζ X = Set.indicator
      {X : ℕ → Site d | exitTime D X ≤ (N : ℕ∞)}
      (fun X => localizedOdometer (E (X (exitTime D X).toNat)) ζ m (X (exitTime D X).toNat)) X := by
  classical
  by_cases hx : exitNat D N X ≤ N
  · have ht : stopBeforeExit D N (fun _ => N) X = exitNat D N X := min_eq_right hx
    have he : exitTime D X ≤ (N : ℕ∞) := exitTime_le_iff.mpr hx
    rw [localizedExitPayoff, ht, if_neg (notMem_exitNat hx), Set.indicator_of_mem (show X ∈ {X : ℕ → Site d | exitTime D X ≤ (N : ℕ∞)} from he),
      exitTime_eq_exitNat hx, ENat.toNat_coe]
  · have ht : stopBeforeExit D N (fun _ => N) X = N := min_eq_left (le_of_not_ge hx)
    have he : ¬exitTime D X ≤ (N : ℕ∞) := fun h => hx (exitTime_le_iff.mp h)
    rw [localizedExitPayoff, ht, if_pos (mem_of_lt_exitNat (lt_of_not_ge hx) (le_refl N)),
      Set.indicator_of_notMem (show X ∉ {X : ℕ → Site d | exitTime D X ≤ (N : ℕ∞)} from he)]

theorem integrable_localizedExitPayoff (hd : 1 ≤ d) (x : Site d) (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) (ζ : Site d → ℝ) :
    Integrable (localizedExitPayoff D N E m ζ) (walkLaw d x) := by
  classical
  have hconst : IsWalkStopping (fun _ : ℕ → Site d => N) := by intro _ _ _ _ h; exact h
  have hs := isWalkStopping_stopBeforeExit (D := D) hconst (fun _ => le_refl N)
  exact integrable_stopped_value hd x N
    (fun _ y => if y ∈ D then 0 else localizedOdometer (E y) ζ m y) hs
    (stopBeforeExit_le (fun _ => le_refl N))

/-- A localized continuation at the exit can be inserted below the remaining-time
odometer in the stopped inequality. -/
theorem killedGreenPair_add_localizedExit_le (hd : 1 ≤ d) (x : Site d) (D : Set (Site d))
    (N m : ℕ) (E : Site d → Set (Site d)) (ζ : Site d → ℝ) :
    killedGreenPair D N ζ x + ∫ X, localizedExitPayoff D N E m ζ X ∂walkLaw d x ≤
      odometerOf ζ (N + m) x := by
  classical
  set τ := stopBeforeExit D N (fun _ => N)
  have hconst : IsWalkStopping (fun _ : ℕ → Site d => N) := by intro _ _ _ _ h; exact h
  have hτ : IsWalkStopping τ := isWalkStopping_stopBeforeExit hconst (fun _ => le_refl N)
  have hτN : ∀ X, τ X ≤ N := stopBeforeExit_le (fun _ => le_refl N)
  have hτt : ∀ X, τ X ≤ N + m := fun X => (hτN X).trans (Nat.le_add_right _ _)
  have hpay : ∀ X : ℕ → Site d, localizedExitPayoff D N E m ζ X ≤
      odometerOf ζ (N + m - τ X) (X (τ X)) := by
    intro X
    change (if X (τ X) ∈ D then 0 else localizedOdometer (E (X (τ X))) ζ m (X (τ X))) ≤ _
    split_ifs
    · exact odometerOf_nonneg _ _ _
    · exact (localizedOdometer_le_full hd _ ζ m _).trans
        (odometerOf_mono_time ζ _ (by have := hτN X; omega))
  have hsint := integrable_stoppedScenery_walk hd x ζ (N + m) hτ hτt
  have hu := integrable_stopped_value hd x (N + m) (fun j => odometerOf ζ (N + m - j)) hτ hτt
  have hb := integral_mono
    (hsint.add (integrable_localizedExitPayoff hd x D N E m ζ)) (hsint.add hu)
    (fun X => add_le_add le_rfl (hpay X))
  change (∫ X, sceneryPartialSum ζ (τ X) X + localizedExitPayoff D N E m ζ X ∂walkLaw d x) ≤
    ∫ X, sceneryPartialSum ζ (τ X) X + odometerOf ζ (N + m - τ X) (X (τ X)) ∂walkLaw d x at hb
  rw [integral_add hsint (integrable_localizedExitPayoff hd x D N E m ζ),
    integral_stoppedScenery_killed hd D N x ζ] at hb
  exact hb.trans (integral_stopped_odometer_le hd x ζ (N + m) hτ hτt)

end Sandpile
