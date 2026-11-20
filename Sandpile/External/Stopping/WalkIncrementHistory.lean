import Sandpile.External.Stopping.WalkContinuity
import Sandpile.External.Stopping.StoppedWalkClockHistory
import Sandpile.External.Stopping.FutureIncrementPath
import Sandpile.External.Stopping.IndependentBlockObservations

/-!
# Walk observations and increment blocks

A walk history depends on the preceding increments, while differences between
later observations depend only on later increments. These facts provide the
independent-block structure used for limiting stopping times.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A walk through time `k` depends only on its first `k` increments. -/
theorem sitePath_eq_of_prefix {d : ℕ} (q : Site d) (ξ η : ℕ → Site d) (k : ℕ)
    (h : ∀ j < k, ξ j = η j) :
    ∀ j ≤ k, LatticeProb.sitePath q ξ j = LatticeProb.sitePath q η j := by
  intro j hj
  simp only [LatticeProb.sitePath]
  congr 1
  exact Finset.sum_congr rfl (fun i hi => h i ((Finset.mem_range.mp hi).trans_le hj))

/-- The displacement between two lattice times depends only on the increments
between them. -/
theorem sitePath_sub_eq_of_tail {d : ℕ} (q : Site d) (ξ η : ℕ → Site d) (k : ℕ)
    (h : ∀ j ≥ k, ξ j = η j) (a b : ℕ) (ha : k ≤ a) (hb : k ≤ b) :
    LatticeProb.sitePath q ξ a - LatticeProb.sitePath q ξ b =
      LatticeProb.sitePath q η a - LatticeProb.sitePath q η b := by
  have hshift : ∀ n, LatticeProb.sitePath q ξ (k + n) - LatticeProb.sitePath q ξ k =
      LatticeProb.sitePath q η (k + n) - LatticeProb.sitePath q η k := by
    intro n
    have hsum : (∑ i ∈ Finset.range n, ξ (k + i)) =
        ∑ i ∈ Finset.range n, η (k + i) :=
      Finset.sum_congr rfl (fun i _ => h (k + i) (Nat.le_add_right k i))
    simp only [LatticeProb.sitePath, Finset.sum_range_add]
    rw [hsum]
    abel
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb
  calc
    _ = (LatticeProb.sitePath q ξ (k + a') - LatticeProb.sitePath q ξ k) -
        (LatticeProb.sitePath q ξ (k + b') - LatticeProb.sitePath q ξ k) := by abel
    _ = (LatticeProb.sitePath q η (k + a') - LatticeProb.sitePath q η k) -
        (LatticeProb.sitePath q η (k + b') - LatticeProb.sitePath q η k) := by
          rw [hshift a', hshift b']
    _ = _ := by abel

/-- Scaling commutes with lattice differences. -/
theorem scaledSite_sub {d : ℕ} (R : ℝ) (x y : Site d) :
    Lclt.scaledSite R (x - y) = Lclt.scaledSite R x - Lclt.scaledSite R y := by
  ext i
  simp only [Lclt.scaledSite, Pi.sub_apply, PiLp.sub_apply, Int.cast_sub]
  ring

/-- After a lattice time, the difference between two interpolations driven by
the same tail increments is constant. -/
theorem linearWalk_sub_eq_of_tail {d : ℕ} (R : ℝ) (q : Site d)
    (ξ η : ℕ → Site d) (k : ℕ) (h : ∀ j ≥ k, ξ j = η j)
    (s : ℝ≥0) (hs : k ≤ ⌊(s : ℝ)⌋₊) :
    linearWalk R s (LatticeProb.sitePath q ξ) -
        linearWalk R s (LatticeProb.sitePath q η) =
      Lclt.scaledSite R (LatticeProb.sitePath q ξ k) -
        Lclt.scaledSite R (LatticeProb.sitePath q η k) := by
  let X := LatticeProb.sitePath q ξ
  let Y := LatticeProb.sitePath q η
  let n := ⌊(s : ℝ)⌋₊
  let a : ℝ := (s : ℝ) - n
  have heq (j : ℕ) (hj : k ≤ j) : Lclt.scaledSite R (X j) - Lclt.scaledSite R (Y j) =
      Lclt.scaledSite R (X k) - Lclt.scaledSite R (Y k) := by
    have hp := sitePath_sub_eq_of_tail q ξ η k h j k hj le_rfl
    have hp' : X j - Y j = X k - Y k := by
      change X j - X k = Y j - Y k at hp
      calc
        X j - Y j = (X j - X k) - (Y j - Y k) + (X k - Y k) := by abel
        _ = X k - Y k := by rw [hp]; abel
    rw [← scaledSite_sub, hp', scaledSite_sub]
  change (1 - a) • Lclt.scaledSite R (X n) + a • Lclt.scaledSite R (X (n + 1)) -
      ((1 - a) • Lclt.scaledSite R (Y n) + a • Lclt.scaledSite R (Y (n + 1))) = _
  calc
    _ = (1 - a) • (Lclt.scaledSite R (X n) - Lclt.scaledSite R (Y n)) +
        a • (Lclt.scaledSite R (X (n + 1)) - Lclt.scaledSite R (Y (n + 1))) := by module
    _ = (1 - a) • (Lclt.scaledSite R (X k) - Lclt.scaledSite R (Y k)) +
        a • (Lclt.scaledSite R (X k) - Lclt.scaledSite R (Y k)) := by
          rw [heq n hs, heq (n + 1) (by omega)]
    _ = _ := by module

/-- Future increments of the diffusive interpolation depend only on increments
at or after the floor of its initial lattice time. -/
theorem futureIncrementPath_walk_eq_of_tail {d : ℕ} (R : ℝ) (q : Site d)
    (ξ η : ℕ → Site d) (k : ℕ) (h : ∀ j ≥ k, ξ j = η j)
    (t : ℝ≥0) (ht : k ≤ ⌊(R ^ 2 * (t : ℝ))⌋₊) :
    futureIncrementPath t (diffusiveWalkPath R (LatticeProb.sitePath q ξ)) =
      futureIncrementPath t (diffusiveWalkPath R (LatticeProb.sitePath q η)) := by
  apply ContinuousMap.ext
  intro s
  simp only [futureIncrementPath_apply]
  change linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * (t + s)) _ -
      linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * t) _ =
    linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * (t + s)) _ -
      linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * t) _
  have hfloor : k ≤ ⌊((⟨R ^ 2, sq_nonneg R⟩ * (t + s) : ℝ≥0) : ℝ)⌋₊ := by
    apply ht.trans
    apply Nat.floor_mono
    change R ^ 2 * (t : ℝ) ≤ R ^ 2 * ((t : ℝ) + (s : ℝ))
    nlinarith [s.property, sq_nonneg R]
  have h₁ := linearWalk_sub_eq_of_tail R q ξ η k h _ hfloor
  have ht' : k ≤ ⌊((⟨R ^ 2, sq_nonneg R⟩ * t : ℝ≥0) : ℝ)⌋₊ := ht
  have h₂ := linearWalk_sub_eq_of_tail R q ξ η k h _ ht'
  have heq : linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * (t + s)) (LatticeProb.sitePath q ξ) -
      linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * (t + s)) (LatticeProb.sitePath q η) =
      linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * t) (LatticeProb.sitePath q ξ) -
      linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * t) (LatticeProb.sitePath q η) := h₁.trans h₂.symm
  calc
    _ = (linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * (t + s)) (LatticeProb.sitePath q ξ) -
          linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * (t + s)) (LatticeProb.sitePath q η)) -
        (linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * t) (LatticeProb.sitePath q ξ) -
          linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * t) (LatticeProb.sitePath q η)) +
        (linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * (t + s)) (LatticeProb.sitePath q η) -
          linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * t) (LatticeProb.sitePath q η)) := by abel
    _ = _ := by rw [heq]; abel

/-- A stopped interpolated path and a truncated stopping rule use only the
increments through the corresponding lattice time. -/
theorem stoppedWalk_clock_eq_of_prefix {d : ℕ} (R : ℝ) (q : Site d)
    (ξ η : ℕ → Site d) (k : ℕ) (h : ∀ j < k, ξ j = η j)
    (τ : (ℕ → Site d) → ℕ) (hτ : IsWalkStopping τ) (t : ℝ≥0)
    (ht : R ^ 2 * (t : ℝ) ≤ k) :
    (LatticeProb.stoppedPath (t : ℝ≥0∞) (diffusiveWalkPath R (LatticeProb.sitePath q ξ)),
      min (τ (LatticeProb.sitePath q ξ)) k) =
    (LatticeProb.stoppedPath (t : ℝ≥0∞) (diffusiveWalkPath R (LatticeProb.sitePath q η)),
      min (τ (LatticeProb.sitePath q η)) k) := by
  have hp := sitePath_eq_of_prefix q ξ η k h
  apply Prod.ext
  · apply ContinuousMap.ext
    intro s
    simp only [LatticeProb.stoppedPath_apply, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
    change linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * min s t) _ =
      linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * min s t) _
    apply linearWalk_grid_causal R k _ _ hp
    change R ^ 2 * (min s t : ℝ≥0) ≤ (k : ℝ)
    have hm : ((min s t : ℝ≥0) : ℝ) ≤ t := by exact_mod_cast min_le_right s t
    nlinarith [sq_nonneg R]
  · exact IsWalkStopping.min_eq_of_history hτ _ _ k hp

/-- The past interpolated walk and truncated stopping clock are independent
of future interpolated increments after a separated lattice time. -/
theorem indepFun_stoppedWalk_clock_future_driver {d : ℕ} [NeZero d]
    (R : ℝ) (q : Site d) (τ : (ℕ → Site d) → ℕ) (hτ : IsWalkStopping τ)
    (t u : ℝ≥0) (k : ℕ) (ht : R ^ 2 * (t : ℝ) ≤ k)
    (hu : k ≤ ⌊R ^ 2 * (u : ℝ)⌋₊) :
    IndepFun
      (fun ξ => (LatticeProb.stoppedPath (t : ℝ≥0∞)
        (diffusiveWalkPath R (LatticeProb.sitePath q ξ)),
        min (τ (LatticeProb.sitePath q ξ)) k))
      (fun ξ => futureIncrementPath u (diffusiveWalkPath R (LatticeProb.sitePath q ξ)))
      (LatticeProb.incPathLaw d) := by
  have hτm : Measurable (fun X => min (τ X) k) :=
    LatticeProb.measurable_of_dependsUpTo (fun X Y hXY =>
      IsWalkStopping.min_eq_of_history hτ X Y k hXY)
  have hp : Measurable (fun X : ℕ → Site d => LatticeProb.stoppedPath (t : ℝ≥0∞)
      (diffusiveWalkPath R X)) :=
    LatticeProb.continuous_stoppedPath.measurable.comp
      (measurable_const.prodMk (measurable_diffusiveWalkPath R))
  have hf : Measurable (fun X : ℕ → Site d => futureIncrementPath u (diffusiveWalkPath R X)) :=
    (continuous_futureIncrementPath u).measurable.comp (measurable_diffusiveWalkPath R)
  change IndepFun _ _ (Measure.infinitePi fun _ : ℕ => LatticeProb.incLaw d)
  apply indepFun_of_depends_on_disjoint_blocks (LatticeProb.incLaw d) (Set.Iio k) (Set.Ici k)
  · apply Set.disjoint_left.2
    intro i hi hj
    change i < k at hi
    change k ≤ i at hj
    omega
  · exact (hp.prodMk hτm).comp (LatticeProb.measurable_sitePath q)
  · exact hf.comp (LatticeProb.measurable_sitePath q)
  · intro ξ η hξη
    exact stoppedWalk_clock_eq_of_prefix R q ξ η k (fun j hj => hξη j hj) τ hτ t ht
  · intro ξ η hξη
    exact futureIncrementPath_walk_eq_of_tail R q ξ η k (fun j hj => hξη j hj) u hu

end Sandpile.External.Stopping
