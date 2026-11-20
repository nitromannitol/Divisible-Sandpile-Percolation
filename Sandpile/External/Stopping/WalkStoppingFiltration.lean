import Sandpile.External.Stopping.ScaledSiteDecode
import LatticeProb.Graph.WalkAverage

/-!
# Discrete stopping events in the step-walk filtration

At positive scale, a step walk reveals its past lattice observations. Every
discrete stopping event is consequently measurable in the step-walk filtration
at the corresponding time.
-/

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A discrete stopping rule has the same value on paths with the same history
through a time at which it has already stopped. -/
theorem IsWalkStopping.eq_of_history_le {d : ℕ} {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) (X Y : ℕ → Site d) (k : ℕ)
    (hXY : ∀ j ≤ k, X j = Y j) (hX : τ X ≤ k) : τ Y = τ X :=
  hτ (τ X) X Y (fun j hj => hXY j (hj.trans hX)) rfl

/-- The event that a discrete stopping rule has stopped by `k` is measurable
in the step-walk filtration at any time at least `k`. -/
theorem measurableSet_walkStopping_le_stepFiltration {d : ℕ} {R : ℝ} (hR : 0 < R)
    (τ : (ℕ → Site d) → ℕ) (hτ : IsWalkStopping τ) (k : ℕ) (t : ℝ≥0)
    (hkt : (k : ℝ≥0) ≤ t) :
    MeasurableSet[Continuum.brownianFiltration (stepWalk R) t] {X | τ X ≤ k} := by
  classical
  let C : (Fin (k + 1) → Site d) → Set (ℕ → Site d) := fun a =>
    {X | ∀ j, ∀ hj : j ≤ k, X j = a ⟨j, by omega⟩}
  let D : (Fin (k + 1) → Site d) → Set (ℕ → Site d) := fun a =>
    if τ (LatticeProb.prefixExt k a) ≤ k then C a else ∅
  have hC (a : Fin (k + 1) → Site d) :
      MeasurableSet[Continuum.brownianFiltration (stepWalk R) t] (C a) := by
    have heq : C a = ⋂ j : ℕ, ⋂ hj : j ≤ k, {X | X j = a ⟨j, by omega⟩} := by
      ext X
      simp only [C, mem_ofPred_eq, mem_iInter]
    rw [heq]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro hj
    have hjt : (j : ℝ≥0) ≤ t := (by exact_mod_cast hj : (j : ℝ≥0) ≤ k).trans hkt
    exact (measurable_walk_coordinate_step_filtration hR j t hjt) (measurableSet_singleton _)
  have heq : {X | τ X ≤ k} = ⋃ a, D a := by
    ext X
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hX
      let a : Fin (k + 1) → Site d := fun j => X j
      have hXY : ∀ j ≤ k, X j = LatticeProb.prefixExt k a j := by
        intro j hj
        rw [LatticeProb.prefixExt_apply a hj]
      have hv : τ (LatticeProb.prefixExt k a) = τ X := IsWalkStopping.eq_of_history_le hτ X _ k hXY hX
      have ha : τ (LatticeProb.prefixExt k a) ≤ k := hv ▸ hX
      refine ⟨a, ?_⟩
      simp only [D, ite_eq_left ha, C, mem_ofPred_eq]
      intro j hj
      rfl
    · rintro ⟨a, ha⟩
      by_cases hstop : τ (LatticeProb.prefixExt k a) ≤ k
      · simp only [D, ite_eq_left hstop, C, mem_ofPred_eq] at ha
        have hXY : ∀ j ≤ k, LatticeProb.prefixExt k a j = X j := by
          intro j hj
          rw [LatticeProb.prefixExt_apply a hj]
          exact (ha j hj).symm
        have hv := IsWalkStopping.eq_of_history_le hτ _ X k hXY hstop
        rw [hv]
        exact hstop
      · simp only [D, ite_eq_right hstop, mem_empty_iff_false] at ha
  rw [heq]
  apply MeasurableSet.iUnion
  intro a
  by_cases ha : τ (LatticeProb.prefixExt k a) ≤ k
  · simpa only [D, ite_eq_left ha] using hC a
  · have hD : D a = ∅ := ite_eq_right ha
    rw [hD]
    exact @MeasurableSet.empty (ℕ → Site d) (Continuum.brownianFiltration (stepWalk R) t)

/-- Every discrete walk stopping time is a stopping time for the step-walk
natural filtration, when lattice indices are viewed as times. -/
theorem isBrownianStopping_stepWalk_of_walkStopping {d : ℕ} {R : ℝ} (hR : 0 < R)
    (τ : (ℕ → Site d) → ℕ) (hτ : IsWalkStopping τ) :
    Continuum.IsBrownianStopping (stepWalk R) (fun X => (τ X : ℝ≥0)) := by
  intro t
  have hfloor : (⌊(t : ℝ)⌋₊ : ℝ≥0) ≤ t := by
    exact_mod_cast Nat.floor_le t.property
  have hm := measurableSet_walkStopping_le_stepFiltration hR τ hτ ⌊(t : ℝ)⌋₊ t hfloor
  have heq : {X : ℕ → Site d | (((τ X : ℝ≥0) : ℝ≥0∞)) ≤ (t : ℝ≥0∞)} =
      {X | τ X ≤ ⌊(t : ℝ)⌋₊} := by
    ext X
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe]
    have h : ((τ X : ℝ≥0) ≤ t) ↔ ((τ X : ℝ) ≤ (t : ℝ)) := by exact_mod_cast Iff.rfl
    exact h.trans (Nat.le_floor_iff t.property).symm
  change MeasurableSet[Continuum.brownianFiltration (stepWalk R) t]
    {X : ℕ → Site d | (((τ X : ℝ≥0) : ℝ≥0∞)) ≤ (t : ℝ≥0∞)}
  rw [heq]
  exact hm

end Sandpile.External.Stopping
