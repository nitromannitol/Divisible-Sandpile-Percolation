/-
The coordinate derivative as a bounded path expectation. Expanding the path
recursion gives the active-site product, which equals survival until optimal stopping.
-/
import Sandpile.Support.OdometerJacobian
import Sandpile.Support.KilledWalk

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

noncomputable def pathOdometerDerivative {d : ℕ} (ζ : Site d → ℝ) :
    ℕ → Site d → (ℕ → Site d) → ℝ
  | 0, _, _ => 0
  | n + 1, z, X => if 0 < odometerOf ζ (n + 1) (X 0) then
      (if X 0 = z then 1 else 0) + pathOdometerDerivative ζ n z (fun j => X (j + 1)) else 0

theorem pathOdometerDerivative_bounds {d : ℕ} (ζ : Site d → ℝ) :
    ∀ n : ℕ, ∀ z : Site d, ∀ X : ℕ → Site d,
      0 ≤ pathOdometerDerivative ζ n z X ∧ pathOdometerDerivative ζ n z X ≤ n := by
  intro n
  induction n with
  | zero => intro z X; simp [pathOdometerDerivative]
  | succ n ih =>
    intro z X
    have h := ih z (fun j => X (j + 1))
    simp only [pathOdometerDerivative]
    split
    · split <;> constructor <;> push_cast <;> linarith
    · exact ⟨le_rfl, Nat.cast_nonneg _⟩

theorem pathOdometerDerivative_congr {d : ℕ} (ζ : Site d → ℝ) :
    ∀ n : ℕ, ∀ z : Site d, ∀ X Y : ℕ → Site d,
      (∀ j ≤ n, X j = Y j) → pathOdometerDerivative ζ n z X = pathOdometerDerivative ζ n z Y := by
  intro n
  induction n with
  | zero => intro z X Y _; rfl
  | succ n ih =>
    intro z X Y h
    have hshift : pathOdometerDerivative ζ n z (fun j => X (j + 1)) =
        pathOdometerDerivative ζ n z (fun j => Y (j + 1)) :=
      ih z _ _ fun j hj => h (j + 1) (by omega)
    simp only [pathOdometerDerivative, h 0 (by omega), hshift]

theorem measurable_pathOdometerDerivative {d : ℕ} (ζ : Site d → ℝ) (n : ℕ) (z : Site d) :
    Measurable (pathOdometerDerivative ζ n z) :=
  measurable_of_dependsOn n _ (pathOdometerDerivative_congr ζ n z)

theorem ae_walkLaw_zero {d : ℕ} (x : Site d) :
    ∀ᵐ X ∂walkLaw d x, X 0 = x := by
  rw [walkLaw, ae_map_iff (measurable_walkPath x).aemeasurable
    (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)]
  exact Eventually.of_forall fun ξ => walkPath_zero x ξ

theorem integral_pathOdometerDerivative {d : ℕ} (hd : 1 ≤ d) (ζ : Site d → ℝ) :
    ∀ n : ℕ, ∀ x z : Site d,
      (∫ X, pathOdometerDerivative ζ n z X ∂walkLaw d x) = odometerJacobian ζ n x z := by
  haveI : NeZero d := ⟨by omega⟩
  intro n
  induction n with
  | zero => intro x z; simp [pathOdometerDerivative, odometerJacobian]
  | succ n ih =>
    intro x z
    have hbound (X : ℕ → Site d) : ‖pathOdometerDerivative ζ n z X‖ ≤ n := by
      rw [Real.norm_eq_abs, abs_of_nonneg (pathOdometerDerivative_bounds ζ n z X).1]
      exact (pathOdometerDerivative_bounds ζ n z X).2
    have hshift : (∫ X, pathOdometerDerivative ζ n z (fun j => X (j + 1)) ∂walkLaw d x) =
        avg (fun y => odometerJacobian ζ n y z) x := by
      have h := LatticeProb.integral_comp_shiftPath d 1 x (pathOdometerDerivative ζ n z)
        (measurable_pathOdometerDerivative ζ n z) hbound
      change (∫ X, pathOdometerDerivative ζ n z (fun j => X (1 + j)) ∂walkLaw d x) =
        avg (fun y => ∫ X, pathOdometerDerivative ζ n z X ∂walkLaw d y) x at h
      simpa only [Nat.add_comm 1, ih] using h
    have hint : Integrable (fun X : ℕ → Site d =>
        pathOdometerDerivative ζ n z (fun j => X (j + 1))) (walkLaw d x) := by
      apply Integrable.of_bound
        ((measurable_pathOdometerDerivative ζ n z).comp
          (measurable_pi_lambda _ fun j => measurable_pi_apply (j + 1))).aestronglyMeasurable (n : ℝ)
      exact Eventually.of_forall fun X => hbound _
    rw [integral_congr_ae (show (fun X => pathOdometerDerivative ζ (n + 1) z X) =ᵐ[walkLaw d x]
        (fun X => if 0 < odometerOf ζ (n + 1) x then (if x = z then 1 else 0) +
          pathOdometerDerivative ζ n z (fun j => X (j + 1)) else 0) from by
      filter_upwards [ae_walkLaw_zero x] with X hX
      simp only [pathOdometerDerivative, hX])]
    by_cases ha : 0 < odometerOf ζ (n + 1) x
    · simp only [if_pos ha, odometerJacobian]
      rw [integral_add (integrable_const _) hint, integral_const, hshift]
      simp
    · simp only [if_neg ha, integral_zero, odometerJacobian]

theorem pathOdometerDerivative_eq_sum {d : ℕ} (ζ : Site d → ℝ) :
    ∀ n : ℕ, ∀ z : Site d, ∀ X : ℕ → Site d,
      pathOdometerDerivative ζ n z X = ∑ j ∈ Finset.range n,
        (if X j = z then (1 : ℝ) else 0) *
          ∏ i ∈ Finset.range (j + 1), (if 0 < odometerOf ζ (n - i) (X i) then 1 else 0) := by
  classical
  intro n
  induction n with
  | zero => intro z X; simp [pathOdometerDerivative]
  | succ n ih =>
    intro z X
    have hstep (j : ℕ) : (if X (j + 1) = z then (1 : ℝ) else 0) *
        (∏ i ∈ Finset.range (j + 1 + 1),
          if 0 < odometerOf ζ (n + 1 - i) (X i) then 1 else 0) =
        (if 0 < odometerOf ζ (n + 1) (X 0) then
          (if X (j + 1) = z then (1 : ℝ) else 0) *
            ∏ i ∈ Finset.range (j + 1),
              (if 0 < odometerOf ζ (n - i) (X (i + 1)) then 1 else 0) else 0) := by
      rw [Finset.prod_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      by_cases ha : 0 < odometerOf ζ (n + 1) (X 0) <;> simp only [ha, if_true, if_false,
        mul_one, mul_zero]
    rw [Finset.sum_range_succ']
    simp only [hstep]
    by_cases ha : 0 < odometerOf ζ (n + 1) (X 0)
    · simp [ha, pathOdometerDerivative, ih, add_comm]
    · simp [ha, pathOdometerDerivative]

theorem lt_optimalStop_iff_active {d : ℕ} (hOS : External.OptimalStopping) (hd : 1 ≤ d)
    (ζ : Site d → ℝ) (n j : ℕ) (hj : j ≤ n) (X : ℕ → Site d) :
    j < optimalStop ζ n X ↔ ∀ i ≤ j, 0 < odometerOf ζ (n - i) (X i) := by
  let S : Set ℕ := {k | k ≤ n ∧ stoppingValue ζ (n - k) (X k) = 0}
  have hS : S.Nonempty := by
    refine ⟨n, le_rfl, ?_⟩
    rw [Nat.sub_self, ← (hOS d hd ζ 0 (X n)).1]
    rfl
  change j < sInf S ↔ _
  constructor
  · intro h i hi
    have hnonneg := odometerOf_nonneg ζ (n - i) (X i)
    by_contra hn
    have hz : odometerOf ζ (n - i) (X i) = 0 := le_antisymm (le_of_not_gt hn) hnonneg
    have hmem : i ∈ S := ⟨hi.trans hj, by rw [← (hOS d hd ζ (n - i) (X i)).1, hz]⟩
    have hle := Nat.sInf_le hmem
    omega
  · intro h
    by_contra hn
    have hmem := Nat.sInf_mem hS
    have hzero : odometerOf ζ (n - sInf S) (X (sInf S)) = 0 := by
      rw [(hOS d hd ζ (n - sInf S) (X (sInf S))).1]
      exact hmem.2
    have hpos := h (sInf S) (by omega)
    rw [hzero] at hpos
    exact lt_irrefl _ hpos

theorem active_product_eq_optimalStop_indicator {d : ℕ} (hOS : External.OptimalStopping)
    (hd : 1 ≤ d) (ζ : Site d → ℝ) (n j : ℕ) (hj : j ≤ n) (X : ℕ → Site d) :
    (∏ i ∈ Finset.range (j + 1),
      (if 0 < odometerOf ζ (n - i) (X i) then (1 : ℝ) else 0)) =
      if j < optimalStop ζ n X then 1 else 0 := by
  classical
  rw [Finset.prod_boole]
  simp only [Finset.mem_range, Nat.lt_succ_iff]
  simp only [← lt_optimalStop_iff_active hOS hd ζ n j hj X]

end Sandpile
