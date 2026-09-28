import Sandpile.Support.ExitGreen
import Sandpile.Support.OriginConcentration
import Sandpile.External.BallGreenBounds

/-! # Exit-Averaged Payoffs and Green-Time Lipschitz Bounds

Exit averaging spreads the coordinate influence of a localized odometer.
The full finite-time Green kernel bounds resampling, its total mass is the
continuation horizon, and the first-passage identity bounds the largest
averaged coefficient for a cube in dimension four.
-/

open MeasureTheory Filter Topology
open scoped Classical

namespace Sandpile

variable {d : ℕ}

/-- `exitAverage D N f x` is the expectation, under the walk from `x`, of `f` at the site
where the walk first exits `D`, provided that exit happens by time `N`; the contribution is
`0` on the event that the walk has not exited `D` by time `N`. -/
noncomputable def exitAverage (D : Set (Site d)) (N : ℕ) (f : Site d → ℝ) (x : Site d) : ℝ := by
  classical
  exact ∫ X, if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
    else f (X (stopBeforeExit D N (fun _ => N) X)) ∂walkLaw d x

/-- The integrand defining `exitAverage D N f x` is integrable against `walkLaw d x`, being a
stopped value of the payoff `fun _ y => if y ∈ D then 0 else f y` at the bounded stopping time
`stopBeforeExit D N (fun _ => N)`. -/
theorem integrable_exitAverage_payoff (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (f : Site d → ℝ) (x : Site d) :
    Integrable (fun X : ℕ → Site d => if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
      else f (X (stopBeforeExit D N (fun _ => N) X))) (walkLaw d x) := by
  classical
  exact integrable_stopped_value hd x N (fun _ y => if y ∈ D then 0 else f y)
    (isWalkStopping_stopBeforeExit (D := D) (isWalkStopping_const N) (fun _ => le_rfl))
    (stopBeforeExit_le (fun _ : ℕ → Site d => le_refl N))

/-- `exitAverage` is nonnegative when `f` is nonnegative pointwise: each term is either `0` or
a value of `f`. -/
theorem exitAverage_nonneg (D : Set (Site d)) (N : ℕ) (f : Site d → ℝ) (x : Site d)
    (hf : ∀ y, 0 ≤ f y) : 0 ≤ exitAverage D N f x := by
  classical
  apply integral_nonneg
  intro X
  dsimp only
  split_ifs
  · exact le_rfl
  · exact hf _

/-- `exitAverage` is monotone in the payoff `f`. -/
theorem exitAverage_mono (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ) (f g : Site d → ℝ)
    (x : Site d) (hfg : ∀ y, f y ≤ g y) : exitAverage D N f x ≤ exitAverage D N g x := by
  classical
  apply integral_mono (integrable_exitAverage_payoff hd D N f x)
    (integrable_exitAverage_payoff hd D N g x)
  intro X
  dsimp only
  split_ifs
  · exact le_rfl
  · exact hfg _

/-- `exitAverage` of a nonnegative constant payoff `c` is bounded above by `c`, since every
term is either `0` or `c`. -/
theorem exitAverage_const_le (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ) (x : Site d)
    (c : ℝ) (hc : 0 ≤ c) : exitAverage D N (fun _ => c) x ≤ c := by
  haveI : NeZero d := ⟨by omega⟩
  classical
  have h := integral_mono (integrable_exitAverage_payoff hd D N (fun _ => c) x)
    (integrable_const c) (fun X => by dsimp only; split_ifs <;> simp_all)
  simpa [exitAverage] using h

/-- `exitAverage` commutes with multiplying the payoff by a constant on the right. -/
theorem exitAverage_mul_const (D : Set (Site d)) (N : ℕ) (f : Site d → ℝ) (x : Site d)
    (c : ℝ) : exitAverage D N (fun y => f y * c) x = exitAverage D N f x * c := by
  classical
  unfold exitAverage
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact Eventually.of_forall fun X => by dsimp only; split_ifs <;> simp

/-- `exitAverage` satisfies the pointwise-in-average triangle inequality: the `exitAverage` of
a difference is bounded by the `exitAverage` of the absolute difference. -/
theorem abs_exitAverage_sub_le (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (f g : Site d → ℝ) (x : Site d) :
    |exitAverage D N f x - exitAverage D N g x| ≤ exitAverage D N (fun y => |f y - g y|) x := by
  classical
  unfold exitAverage
  rw [← integral_sub (integrable_exitAverage_payoff hd D N f x)
    (integrable_exitAverage_payoff hd D N g x)]
  have h := abs_integral_le_integral_abs (f := fun X : ℕ → Site d =>
    (if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
      else f (X (stopBeforeExit D N (fun _ => N) X))) -
    (if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
      else g (X (stopBeforeExit D N (fun _ => N) X))))
    (μ := walkLaw d x)
  refine h.trans_eq ?_
  apply integral_congr_ae
  exact Eventually.of_forall fun X => by dsimp only; split_ifs <;> simp

/-- `exitAverage` commutes with a finite sum over an index type: summing `exitAverage D N (f i) x`
over `i ∈ s` equals `exitAverage D N (fun y => ∑ i ∈ s, f i y) x`. -/
theorem exitAverage_finset_sum (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ) (x : Site d)
    {ι : Type*} (s : Finset ι) (f : ι → Site d → ℝ) :
    (∑ i ∈ s, exitAverage D N (f i) x) = exitAverage D N (fun y => ∑ i ∈ s, f i y) x := by
  classical
  unfold exitAverage
  rw [← integral_finsetSum s (fun i _ => integrable_exitAverage_payoff hd D N (f i) x)]
  apply integral_congr_ae
  exact Eventually.of_forall fun X => by dsimp only; split_ifs <;> simp

/-- When the payoff `f` is bounded above by the Green function to `y`, `exitAverage D N f x` is
bounded by the expected Green function value at the walk's actual exit time from `D`, not
capped at the horizon `N`. -/
theorem exitAverage_le_green_exit (hd : 3 ≤ d) (D : Set (Site d)) (N : ℕ) (x y : Site d)
    (f : Site d → ℝ) (hf : ∀ w, f w ≤ green d w y) :
    exitAverage D N f x ≤ ∫ X, green d (X (exitTime D X).toNat) y ∂walkLaw d x := by
  classical
  apply integral_mono (integrable_exitAverage_payoff (by omega) D N f x)
    (integrable_green_at_exit hd D x y)
  intro X
  dsimp only
  split_ifs with hx
  · exact green_nonneg _ _
  · have hle : exitTime D X ≤ (N : ℕ∞) := by
      apply exitTime_le_iff.mpr
      by_contra hn
      have ht : stopBeforeExit D N (fun _ => N) X = N := min_eq_left (le_of_not_ge hn)
      rw [ht] at hx
      exact hx (mem_of_lt_exitNat (lt_of_not_ge hn) (le_refl N))
    rw [stoppedExit_eq_toNat hle]
    exact hf _

/-- Each coordinate of a site of `Site 4` is bounded in absolute value by the Euclidean
lattice norm `External.BallGreen.latticeNorm`. -/
theorem ballNorm_coord (u : Site 4) (i : Fin 4) :
    |(u i : ℝ)| ≤ External.BallGreen.latticeNorm u := by
  unfold External.BallGreen.latticeNorm
  have hs : (u i : ℝ) ^ 2 ≤ ∑ j : Fin 4, (u j : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j => (u j : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  apply (Real.le_sqrt (abs_nonneg (u i : ℝ))
    (Finset.sum_nonneg (fun j _ => sq_nonneg (u j : ℝ)))).mpr
  simpa only [sq_abs] using hs

/-- **Cube exit Green bound in dimension four.**  Under `External.BallGreenBounds` there is a
constant `B` such that the expected Green function value at the exit of the cube of side `r`
around `x` is at most `B / r ^ 2`, uniformly in `x`, `y` and every `r ≥ 2`. -/
theorem exists_cube_exit_green_bound (hBallGreen : External.BallGreenBounds) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℕ, 2 ≤ r → ∀ x y : Site 4,
      (∫ X, green 4 (X (exitTime {w : Site 4 | ∀ i, |(w i : ℝ) - (x i : ℝ)| ≤ r} X).toNat) y
        ∂walkLaw 4 x) ≤ B / (r : ℝ) ^ 2 := by
  obtain ⟨B, _, hB, _, hbound⟩ := hBallGreen
  refine ⟨B, hB, ?_⟩
  intro r hr x y
  apply integral_green_at_exit_le_of_outside (by norm_num) _ (finite_real_cube x r) x y
  intro w hw
  have htr : green 4 w x = green 4 0 (x - w) := by
    rw [External.Sec16.green_eq, External.Sec16.green_eq]
    congr 1
    abel
  rw [htr]
  refine ((hbound r hr).1 (x - w)).2.2.trans ?_
  have hnot : ¬ ∀ i, |(w i : ℝ) - (x i : ℝ)| ≤ r := hw
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  have hn := ballNorm_coord (x - w) i
  simp only [Pi.sub_apply, Int.cast_sub] at hn
  rw [abs_sub_comm (x i : ℝ) (w i : ℝ)] at hn
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hs : (r : ℝ) ^ 2 ≤ (1 + External.BallGreen.latticeNorm (x - w)) ^ 2 := by
    have hnorm : 0 ≤ External.BallGreen.latticeNorm (x - w) := Real.sqrt_nonneg _
    nlinarith
  exact div_le_div_of_nonneg_left hB.le (by positivity) hs

/-- The `n`-step Green time `greenTime d n x y` is bounded by the full transient Green
function `green d x y`, being a partial sum of the summable heat kernel. -/
theorem greenTime_le_green_transient (hd : 3 ≤ d) (n : ℕ) (x y : Site d) :
    greenTime d n x y ≤ green d x y :=
  (summable_heatKernel_transient hd x y).sum_le_tsum _ (fun k _ => heatKernel_nonneg k x y)

/-- `exitInfluence D N m x y` is the `exitAverage` of the `m`-step Green time to `y`: how much
the exit-averaged walk from `x` contributes to the Green time at `y` through the site where it
exits `D`. -/
noncomputable def exitInfluence (D : Set (Site d)) (N m : ℕ) (x y : Site d) : ℝ :=
  exitAverage D N (fun w => greenTime d m w y) x

/-- `exitInfluence` is nonnegative, from the nonnegativity of `greenTime` and
`exitAverage_nonneg`. -/
theorem exitInfluence_nonneg (D : Set (Site d)) (N m : ℕ) (x y : Site d) :
    0 ≤ exitInfluence D N m x y :=
  exitAverage_nonneg D N _ x (fun w => greenTime_nonneg m w y)

/-- `exitInfluence` is bounded by the expected Green function value at the walk's actual exit
time from `D`, combining `exitAverage_le_green_exit` with `greenTime_le_green_transient`. -/
theorem exitInfluence_le_green_exit (hd : 3 ≤ d) (D : Set (Site d)) (N m : ℕ) (x y : Site d) :
    exitInfluence D N m x y ≤ ∫ X, green d (X (exitTime D X).toNat) y ∂walkLaw d x :=
  exitAverage_le_green_exit hd D N x y _ (fun w => greenTime_le_green_transient hd m w y)

/-- The sum over any finset `s` of `m`-step Green times from `x` is at most `m`, since the
Green times of the killed walk on `Set.univ` sum to the horizon length. -/
theorem finset_sum_greenTime_le (hd : 1 ≤ d) (s : Finset (Site d)) (m : ℕ) (x : Site d) :
    ∑ y ∈ s, greenTime d m x y ≤ m := by
  have hg : (fun y : Site d => killedGreenTime Set.univ m x y) = fun y => greenTime d m x y := by
    funext y
    simp only [killedGreenTime, greenTime, LatticeProb.greenTime, killedKernel_univ]
  have hs := summable_killedGreenTime_mul Set.univ m x (fun _ => (1 : ℝ))
  simp only [mul_one, hg] at hs
  exact (hs.sum_le_tsum s (fun y _ => greenTime_nonneg m x y)).trans
    (by simpa only [hg] using tsum_killedGreenTime_le hd Set.univ m x)

/-- The sum over any finset `s` of `exitInfluence D N m x y` is at most `m`, by combining
`finset_sum_greenTime_le` with `exitAverage_mono` and `exitAverage_const_le`. -/
theorem finset_sum_exitInfluence_le (hd : 1 ≤ d) (D : Set (Site d)) (N m : ℕ)
    (x : Site d) (s : Finset (Site d)) : ∑ y ∈ s, exitInfluence D N m x y ≤ m := by
  unfold exitInfluence
  rw [exitAverage_finset_sum hd]
  exact (exitAverage_mono hd D N _ (fun _ => (m : ℝ)) x
    (fun w => finset_sum_greenTime_le hd s m w)).trans
    (exitAverage_const_le hd D N x m (Nat.cast_nonneg _))

/-- The `n`-step transient Green time `greenTime d n x z` bounds the effect on
`localizedOdometer D ζ n x` of changing the scenery value at `z`: a coordinate Lipschitz bound
for the localized odometer that does not use the killing set `D` in its constant, only in the
odometer itself. -/
theorem abs_localizedOdometer_update_greenTime_le (hd : 1 ≤ d) (D : Set (Site d))
    (ζ : Site d → ℝ) (z : Site d) (v : ℝ) : ∀ n : ℕ, ∀ x : Site d,
    |localizedOdometer D ζ n x - localizedOdometer D (Function.update ζ z v) n x| ≤
      greenTime d n x z * |ζ z - v| := by
  classical
  intro n
  induction n with
  | zero =>
    intro x
    rw [localizedOdometer_zero hd, localizedOdometer_zero hd]
    simp [greenTime, LatticeProb.greenTime]
  | succ n ih =>
    intro x
    by_cases hx : x ∈ D
    · have hmax : |localizedOdometer D ζ (n + 1) x -
          localizedOdometer D (Function.update ζ z v) (n + 1) x| ≤
          |ζ x - Function.update ζ z v x| +
            |avg (localizedOdometer D ζ n) x -
              avg (localizedOdometer D (Function.update ζ z v) n) x| := by
        rw [localizedOdometer_succ' hd D _ n x hx, localizedOdometer_succ' hd D _ n x hx,
          max_comm 0, max_comm 0]
        refine (abs_max_sub_max_le_abs _ _ _).trans ?_
        convert abs_add_le (ζ x - Function.update ζ z v x)
          (avg (localizedOdometer D ζ n) x -
            avg (localizedOdometer D (Function.update ζ z v) n) x) using 1
        congr 1
        ring
      have ha := (abs_avg_sub_le_avg_abs (localizedOdometer D ζ n)
        (localizedOdometer D (Function.update ζ z v) n) x).trans (avg_mono_le ih x)
      have hav : avg (fun y => greenTime d n y z * |ζ z - v|) x =
          avg (fun y => greenTime d n y z) x * |ζ z - v| := LatticeProb.walkOp_mul_const _ _ _
      rw [hav] at ha
      have hc : |ζ x - Function.update ζ z v x| = (if x = z then 1 else 0) * |ζ z - v| := by
        by_cases he : x = z
        · subst he; simp
        · simp [he]
      rw [hc] at hmax
      rw [greenTime_succ_avg, add_mul]
      change _ ≤ (if x = z then 1 else 0) * |ζ z - v| +
        avg (fun y => greenTime d n y z) x * |ζ z - v|
      linarith
    · rw [localizedOdometer_of_notMem D _ _ hx, localizedOdometer_of_notMem D _ _ hx,
        sub_self, abs_zero]
      exact mul_nonneg (greenTime_nonneg _ _ _) (abs_nonneg _)

/-- `localizedExitAverage D N E m ζ x` composes exit averaging over `D` with the localized
odometer: at the site `w` where the walk from `x` exits `D` (or `0` if it has not exited by
time `N`), it reads `localizedOdometer (E w) ζ m w`, the odometer killed on `E w` run for `m`
steps from `w`. -/
noncomputable def localizedExitAverage (D : Set (Site d)) (N : ℕ) (E : Site d → Set (Site d))
    (m : ℕ) (ζ : Site d → ℝ) (x : Site d) : ℝ :=
  exitAverage D N (fun w => localizedOdometer (E w) ζ m w) x

/-- `localizedExitAverage D N E m · x` is measurable in the scenery `ζ`. -/
theorem measurable_localizedExitAverage (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) (x : Site d) :
    Measurable (fun ζ : Site d → ℝ => localizedExitAverage D N E m ζ x) :=
  measurable_integral_localizedExitPayoff hd x D N E m

/-- `localizedExitAverage`'s coordinate Lipschitz bound: `exitInfluence D N m x z` bounds the
effect on it of changing the scenery `ζ` at `z`, obtained by feeding
`abs_localizedOdometer_update_greenTime_le` through `abs_exitAverage_sub_le`. -/
theorem abs_localizedExitAverage_update_le (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) (ζ : Site d → ℝ) (x z : Site d) (v : ℝ) :
    |localizedExitAverage D N E m ζ x - localizedExitAverage D N E m (Function.update ζ z v) x| ≤
      exitInfluence D N m x z * |ζ z - v| := by
  apply (abs_exitAverage_sub_le hd D N _ _ x).trans
  have h := exitAverage_mono hd D N _ (fun w => greenTime d m w z * |ζ z - v|) x
    (fun w => abs_localizedOdometer_update_greenTime_le hd (E w) ζ z v m w)
  simpa only [exitInfluence, exitAverage_mul_const] using h

/-- `localizedExitAverage D N E m ζ x` depends on `ζ` only through its values on the box of
radius `N + m` around `x`: the exit time from `D` is at most `N`, and from there the localized
odometer run for `m` steps only reads the box of radius `m` around the exit point. -/
theorem localizedExitAverage_congr_box (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) (x : Site d) (ζ η : Site d → ℝ)
    (he : ∀ z ∈ boxFinset x (N + m), ζ z = η z) :
    localizedExitAverage D N E m ζ x = localizedExitAverage D N E m η x := by
  classical
  apply integral_congr_ae
  filter_upwards [ae_boxDist_walk hd x] with X hX
  change (if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0 else _) =
    (if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0 else _)
  split_ifs
  · rfl
  · apply localizedOdometer_congr_box hd
    intro z hz
    apply he z
    have hstop := stopBeforeExit_le (D := D) (fun _ : ℕ → Site d => le_refl N) X
    have hdist := hX (stopBeforeExit D N (fun _ => N) X)
    have hz' := mem_boxFinset_iff.mp hz
    exact mem_boxFinset
      ((boxDist_trans x (X (stopBeforeExit D N (fun _ => N) X)) z).trans (by omega))

end Sandpile
