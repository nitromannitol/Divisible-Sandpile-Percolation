import Sandpile.Support.OriginKilled
import Sandpile.Support.HitProb
import Sandpile.Support.RefinedIncrement
import LatticeProb.Graph.ExitDecomp

/-!
# The origin-killed heat kernel and the influence bound it gives

Reversing the heat kernel killed at the origin identifies its neighbor average
with the first-hitting kernel. The resulting hitting probability is the sharp
coordinate influence bound for the averaged origin-frozen odometer.
-/

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- The heat kernel of simple random walk on the lattice killed at the origin: the `k`-step
transition probability from `x` to `z` for a walk confined to `{x ≠ 0}`. -/
noncomputable abbrev originHeat (k : ℕ) (x z : Site d) : ℝ :=
  LatticeProb.Graph.killedHeat (LatticeProb.lattice d) {x : Site d | x ≠ 0} k x z

/-- The origin-killed heat kernel is symmetric in its two site arguments, from the
reversibility of the killed network `Network.killedHeat_reversible` and the lattice's
constant vertex degree `2d`. -/
theorem originHeat_symm (hd : 1 ≤ d) (k : ℕ) (x z : Site d) :
    originHeat k x z = originHeat k z x := by
  have h := LatticeProb.Network.killedHeat_reversible
    (G := LatticeProb.lattice d) {x : Site d | x ≠ 0} k x z
  simp only [LatticeProb.Graph.Zd.degree_eq] at h
  exact mul_left_cancel₀ (by exact_mod_cast (show 2 * d ≠ 0 by omega)) h

/-- The origin-killed heat kernel vanishes started from the origin, since `0` is not in the
surviving set `{x ≠ 0}`. -/
theorem originHeat_zero_source (k : ℕ) (z : Site d) : originHeat k 0 z = 0 :=
  LatticeProb.Network.killedHeat_of_source_not_mem (by simp) k z

/-- The origin-killed heat kernel vanishes when the target is the origin, since `0` is not in
the surviving set `{x ≠ 0}`. -/
theorem originHeat_zero_target (k : ℕ) (x : Site d) : originHeat k x 0 = 0 :=
  LatticeProb.Network.killedHeat_of_target_not_mem (by simp) k x

/-- The one-step recursion for `originHeat`: it vanishes started from `x = 0`, and otherwise
equals the neighbor average of the previous step's kernel. -/
theorem originHeat_succ (k : ℕ) (x z : Site d) :
    originHeat (k + 1) x z = if x = 0 then 0 else avg (fun y => originHeat k y z) x := by
  rw [originHeat, LatticeProb.Graph.Zd.killedHeat_succ_walkOp]
  simp only [Set.mem_setOf_eq]
  by_cases hx : x = 0 <;> simp [hx, avg]

/-- The two-argument averaging operator `avg` commutes: averaging over the first site then
the second agrees with averaging over the second then the first, by Fubini for the finite
double sum defining `avg`. -/
theorem avg_commute (F : Site d → Site d → ℝ) (x y : Site d) :
    avg (fun v => avg (F v) y) x = avg (fun w => avg (fun v => F v w) x) y := by
  unfold avg LatticeProb.walkOp LatticeProb.nbrSum
  simp only [← add_div, ← Finset.sum_add_distrib, ← Finset.sum_div, div_div]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The average of the killed kernel from the neighbors of the origin is
exactly the next first-hitting probability, by reversal. -/
theorem avg_originHeat_eq_firstHit (hd : 1 ≤ d) : ∀ k : ℕ, ∀ z : Site d,
    avg (fun x => originHeat k x z) 0 = LatticeProb.srwFirstHit d (k + 1) z := by
  classical
  intro k
  induction k with
  | zero =>
    intro z
    by_cases hz : z = 0
    · subst hz
      simp only [originHeat_zero_target, LatticeProb.srwFirstHit_succ_origin]
      simp [avg, LatticeProb.walkOp, LatticeProb.nbrSum]
    · rw [LatticeProb.srwFirstHit_succ_of_ne hz]
      have hzero (x : Site d) : originHeat 0 x z = if x = z then 1 else 0 := by
        rw [originHeat, LatticeProb.Network.killedHeat_zero]
        by_cases hx : x = 0
        · subst hx
          simp [Ne.symm hz]
        · simp [hx]
      simp only [hzero]
      have hr := LatticeProb.Network.heat_reversible (G := LatticeProb.lattice d) 1 0 z
      simp only [LatticeProb.Graph.Zd.degree_eq] at hr
      have he := mul_left_cancel₀ (by exact_mod_cast (show 2 * d ≠ 0 by omega)) hr
      convert he using 1
      · simp only [avg, LatticeProb.Graph.heat, LatticeProb.Graph.Zd.walkOp_eq]
        congr 1
        funext w
        by_cases hw : w = z <;> simp [hw]
      · simp only [LatticeProb.Graph.heat, LatticeProb.Graph.Zd.walkOp_eq, LatticeProb.srwFirstHit]
        congr 1
        funext w
        by_cases hw : w = 0 <;> simp [hw]
  | succ k ih =>
    intro z
    by_cases hz : z = 0
    · subst hz
      simp only [originHeat_zero_target, LatticeProb.srwFirstHit_succ_origin]
      simp [avg, LatticeProb.walkOp, LatticeProb.nbrSum]
    · have he (x : Site d) : originHeat (k + 1) x z = avg (fun y => originHeat k x y) z := by
        rw [originHeat_symm hd, originHeat_succ, if_neg hz]
        congr 1
        funext y
        exact originHeat_symm hd k y x
      simp_rw [he]
      rw [avg_commute, LatticeProb.srwFirstHit_succ_of_ne hz]
      exact congrArg (fun f : Site d → ℝ => avg f z) (funext ih)

/-- The origin-killed Green time `∑_{k<n} originHeat k x z`: the expected number of visits
to `z` by time `n` of the walk from `x` killed at the origin. -/
noncomputable def originGreenTime (n : ℕ) (x z : Site d) : ℝ :=
  ∑ k ∈ Finset.range n, originHeat k x z

/-- `originGreenTime` is nonnegative, as a finite sum of nonnegative killed heat kernel
values. -/
theorem originGreenTime_nonneg (n : ℕ) (x z : Site d) : 0 ≤ originGreenTime n x z :=
  Finset.sum_nonneg fun k _ => LatticeProb.Network.killedHeat_nonneg _ k x z

/-- The one-step recursion for `originGreenTime` from a nonzero site `x`: it adds the
indicator `x = z` to the neighbor average of the previous Green time, mirroring the
recursion `originHeat_succ` of the kernel it sums. -/
theorem originGreenTime_succ (n : ℕ) (x z : Site d) (hx : x ≠ 0) :
    originGreenTime (n + 1) x z =
      (if x = z then 1 else 0) + avg (fun y => originGreenTime n y z) x := by
  classical
  rw [originGreenTime, Finset.sum_range_succ']
  simp only [originHeat_succ, if_neg hx]
  have hzero : originHeat 0 x z = if x = z then 1 else 0 := by
    rw [originHeat, LatticeProb.Network.killedHeat_zero,
      if_pos (show x ∈ {x : Site d | x ≠ 0} from hx)]
    split_ifs <;> rfl
  rw [hzero, add_comm]
  congr 1
  exact (LatticeProb.walkOp_finsetSum (Finset.range n) (fun k y => originHeat k y z) x).symm

/-- The origin-averaged origin-killed Green time up to `n` is bounded by the total hitting
probability `LatticeProb.srwHitProb d z`: by `avg_originHeat_eq_firstHit` it is a partial sum
of the first-hitting-time probabilities `srwFirstHit`, which sum to at most the total hitting
probability. -/
theorem avg_originGreenTime_le_hitProb (hd : 1 ≤ d) (n : ℕ) (z : Site d) :
    avg (fun x => originGreenTime n x z) 0 ≤ LatticeProb.srwHitProb d z := by
  change LatticeProb.walkOp (fun x => ∑ k ∈ Finset.range n, originHeat k x z) 0 ≤ _
  rw [LatticeProb.walkOp_finsetSum]
  simp_rw [show ∀ k : ℕ, LatticeProb.walkOp (fun x => originHeat k x z) 0 =
      LatticeProb.srwFirstHit d (k + 1) z from fun k => avg_originHeat_eq_firstHit hd k z]
  have hsum := (LatticeProb.summable_srwFirstHit (by omega) z).sum_le_tsum
    (Finset.range (n + 1)) (fun k _ => LatticeProb.srwFirstHit_nonneg k z)
  rw [Finset.sum_range_succ'] at hsum
  have hn := LatticeProb.srwFirstHit_nonneg 0 z
  exact (le_add_of_nonneg_right hn).trans hsum

/-- The averaging operator does not increase the absolute difference of two functions:
`|avg f x - avg g x| ≤ avg |f - g| x`, by the triangle inequality applied termwise in the
finite sum defining `avg`. -/
theorem abs_avg_sub_le_avg_abs (f g : Site d → ℝ) (x : Site d) :
    |avg f x - avg g x| ≤ avg (fun y => |f y - g y|) x := by
  change |LatticeProb.walkOp f x - LatticeProb.walkOp g x| ≤ _
  rw [← LatticeProb.walkOp_sub]
  unfold LatticeProb.walkOp LatticeProb.nbrSum avg
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ))]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => abs_add_le _ _)

/-- The killed Green kernel bounds the effect of one changed scenery coordinate. -/
theorem abs_originOdometer_update_le (hd : 1 ≤ d) (ζ : Site d → ℝ) (z : Site d) (v : ℝ) :
    ∀ n : ℕ, ∀ x : Site d,
      |originOdometer ζ n x - originOdometer (Function.update ζ z v) n x| ≤
        originGreenTime n x z * |ζ z - v| := by
  classical
  intro n
  induction n with
  | zero =>
    intro x
    change |localizedOdometer _ _ 0 _ - localizedOdometer _ _ 0 _| ≤ _
    rw [localizedOdometer_zero hd, localizedOdometer_zero hd]
    simp [originGreenTime]
  | succ n ih =>
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [originOdometer_zero, originOdometer_zero, sub_self, abs_zero]
      exact mul_nonneg (originGreenTime_nonneg _ _ _) (abs_nonneg _)
    · have hmax : |originOdometer ζ (n + 1) x - originOdometer (Function.update ζ z v) (n + 1) x| ≤
          |ζ x - Function.update ζ z v x| +
            |avg (originOdometer ζ n) x - avg (originOdometer (Function.update ζ z v) n) x| := by
        change |localizedOdometer _ _ _ _ - localizedOdometer _ _ _ _| ≤ _
        rw [localizedOdometer_succ' hd _ _ n x hx, localizedOdometer_succ' hd _ _ n x hx,
          max_comm 0, max_comm 0]
        refine (abs_max_sub_max_le_abs _ _ _).trans ?_
        convert abs_add_le (ζ x - Function.update ζ z v x)
          (avg (originOdometer ζ n) x - avg (originOdometer (Function.update ζ z v) n) x) using 1
        congr 1
        ring
      have ha := (abs_avg_sub_le_avg_abs (originOdometer ζ n)
        (originOdometer (Function.update ζ z v) n) x).trans (avg_mono_le ih x)
      have hav : avg (fun y => originGreenTime n y z * |ζ z - v|) x =
          avg (fun y => originGreenTime n y z) x * |ζ z - v| :=
        LatticeProb.walkOp_mul_const _ _ _
      rw [hav] at ha
      have hc : |ζ x - Function.update ζ z v x| = (if x = z then 1 else 0) * |ζ z - v| := by
        by_cases he : x = z
        · subst he
          simp
        · simp [he]
      rw [hc] at hmax
      rw [originGreenTime_succ n x z hx, add_mul]
      linarith

/-- The limiting coordinate-influence bound at `z`: `0` at the origin itself, and otherwise
the total hitting probability `LatticeProb.srwHitProb d z`. -/
noncomputable def originInfluence (z : Site d) : ℝ :=
  if z = 0 then 0 else LatticeProb.srwHitProb d z

/-- `originInfluence` is nonnegative, since hitting probabilities are nonnegative. -/
theorem originInfluence_nonneg (z : Site d) : 0 ≤ originInfluence z := by
  unfold originInfluence
  split_ifs
  · exact le_rfl
  · exact LatticeProb.srwHitProb_nonneg z

/-- **The origin-averaged odometer's sensitivity to one scenery coordinate is bounded by
`originInfluence`.** Combines the pointwise sensitivity bound `abs_originOdometer_update_le`
with the averaging bound `abs_avg_sub_le_avg_abs` and the hitting-probability bound
`avg_originGreenTime_le_hitProb`. -/
theorem abs_avg_originOdometer_update_le (hd : 1 ≤ d) (ζ : Site d → ℝ) (z : Site d)
    (v : ℝ) (n : ℕ) :
    |avg (originOdometer ζ n) 0 - avg (originOdometer (Function.update ζ z v) n) 0| ≤
      originInfluence z * |ζ z - v| := by
  by_cases hz : z = 0
  · subst hz
    rw [originOdometer_update hd ζ v n]
    simp [originInfluence]
  · have h := (abs_avg_sub_le_avg_abs (originOdometer ζ n)
        (originOdometer (Function.update ζ z v) n) 0).trans
      (avg_mono_le (abs_originOdometer_update_le hd ζ z v n) 0)
    have hav : avg (fun x => originGreenTime n x z * |ζ z - v|) 0 =
        avg (fun x => originGreenTime n x z) 0 * |ζ z - v| :=
      LatticeProb.walkOp_mul_const _ _ _
    rw [hav] at h
    rw [originInfluence, if_neg hz]
    exact h.trans
      (mul_le_mul_of_nonneg_right (avg_originGreenTime_le_hitProb hd n z) (abs_nonneg _))

end Sandpile
