/-
The coordinate Lipschitz bound for the odometer killed on an arbitrary set, at the sharp
constant of the odometer killed at the origin alone.

`Sandpile.abs_avg_originOdometer_update_le` bounds the change of `Pw_n(0)` per unit change of
the scenery at `z` by the hitting probability `G(0,z)/G(0,0)`, through the Green kernel of the
walk killed at the origin.  The same induction runs with the walk killed on any set, and the
killed heat kernel is monotone in the set it is killed outside of, so killing more only lowers
the constant.  This is what `sandpile.tex:5366-5368` needs for the odometer killed at the
origin and at one further site: the paper's `(G(x,0)+G(x,z))/(G(0,0)+G(0,z))` is a sharper
constant than `G(0,z)/G(0,0)`, and the argument uses only the square summability, which the
larger constant already has.
-/
import Sandpile.Support.Dgt4Truncation

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The killed heat kernel is monotone in the set the walk is killed outside of. -/
theorem killedHeat_mono {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {C C' : Set V} (h : C ⊆ C') :
    ∀ (k : ℕ) (x y : V),
      LatticeProb.Graph.killedHeat G C k x y ≤ LatticeProb.Graph.killedHeat G C' k x y := by
  classical
  intro k
  induction k with
  | zero =>
      intro x y
      rw [LatticeProb.Network.killedHeat_zero, LatticeProb.Network.killedHeat_zero]
      by_cases hx : x ∈ C
      · rw [if_pos hx, if_pos (h hx)]
      · rw [if_neg hx]
        split_ifs <;> norm_num
  | succ k ih =>
      intro x y
      rw [LatticeProb.Network.killedHeat_succ, LatticeProb.Network.killedHeat_succ]
      by_cases hx : x ∈ C
      · rw [if_pos hx, if_pos (h hx)]
        exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun z _ => ih z y)
          (Nat.cast_nonneg _)
      · rw [if_neg hx]
        split_ifs with hx'
        · exact div_nonneg
            (Finset.sum_nonneg fun z _ => LatticeProb.Network.killedHeat_nonneg _ k z y)
            (Nat.cast_nonneg _)
        · exact le_refl 0

/-- The Green kernel of the walk killed outside `D`, run for `n` steps. -/
noncomputable def localGreenTime (D : Set (Site d)) (n : ℕ) (x z : Site d) : ℝ :=
  ∑ k ∈ Finset.range n, LatticeProb.Graph.killedHeat (LatticeProb.lattice d) D k x z

theorem localGreenTime_nonneg (D : Set (Site d)) (n : ℕ) (x z : Site d) :
    0 ≤ localGreenTime D n x z :=
  Finset.sum_nonneg fun k _ => LatticeProb.Network.killedHeat_nonneg _ k x z

theorem localGreenTime_of_notMem {D : Set (Site d)} {x : Site d} (hx : x ∉ D) (n : ℕ)
    (z : Site d) : localGreenTime D n x z = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  exact LatticeProb.Network.killedHeat_of_source_not_mem hx k z

theorem localGreenTime_succ (D : Set (Site d)) (n : ℕ) (x z : Site d) (hx : x ∈ D) :
    localGreenTime D (n + 1) x z
      = (if x = z then 1 else 0) + avg (fun y => localGreenTime D n y z) x := by
  classical
  rw [localGreenTime, Finset.sum_range_succ']
  simp only [LatticeProb.Graph.Zd.killedHeat_succ_walkOp, if_pos hx]
  have hzero : LatticeProb.Graph.killedHeat (LatticeProb.lattice d) D 0 x z
      = if x = z then 1 else 0 := by
    rw [LatticeProb.Network.killedHeat_zero, if_pos hx]
    split_ifs <;> rfl
  rw [hzero, add_comm]
  congr 1
  exact (LatticeProb.walkOp_finsetSum (Finset.range n)
    (fun k y => LatticeProb.Graph.killedHeat (LatticeProb.lattice d) D k y z) x).symm

/-- The killed Green kernel bounds the effect of one changed scenery coordinate on the
odometer killed outside `D`. -/
theorem abs_localizedOdometer_update_le (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (z : Site d) (v : ℝ) :
    ∀ n : ℕ, ∀ x : Site d,
      |localizedOdometer D ζ n x - localizedOdometer D (Function.update ζ z v) n x| ≤
        localGreenTime D n x z * |ζ z - v| := by
  classical
  intro n
  induction n with
  | zero =>
      intro x
      rw [localizedOdometer_zero hd, localizedOdometer_zero hd]
      simp [localGreenTime]
  | succ n ih =>
      intro x
      by_cases hx : x ∈ D
      · have hmax : |localizedOdometer D ζ (n + 1) x
              - localizedOdometer D (Function.update ζ z v) (n + 1) x| ≤
            |ζ x - Function.update ζ z v x| +
              |avg (localizedOdometer D ζ n) x
                - avg (localizedOdometer D (Function.update ζ z v) n) x| := by
          rw [localizedOdometer_succ' hd D ζ n x hx,
            localizedOdometer_succ' hd D (Function.update ζ z v) n x hx, max_comm 0, max_comm 0]
          refine (abs_max_sub_max_le_abs _ _ _).trans ?_
          convert abs_add_le (ζ x - Function.update ζ z v x)
            (avg (localizedOdometer D ζ n) x
              - avg (localizedOdometer D (Function.update ζ z v) n) x) using 1
          congr 1
          ring
        have ha := (abs_avg_sub_le_avg_abs (localizedOdometer D ζ n)
          (localizedOdometer D (Function.update ζ z v) n) x).trans (avg_mono_le ih x)
        have hav : avg (fun y => localGreenTime D n y z * |ζ z - v|) x =
            avg (fun y => localGreenTime D n y z) x * |ζ z - v| :=
          LatticeProb.walkOp_mul_const _ _ _
        rw [hav] at ha
        have hc : |ζ x - Function.update ζ z v x| = (if x = z then 1 else 0) * |ζ z - v| := by
          by_cases he : x = z
          · subst he; simp
          · simp [he]
        rw [hc] at hmax
        rw [localGreenTime_succ D n x z hx, add_mul]
        linarith
      · rw [localizedOdometer_of_notMem D ζ (n + 1) hx,
          localizedOdometer_of_notMem D (Function.update ζ z v) (n + 1) hx,
          localGreenTime_of_notMem hx]
        simp

/-- Killing the walk on more sites only lowers the coordinate Lipschitz constant, so the
odometer killed outside any `D` avoiding the origin has the coefficients of the odometer
killed at the origin alone. -/
theorem abs_avg_localizedOdometer_update_le (hd : 1 ≤ d) {D : Set (Site d)}
    (hD : D ⊆ {x : Site d | x ≠ 0}) (ζ : Site d → ℝ) (z : Site d) (v : ℝ) (n : ℕ) :
    |avg (localizedOdometer D ζ n) 0 - avg (localizedOdometer D (Function.update ζ z v) n) 0| ≤
      originInfluence z * |ζ z - v| := by
  classical
  have h := (abs_avg_sub_le_avg_abs (localizedOdometer D ζ n)
      (localizedOdometer D (Function.update ζ z v) n) 0).trans
    (avg_mono_le (abs_localizedOdometer_update_le hd D ζ z v n) 0)
  have hav : avg (fun x => localGreenTime D n x z * |ζ z - v|) 0 =
      avg (fun x => localGreenTime D n x z) 0 * |ζ z - v| :=
    LatticeProb.walkOp_mul_const _ _ _
  rw [hav] at h
  have hmono : avg (fun x => localGreenTime D n x z) 0 ≤ originInfluence z := by
    by_cases hz : z = 0
    · subst hz
      have hzero : ∀ x : Site d, localGreenTime D n x 0 = 0 := by
        intro x
        refine Finset.sum_eq_zero fun k _ => ?_
        exact LatticeProb.Network.killedHeat_of_target_not_mem
          (fun hmem => (hD hmem) rfl) k x
      have : avg (fun x => localGreenTime D n x (0 : Site d)) 0 = 0 := by
        simp [hzero, avg, LatticeProb.walkOp, LatticeProb.nbrSum]
      rw [this, originInfluence, if_pos rfl]
    · have hle : ∀ x : Site d, localGreenTime D n x z ≤ originGreenTime n x z := by
        intro x
        exact Finset.sum_le_sum fun k _ => killedHeat_mono hD k x z
      refine le_trans (avg_mono_le hle 0) ?_
      rw [originInfluence, if_neg hz]
      exact avg_originGreenTime_le_hitProb hd n z
  exact h.trans (mul_le_mul_of_nonneg_right hmono (abs_nonneg _))

end Sandpile
