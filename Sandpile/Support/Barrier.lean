/-
The parabolic barrier of Step 1 of the proof of `thm:dgt4-height-lower`,
`sandpile.tex:4197-4230`, and the two elementary facts about the squared
Euclidean norm that it rests on: its neighbour average exceeds it by exactly
one, and it dominates the square of the sup-norm distance to the origin.

If the scenery is at most `-a` on a box and the odometer is below the parabola
`a|z|^2/2` on the boundary sphere at every time, then the recursion cannot lift
it above the parabola anywhere in the box, at any time.  In particular the
neighbour average at the origin is at most `a/2`, which is what makes the
reflected increment positive.
-/
import Sandpile.Support.Odometer
import Sandpile.Support.Kernel
import Sandpile.Support.Stationary
import LatticeProb.Walk.SRWDiag

open LatticeProb

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- The cast of the natural absolute value of an integer is the absolute value
of its cast. -/
theorem natAbs_cast_real (n : ℤ) : ((n.natAbs : ℕ) : ℝ) = |((n : ℤ) : ℝ)| := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs n, Int.cast_natCast]

theorem sqNorm_add_unit (x : Site d) (i : Fin d) :
    sqNorm (x + unit i) = sqNorm x + 2 * ((x i : ℤ) : ℝ) + 1 := by
  classical
  have hterm : ∀ j : Fin d, (((x + unit i) j : ℤ) : ℝ) ^ 2
      = ((x j : ℤ) : ℝ) ^ 2 + (if j = i then 2 * ((x i : ℤ) : ℝ) + 1 else 0) := by
    intro j
    by_cases h : j = i
    · subst h
      have : (x + unit j) j = x j + 1 := by simp [unit, Pi.single_eq_same]
      rw [this]
      push_cast
      split_ifs with h2
      · ring
      · exact absurd rfl h2
    · have : (x + unit i) j = x j := by
        simp [unit, Pi.single_eq_of_ne h]
      rw [this, if_neg h, add_zero]
  rw [sqNorm, sqNorm, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ i (fun _ => 2 * ((x i : ℤ) : ℝ) + 1)]
  simp
  ring

theorem sqNorm_sub_unit (x : Site d) (i : Fin d) :
    sqNorm (x - unit i) = sqNorm x - 2 * ((x i : ℤ) : ℝ) + 1 := by
  classical
  have hterm : ∀ j : Fin d, (((x - unit i) j : ℤ) : ℝ) ^ 2
      = ((x j : ℤ) : ℝ) ^ 2 + (if j = i then -(2 * ((x i : ℤ) : ℝ)) + 1 else 0) := by
    intro j
    by_cases h : j = i
    · subst h
      have : (x - unit j) j = x j - 1 := by simp [unit, Pi.single_eq_same]
      rw [this]
      push_cast
      split_ifs with h2
      · ring
      · exact absurd rfl h2
    · have : (x - unit i) j = x j := by
        simp [unit, Pi.single_eq_of_ne h]
      rw [this, if_neg h, add_zero]
  rw [sqNorm, sqNorm, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ i (fun _ => -(2 * ((x i : ℤ) : ℝ)) + 1)]
  simp
  ring

/-- **The parabola is the discrete barrier**: the neighbour average of the
squared norm exceeds it by exactly one. -/
theorem avg_sqNorm (hd : 1 ≤ d) (x : Site d) : avg (sqNorm (d := d)) x = sqNorm x + 1 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  show (∑ i : Fin d, (sqNorm (x + unit i) + sqNorm (x - unit i))) / (2 * (d : ℝ))
      = sqNorm x + 1
  have hsum : ∀ i : Fin d, sqNorm (x + unit i) + sqNorm (x - unit i)
      = 2 * sqNorm x + 2 := by
    intro i
    rw [sqNorm_add_unit, sqNorm_sub_unit]
    ring
  rw [Finset.sum_congr rfl fun i _ => hsum i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The squared sup-norm distance to the origin is at most the squared Euclidean
norm. -/
theorem sq_boxDist_le_sqNorm (x : Site d) :
    ((boxDist (0 : Site d) x : ℕ) : ℝ) ^ 2 ≤ sqNorm x := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : boxDist (0 : Site 0) x = 0 := by
      simp [boxDist]
    rw [this]
    simp [sqNorm]
  · haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
      Finset.univ_nonempty (fun i : Fin d => ((0 : Site d) i - x i).natAbs)
    have hb : boxDist (0 : Site d) x = (x i).natAbs := by
      rw [boxDist, hi]
      simp
    rw [hb]
    have hcast : (((x i).natAbs : ℕ) : ℝ) ^ 2 = ((x i : ℤ) : ℝ) ^ 2 := by
      rw [natAbs_cast_real, sq_abs]
    rw [hcast, sqNorm]
    exact Finset.single_le_sum (f := fun j : Fin d => ((x j : ℤ) : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-! ### The parabolic barrier -/

/-- The odometer written in the scenery is nondecreasing in time. -/
theorem odometerOf_le_succ (ζ : Site d → ℝ) :
    ∀ (t : ℕ) (x : Site d), odometerOf ζ t x ≤ odometerOf ζ (t + 1) x := by
  intro t
  induction t with
  | zero => intro x; exact odometerOf_nonneg _ _ _
  | succ n ih =>
      intro x
      have hstep : avg (odometerOf ζ n) x ≤ avg (odometerOf ζ (n + 1)) x := by
        show (∑ i : Fin d, (odometerOf ζ n (x + unit i) + odometerOf ζ n (x - unit i)))
              / (2 * (d : ℝ))
            ≤ (∑ i : Fin d, (odometerOf ζ (n+1) (x + unit i) + odometerOf ζ (n+1) (x - unit i)))
              / (2 * (d : ℝ))
        rcases Nat.eq_zero_or_pos d with hd0 | hd0
        · subst hd0; simp
        · have hc : (0 : ℝ) < 2 * (d : ℝ) := by
            have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
            linarith
          refine div_le_div_of_nonneg_right ?_ hc.le
          exact Finset.sum_le_sum fun i _ => add_le_add (ih _) (ih _)
      show max 0 (ζ x + avg (odometerOf ζ n) x) ≤ max 0 (ζ x + avg (odometerOf ζ (n+1)) x)
      exact max_le_max le_rfl (by linarith)

theorem odometerOf_mono_time (ζ : Site d → ℝ) (x : Site d) :
    Monotone fun t => odometerOf ζ t x :=
  monotone_nat_of_le_succ fun t => odometerOf_le_succ ζ t x

/-- **The parabolic barrier.**  If the scenery is at most `-a` on the box of
radius `R` about the origin and the odometer is below the parabola `a|z|^2/2` on
the boundary sphere at every time, then it is below the parabola on the whole
box at every time.  This is the claim inside Step 1 of the proof of
`thm:dgt4-height-lower`, `sandpile.tex:4207-4223`. -/
theorem odometerOf_le_parabola (hd : 1 ≤ d) (ζ : Site d → ℝ) (a : ℝ) (ha : 0 ≤ a) (R t : ℕ)
    (hζ : ∀ z : Site d, boxDist 0 z ≤ R → ζ z ≤ -a)
    (hbnd : ∀ s : ℕ, s ≤ t → ∀ z : Site d, boxDist 0 z = R →
      odometerOf ζ s z ≤ a / 2 * sqNorm z) :
    ∀ s : ℕ, s ≤ t → ∀ x : Site d, boxDist 0 x ≤ R → odometerOf ζ s x ≤ a / 2 * sqNorm x := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  intro s
  induction s with
  | zero =>
      intro _ x _
      have h0 : odometerOf ζ 0 x = 0 := rfl
      rw [h0]
      exact mul_nonneg (by linarith) (sqNorm_nonneg x)
  | succ n ih =>
      intro hnt x hx
      have hn : n ≤ t := Nat.le_of_succ_le hnt
      rcases eq_or_lt_of_le hx with hxR | hxR
      · exact hbnd (n + 1) hnt x hxR
      · -- the neighbours stay in the box
        have hnb : ∀ i : Fin d, boxDist 0 (x + unit i) ≤ R ∧ boxDist 0 (x - unit i) ≤ R := by
          intro i
          constructor
          · refine le_trans (boxDist_trans 0 x (x + unit i)) ?_
            have := boxDist_add_unit x i
            omega
          · refine le_trans (boxDist_trans 0 x (x - unit i)) ?_
            have := boxDist_sub_unit x i
            omega
        have hterm : ∀ i : Fin d,
            odometerOf ζ n (x + unit i) + odometerOf ζ n (x - unit i)
              ≤ a / 2 * sqNorm (x + unit i) + a / 2 * sqNorm (x - unit i) :=
          fun i => add_le_add (ih hn _ (hnb i).1) (ih hn _ (hnb i).2)
        have havg : avg (odometerOf ζ n) x ≤ a / 2 * (sqNorm x + 1) := by
          have hsum : (∑ i : Fin d, (odometerOf ζ n (x + unit i) + odometerOf ζ n (x - unit i)))
              ≤ ∑ i : Fin d, (a / 2 * sqNorm (x + unit i) + a / 2 * sqNorm (x - unit i)) :=
            Finset.sum_le_sum fun i _ => hterm i
          have hid : (∑ i : Fin d, (a / 2 * sqNorm (x + unit i) + a / 2 * sqNorm (x - unit i)))
              / (2 * (d : ℝ)) = a / 2 * (sqNorm x + 1) := by
            have hav : (∑ i : Fin d, (sqNorm (x + unit i) + sqNorm (x - unit i)))
                / (2 * (d : ℝ)) = sqNorm x + 1 := avg_sqNorm (d := d) hd x
            have hfac : (∑ i : Fin d, (a / 2 * sqNorm (x + unit i) + a / 2 * sqNorm (x - unit i)))
                = a / 2 * ∑ i : Fin d, (sqNorm (x + unit i) + sqNorm (x - unit i)) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [hfac, mul_div_assoc, hav]
          show (∑ i : Fin d, (odometerOf ζ n (x + unit i) + odometerOf ζ n (x - unit i)))
              / (2 * (d : ℝ)) ≤ a / 2 * (sqNorm x + 1)
          rw [← hid]
          exact div_le_div_of_nonneg_right hsum (by linarith)
        have hζx : ζ x ≤ -a := hζ x hx
        show max 0 (ζ x + avg (odometerOf ζ n) x) ≤ a / 2 * sqNorm x
        refine max_le ?_ ?_
        · exact mul_nonneg (by linarith) (sqNorm_nonneg x)
        · linarith

/-- At the origin the barrier bounds the neighbour average by `a/2`. -/
theorem avg_odometerOf_le_half (hd : 1 ≤ d) (ζ : Site d → ℝ) (a : ℝ) (_ha : 0 ≤ a) (R : ℕ)
    (hR : 1 ≤ R)
    (t : ℕ)
    (hpar : ∀ x : Site d, boxDist 0 x ≤ R → odometerOf ζ t x ≤ a / 2 * sqNorm x) :
    avg (odometerOf ζ t) 0 ≤ a / 2 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnb : ∀ i : Fin d, boxDist (0 : Site d) (0 + unit i) ≤ R ∧
      boxDist (0 : Site d) (0 - unit i) ≤ R := by
    intro i
    exact ⟨le_trans (boxDist_add_unit 0 i) hR, le_trans (boxDist_sub_unit 0 i) hR⟩
  have hsum : (∑ i : Fin d, (odometerOf ζ t ((0 : Site d) + unit i)
        + odometerOf ζ t ((0 : Site d) - unit i)))
      ≤ ∑ i : Fin d, (a / 2 * sqNorm ((0 : Site d) + unit i)
        + a / 2 * sqNorm ((0 : Site d) - unit i)) :=
    Finset.sum_le_sum fun i _ =>
      add_le_add (hpar _ (hnb i).1) (hpar _ (hnb i).2)
  have hid : (∑ i : Fin d, (a / 2 * sqNorm ((0 : Site d) + unit i)
        + a / 2 * sqNorm ((0 : Site d) - unit i))) / (2 * (d : ℝ)) = a / 2 := by
    have hav : (∑ i : Fin d, (sqNorm ((0 : Site d) + unit i)
          + sqNorm ((0 : Site d) - unit i))) / (2 * (d : ℝ)) = sqNorm (0 : Site d) + 1 :=
      avg_sqNorm (d := d) hd (0 : Site d)
    have hfac : (∑ i : Fin d, (a / 2 * sqNorm ((0 : Site d) + unit i)
          + a / 2 * sqNorm ((0 : Site d) - unit i)))
        = a / 2 * ∑ i : Fin d, (sqNorm ((0 : Site d) + unit i)
          + sqNorm ((0 : Site d) - unit i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hfac, mul_div_assoc, hav, sqNorm_zero]
    ring
  show (∑ i : Fin d, (odometerOf ζ t ((0 : Site d) + unit i)
      + odometerOf ζ t ((0 : Site d) - unit i))) / (2 * (d : ℝ)) ≤ a / 2
  rw [← hid]
  exact div_le_div_of_nonneg_right hsum (by linarith)

end Sandpile
