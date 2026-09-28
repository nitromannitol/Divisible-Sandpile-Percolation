import Sandpile.External.VarianceScale
import LatticeProb.Walk.VarianceScale
import LatticeProb.Walk.WindowD4
import LatticeProb.Walk.Correlation

/-!
# The finite-time variance scale is proved

The finite-time variance scale is no longer assumed.

`Sandpile/External/VarianceScale.lean` states the random-walk estimates of
`ssec:green-estimates` as a `Prop`, as a cited result must be stated while it is
only assumed.  The shared library now proves all three clauses for the simple
random walk, so the `Prop` is discharged here.  The `Prop` and its name are left
untouched, so no frozen statement changes, and every node carrying
`Sandpile.External.VarianceScale` as a hypothesis becomes unconditional.

The only content is that this file's `heatKernel` and the library's `srwHeat`
are the same recursion written twice, once in the two-point form and once in the
translation-invariant form; they are identified by induction on the time.
Everything after that is `funext`, the shift invariance of a sum over the
lattice, and the fact that the variance and correlation rates of the two
developments are definitionally equal.
-/

open LatticeProb

/-- The paper's two-point heat kernel `Sandpile.heatKernel` agrees with the library's
translation-invariant `LatticeProb.srwHeat`, by induction on the time using the same
nearest-neighbor recursion on both sides. -/
theorem Sandpile.heatKernel_eq_srwHeat (d : ℕ) : ∀ (k : ℕ) (x y : Sandpile.Site d),
    Sandpile.heatKernel d k x y = LatticeProb.srwHeat d k (y - x) := by
  intro k
  induction k with
  | zero =>
      intro x y
      show (if x = y then (1 : ℝ) else 0) = LatticeProb.srwHeat d 0 (y - x)
      rw [LatticeProb.srwHeat_zero]
      by_cases h : x = y
      · rw [if_pos h, if_pos (by rw [h]; ring)]
      · rw [if_neg h, if_neg (fun hc => h (by linear_combination -hc))]
  | succ k ih =>
      intro x y
      show (∑ i : Fin d, (Sandpile.heatKernel d k (x + LatticeProb.unit i) y
            + Sandpile.heatKernel d k (x - LatticeProb.unit i) y)) / (2 * (d : ℝ))
          = LatticeProb.srwHeat d (k + 1) (y - x)
      rw [LatticeProb.srwHeat_succ_eq_sum_dir]
      congr 1
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ih (x + LatticeProb.unit i) y, ih (x - LatticeProb.unit i) y, Fintype.sum_bool]
      rw [LatticeProb.dirVec_eq_unit, LatticeProb.dirVec_eq_neg_unit]
      have h1 : y - (x + LatticeProb.unit i) = y - x + -LatticeProb.unit i := by ring
      have h2 : y - (x - LatticeProb.unit i) = y - x + LatticeProb.unit i := by ring
      rw [h1, h2]
      ring

/-- `Sandpile.greenTime`, summed from the origin, agrees with the library's
`LatticeProb.srwGreen`, termwise via `heatKernel_eq_srwHeat`. -/
theorem Sandpile.greenTime_eq_srwGreen (d t : ℕ) (y : Sandpile.Site d) :
    Sandpile.greenTime d t 0 y = LatticeProb.srwGreen d t y := by
  show (∑ k ∈ Finset.range t, Sandpile.heatKernel d k 0 y) = LatticeProb.srwGreen d t y
  rw [LatticeProb.srwGreen]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [heatKernel_eq_srwHeat d k 0 y, sub_zero]

/-- The file's `varianceRate` and the library's `LatticeProb.varianceRate` are the same
`if`-chain on the dimension, definitionally. -/
theorem Sandpile.varianceRate_eq (d t : ℕ) :
    Sandpile.External.Variance.varianceRate d t = LatticeProb.varianceRate d t := rfl

/-- The first conjunct of `Sandpile.External.VarianceScale`, discharged. -/
theorem Sandpile.variance_clause_one :
    ∀ d : ℕ, 1 ≤ d →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ t : ℕ, 2 ≤ t →
          c * Sandpile.External.Variance.varianceRate d t ≤
              ∑' y : Sandpile.Site d, Sandpile.greenTime d t 0 y ^ 2 ∧
            (∑' y : Sandpile.Site d, Sandpile.greenTime d t 0 y ^ 2) ≤
              C * Sandpile.External.Variance.varianceRate d t := by
  intro d hd
  obtain ⟨c, C, hc, hC, h⟩ := LatticeProb.exists_tsum_srwGreen_sq_bounds (d := d) hd
  refine ⟨c, C, hc, hC, fun t ht => ?_⟩
  have hfun : (fun y : Sandpile.Site d => Sandpile.greenTime d t 0 y ^ 2)
      = fun y : Sandpile.Site d => LatticeProb.srwGreen d t y ^ 2 := by
    funext y
    rw [greenTime_eq_srwGreen]
  rw [hfun, varianceRate_eq]
  exact h t ht

/-- The two-argument form of `greenTime_eq_srwGreen`: the paper's Green sum between
arbitrary sites `x` and `y` agrees with the library's translation-invariant `srwGreen`
evaluated at the difference `y - x`. -/
theorem Sandpile.greenTime_eq_srwGreen' (d t : ℕ) (x y : Sandpile.Site d) :
    Sandpile.greenTime d t x y = LatticeProb.srwGreen d t (y - x) := by
  show (∑ k ∈ Finset.range t, Sandpile.heatKernel d k x y) = LatticeProb.srwGreen d t (y - x)
  rw [LatticeProb.srwGreen]
  exact Finset.sum_congr rfl fun k _ => heatKernel_eq_srwHeat d k x y

/-- The file's `windowKernel` (a finite time-window sum of the two-point heat kernel)
agrees with the library's translation-invariant `LatticeProb.srwWindow`. -/
theorem Sandpile.windowKernel_eq_srwWindow (m n : ℕ) (x z : Sandpile.Site 4) :
    Sandpile.External.Variance.windowKernel m n x z = LatticeProb.srwWindow 4 m n (z - x) := by
  rw [Sandpile.External.Variance.windowKernel, LatticeProb.srwWindow]
  exact Finset.sum_congr rfl fun k _ => heatKernel_eq_srwHeat 4 k x z

/-- Summing `g` over `z - x` for `z` ranging over the lattice is the same as summing `g`
directly, by the library's shift invariance `LatticeProb.tsum_shift`. -/
theorem Sandpile.tsum_shift_sub {d : ℕ} (x : Sandpile.Site d) (g : Sandpile.Site d → ℝ) :
    ∑' z : Sandpile.Site d, g (z - x) = ∑' y : Sandpile.Site d, g y := by
  have h := LatticeProb.tsum_shift (-x) g
  simpa [sub_eq_add_neg] using h

/-- The file's `corrRate` and the library's `LatticeProb.corrRate` are the same `if`-chain
on the dimension, definitionally. -/
theorem Sandpile.corrRate_eq (d m n : ℕ) :
    Sandpile.External.Variance.corrRate d m n = LatticeProb.corrRate d m n := rfl

-- FROZEN-STATEMENT-BEGIN
/-- The random-walk estimates of `ssec:green-estimates`, `eq:Qt-table`,
`eq:corr-bound` and the four dimension-four window displays, proved rather than
assumed. -/
theorem Sandpile.External.varianceScale : Sandpile.External.VarianceScale
-- FROZEN-STATEMENT-END
:= by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨c, C, hc, hC, h⟩ := LatticeProb.exists_tsum_srwGreen_sq_bounds (d := d) hd
    refine ⟨c, C, hc, hC, fun t ht => ?_⟩
    have hfun : (fun y : Sandpile.Site d => Sandpile.greenTime d t 0 y ^ 2)
        = fun y : Sandpile.Site d => LatticeProb.srwGreen d t y ^ 2 := by
      funext y; rw [greenTime_eq_srwGreen]
    rw [hfun, varianceRate_eq]
    exact h t ht
  · intro d hd hd4
    obtain ⟨C, hC, h⟩ := LatticeProb.exists_tsum_srwGreen_mul_le (d := d) hd hd4
    refine ⟨C, hC, fun m n hm hmn => ?_⟩
    have hfun : (fun x : Sandpile.Site d =>
          Sandpile.greenTime d m 0 x * Sandpile.greenTime d n 0 x)
        = fun x : Sandpile.Site d => LatticeProb.srwGreen d m x * LatticeProb.srwGreen d n x := by
      funext x; rw [greenTime_eq_srwGreen, greenTime_eq_srwGreen]
    have hfm : (fun x : Sandpile.Site d => Sandpile.greenTime d m 0 x ^ 2)
        = fun x : Sandpile.Site d => LatticeProb.srwGreen d m x ^ 2 := by
      funext x; rw [greenTime_eq_srwGreen]
    have hfn : (fun x : Sandpile.Site d => Sandpile.greenTime d n 0 x ^ 2)
        = fun x : Sandpile.Site d => LatticeProb.srwGreen d n x ^ 2 := by
      funext x; rw [greenTime_eq_srwGreen]
    rw [hfun, hfm, hfn, corrRate_eq]
    exact h m n hm hmn
  · obtain ⟨C₁, hC₁, hwin⟩ := LatticeProb.exists_tsum_srwWindow_sq_le
    obtain ⟨C₂, hC₂, hfull⟩ := LatticeProb.exists_tsum_srwGreen_four_sq_le
    refine ⟨max (max C₁ C₂) (max (2 * LatticeProb.diagConst 4) (1 + 2 * LatticeProb.diagConst 4)),
      lt_of_lt_of_le hC₁ (le_trans (le_max_left _ _) (le_max_left _ _)), ?_, ?_⟩
    · intro m n hm hmn x
      constructor
      · have hfun : (fun z : Sandpile.Site 4 =>
              Sandpile.External.Variance.windowKernel m n x z ^ 2)
            = fun z : Sandpile.Site 4 => LatticeProb.srwWindow 4 m n (z - x) ^ 2 := by
          funext z; rw [windowKernel_eq_srwWindow]
        rw [hfun, tsum_shift_sub x (fun y => LatticeProb.srwWindow 4 m n y ^ 2)]
        refine le_trans (hwin m n hm hmn.le) ?_
        have hlog : (0 : ℝ) ≤ Real.log (((n : ℝ) + 2) / ((m : ℝ) + 2)) := by
          refine Real.log_nonneg ((one_le_div (by positivity)).mpr ?_)
          have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn.le
          linarith
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      · intro z
        rw [windowKernel_eq_srwWindow]
        refine le_trans (LatticeProb.srwWindow_le hm n _) ?_
        have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        refine div_le_div_of_nonneg_right ?_ hmpos.le
        exact le_trans (le_max_left _ _) (le_max_right _ _)
    · intro n hn x
      constructor
      · have hfun : (fun z : Sandpile.Site 4 => Sandpile.greenTime 4 n x z ^ 2)
            = fun z : Sandpile.Site 4 => LatticeProb.srwGreen 4 n (z - x) ^ 2 := by
          funext z; rw [greenTime_eq_srwGreen']
        rw [hfun, tsum_shift_sub x (fun y => LatticeProb.srwGreen 4 n y ^ 2)]
        refine le_trans (hfull n hn) ?_
        have hlog : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) := by
          refine Real.log_nonneg ?_
          have : (0 : ℝ) ≤ (n : ℝ) := by positivity
          linarith
        refine mul_le_mul_of_nonneg_right ?_ hlog
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      · intro z
        rw [greenTime_eq_srwGreen']
        refine le_trans (LatticeProb.srwGreen_four_le n _) ?_
        exact le_trans (le_max_right _ _) (le_max_right _ _)
