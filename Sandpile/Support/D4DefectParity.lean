import Sandpile.Support.D4DefectTail
import Sandpile.Support.ContPairedGradient

/-!
# The ℓ² truncation defect across a parity change

The `ℓ²` bounds of `Sandpile.exists_heatKernel_tail_l2_four` compare two sites of the same
parity, which is what the total-variation gradient bound `eq:rw-tv-gradient` requires. In the
pairing of Step 1 of `prop:d4-superdiffusive-limit` the moving site `⌊Rz⌋` takes both parities
against the fixed base point, so the defect at a site of the other parity is compared with the
base point one time later: the one-step recursion in the base point writes `p_{n+1}(x',·)` as the
average of `p_n` over the `2d` neighbours of `x'`, each of which has the parity of `x` and lies
within `|x-x'|+1` of it, and the time shift telescopes against the tail, leaving one term
`p_t(0,·)` whose `ℓ²` norm is `O(t^{-1})`. This is the `ℓ²` transposition of
`Sandpile.Support.tsum_abs_heatKernel_sub_succ_le`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile

open Sandpile.Support

variable {d : ℕ}

/-- The square of a difference of heat kernels at two times is finitely
supported, hence summable. -/
theorem summable_heatKernel_sub_sq (n m : ℕ) (x w : Site d) :
    Summable fun y : Site d => (heatKernel d n x y - heatKernel d m w y) ^ 2 := by
  refine summable_of_ne_finset_zero (s := boxFinset x n ∪ boxFinset w m) fun z hz => ?_
  rw [Finset.mem_union, not_or] at hz
  have h1 : heatKernel d n x z = 0 := by
    by_contra hne; exact hz.1 (mem_boxFinset (heatKernel_support n x hne))
  have h2 : heatKernel d m w z = 0 := by
    by_contra hne; exact hz.2 (mem_boxFinset (heatKernel_support m w hne))
  simp [h1, h2]

/-- The square of a single heat kernel is finitely supported, hence summable. -/
theorem summable_heatKernel_sq (n : ℕ) (x : Site d) :
    Summable fun y : Site d => heatKernel d n x y ^ 2 := by
  refine summable_of_ne_finset_zero (s := boxFinset x n) fun z hz => ?_
  have h1 : heatKernel d n x z = 0 := by
    by_contra hne; exact hz (mem_boxFinset (heatKernel_support n x hne))
  simp [h1]

/-- **The `ℓ²` gradient bound across a parity change, one time against the
next.** -/
theorem tsum_sq_heatKernel_sub_succ_le {C : ℝ} (hC : 0 < C) (hd : 1 ≤ d)
    (hl2 : ∀ n : ℕ, 1 ≤ n → ∀ x w : Site d, Sandpile.External.SameParity x w →
      ∑' y : Site d, (heatKernel d n x y - heatKernel d n w y) ^ 2 ≤
        C * Sandpile.External.latticeDist x w * (n : ℝ) ^ (-(5 : ℝ) / 2))
    (n : ℕ) (hn : 1 ≤ n) (x x' : Site d)
    (hpar : ¬ Sandpile.External.SameParity x x') :
    ∑' y : Site d, (heatKernel d n x y - heatKernel d (n + 1) x' y) ^ 2 ≤
      C * (Sandpile.External.latticeDist x x' + 1) * (n : ℝ) ^ (-(5 : ℝ) / 2) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnpow : (0 : ℝ) ≤ (n : ℝ) ^ (-(5 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  set K : ℝ := C * (Sandpile.External.latticeDist x x' + 1) * (n : ℝ) ^ (-(5 : ℝ) / 2) with hK
  have hdist : (0 : ℝ) ≤ Sandpile.External.latticeDist x x' := Real.sqrt_nonneg _
  have hKnn : 0 ≤ K := by positivity
  -- the two neighbour bounds
  have hbadd : ∀ i : Fin d,
      ∑' y : Site d, (heatKernel d n x y - heatKernel d n (x' + unit i) y) ^ 2 ≤ K := by
    intro i
    have ht := latticeDist_triangle x x' (x' + unit i)
    rw [latticeDist_add_unit] at ht
    refine le_trans (hl2 n hn x (x' + unit i) (sameParity_add_unit_of_not hpar i)) ?_
    simp only [hK]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hC.le) hnpow
  have hbsub : ∀ i : Fin d,
      ∑' y : Site d, (heatKernel d n x y - heatKernel d n (x' - unit i) y) ^ 2 ≤ K := by
    intro i
    have ht := latticeDist_triangle x x' (x' - unit i)
    rw [latticeDist_sub_unit] at ht
    refine le_trans (hl2 n hn x (x' - unit i) (sameParity_sub_unit_of_not hpar i)) ?_
    simp only [hK]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hC.le) hnpow
  -- the pointwise convexity bound
  have hptw : ∀ y : Site d, (heatKernel d n x y - heatKernel d (n + 1) x' y) ^ 2 ≤
      (∑ i : Fin d, ((heatKernel d n x y - heatKernel d n (x' + unit i) y) ^ 2 +
        (heatKernel d n x y - heatKernel d n (x' - unit i) y) ^ 2)) / (2 * (d : ℝ)) := by
    intro y
    rw [heatKernel_sub_succ_eq hd n x x' y, div_pow]
    have hcs : (∑ i : Fin d,
        ((heatKernel d n x y - heatKernel d n (x' + unit i) y) +
          (heatKernel d n x y - heatKernel d n (x' - unit i) y))) ^ 2 ≤
        (d : ℝ) * ∑ i : Fin d,
          ((heatKernel d n x y - heatKernel d n (x' + unit i) y) +
            (heatKernel d n x y - heatKernel d n (x' - unit i) y)) ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => (heatKernel d n x y - heatKernel d n (x' + unit i) y) +
          (heatKernel d n x y - heatKernel d n (x' - unit i) y))
    have hpair : ∑ i : Fin d,
        ((heatKernel d n x y - heatKernel d n (x' + unit i) y) +
          (heatKernel d n x y - heatKernel d n (x' - unit i) y)) ^ 2 ≤
        2 * ∑ i : Fin d, ((heatKernel d n x y - heatKernel d n (x' + unit i) y) ^ 2 +
          (heatKernel d n x y - heatKernel d n (x' - unit i) y) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      nlinarith [sq_nonneg ((heatKernel d n x y - heatKernel d n (x' + unit i) y) -
        (heatKernel d n x y - heatKernel d n (x' - unit i) y))]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (2 * (d : ℝ)) ^ 2)]
    have hmove : (∑ i : Fin d, ((heatKernel d n x y - heatKernel d n (x' + unit i) y) ^ 2 +
        (heatKernel d n x y - heatKernel d n (x' - unit i) y) ^ 2)) / (2 * (d : ℝ)) *
        (2 * (d : ℝ)) ^ 2 =
        (∑ i : Fin d, ((heatKernel d n x y - heatKernel d n (x' + unit i) y) ^ 2 +
          (heatKernel d n x y - heatKernel d n (x' - unit i) y) ^ 2)) * (2 * (d : ℝ)) := by
      field_simp
    rw [hmove]
    nlinarith [hcs, hpair]
  -- sum the pointwise bound
  have hsumL : Summable fun y : Site d =>
      (heatKernel d n x y - heatKernel d (n + 1) x' y) ^ 2 :=
    summable_heatKernel_sub_sq n (n + 1) x x'
  have hsumeach : ∀ i : Fin d, Summable fun y : Site d =>
      ((heatKernel d n x y - heatKernel d n (x' + unit i) y) ^ 2 +
        (heatKernel d n x y - heatKernel d n (x' - unit i) y) ^ 2) :=
    fun i => (summable_heatKernel_sub_sq n n x (x' + unit i)).add
      (summable_heatKernel_sub_sq n n x (x' - unit i))
  have hsumR : Summable fun y : Site d =>
      (∑ i : Fin d, ((heatKernel d n x y - heatKernel d n (x' + unit i) y) ^ 2 +
        (heatKernel d n x y - heatKernel d n (x' - unit i) y) ^ 2)) / (2 * (d : ℝ)) :=
    (summable_sum (fun i (_ : i ∈ Finset.univ) => hsumeach i)).div_const _
  have hcalc : ∑' y : Site d,
      (∑ i : Fin d, ((heatKernel d n x y - heatKernel d n (x' + unit i) y) ^ 2 +
        (heatKernel d n x y - heatKernel d n (x' - unit i) y) ^ 2)) / (2 * (d : ℝ)) ≤ K := by
    have he : ∑' y : Site d,
        (∑ i : Fin d, ((heatKernel d n x y - heatKernel d n (x' + unit i) y) ^ 2 +
          (heatKernel d n x y - heatKernel d n (x' - unit i) y) ^ 2)) / (2 * (d : ℝ)) =
        (∑' y : Site d, ∑ i : Fin d,
          ((heatKernel d n x y - heatKernel d n (x' + unit i) y) ^ 2 +
            (heatKernel d n x y - heatKernel d n (x' - unit i) y) ^ 2)) / (2 * (d : ℝ)) := by
      simp_rw [div_eq_mul_inv]
      exact Summable.tsum_mul_right _ (summable_sum (fun i (_ : i ∈ Finset.univ) => hsumeach i))
    rw [he, (Summable.tsum_finsetSum fun i (_ : i ∈ Finset.univ) => hsumeach i)]
    have hterm : ∀ i : Fin d, (∑' y : Site d,
        ((heatKernel d n x y - heatKernel d n (x' + unit i) y) ^ 2 +
          (heatKernel d n x y - heatKernel d n (x' - unit i) y) ^ 2)) ≤ 2 * K := by
      intro i
      rw [Summable.tsum_add (summable_heatKernel_sub_sq n n x (x' + unit i))
        (summable_heatKernel_sub_sq n n x (x' - unit i))]
      linarith [hbadd i, hbsub i]
    have hsum : (∑ i : Fin d, ∑' y : Site d,
        ((heatKernel d n x y - heatKernel d n (x' + unit i) y) ^ 2 +
          (heatKernel d n x y - heatKernel d n (x' - unit i) y) ^ 2)) ≤ (d : ℝ) * (2 * K) := by
      calc _ ≤ ∑ _i : Fin d, 2 * K := Finset.sum_le_sum fun i _ => hterm i
        _ = (d : ℝ) * (2 * K) := by simp [Finset.sum_const]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hsum]
  exact le_trans (hsumL.tsum_le_tsum hptw hsumR) hcalc

/-- The summability of a shifted heat-kernel series in a transient dimension. -/
theorem summable_heatKernel_shift (hd : 3 ≤ d) (t : ℕ) (x y : Site d) :
    Summable fun j : ℕ => heatKernel d (t + j) x y :=
  (summable_heatKernel_transient hd x y).comp_injective
    (f := fun k : ℕ => heatKernel d k x y) (i := fun j : ℕ => t + j)
    (fun _ _ hpq => Nat.add_left_cancel hpq)

/-- **The time-shift telescoping.**  Comparing the tail at `x` with the base
point one time later costs exactly one term `p_t(0,·)`. -/
theorem tsum_tail_sub_eq_succ (hd : 3 ≤ d) (t : ℕ) (x y : Site d) :
    ∑' j : ℕ, (heatKernel d (t + j) x y - heatKernel d (t + j) 0 y) =
      (∑' j : ℕ, (heatKernel d (t + j) x y - heatKernel d (t + j + 1) 0 y)) -
        heatKernel d t 0 y := by
  have hx : Summable fun j : ℕ => heatKernel d (t + j) x y := summable_heatKernel_shift hd t x y
  have h0 : Summable fun j : ℕ => heatKernel d (t + j) 0 y := summable_heatKernel_shift hd t 0 y
  have h1 : Summable fun j : ℕ => heatKernel d (t + j + 1) 0 y := by
    have := (summable_heatKernel_transient hd (0 : Site d) y).comp_injective
      (f := fun k : ℕ => heatKernel d k 0 y) (i := fun j : ℕ => t + j + 1)
      (fun _ _ hpq => by simpa using hpq)
    exact this
  have hsplit : ∑' j : ℕ, heatKernel d (t + j) 0 y =
      heatKernel d t 0 y + ∑' j : ℕ, heatKernel d (t + j + 1) 0 y := by
    rw [h0.tsum_eq_zero_add]
    simp only [Nat.add_zero, ← Nat.add_assoc]
  rw [hx.tsum_sub h0, hx.tsum_sub h1, hsplit]
  ring

/-- The `ℓ²` norm of a single time slice at the base point: `‖p_t(0,·)‖₂² ≤ Ct^{-2}`. -/
theorem exists_heatKernel_diag_l2_four (hHK : Sandpile.External.HeatKernelBounds) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 1 ≤ t → ∀ x : Site 4,
      ∑' y : Site 4, heatKernel 4 t x y ^ 2 ≤ C * (((t : ℝ)) ^ 2)⁻¹ := by
  obtain ⟨C, hC, hb⟩ := exists_heatKernel_sq_bound_four hHK
  refine ⟨C, hC, fun t ht x => ?_⟩
  have habs : ∀ y : Site 4, |heatKernel 4 t x y| ≤ C * (((t : ℝ)) ^ 2)⁻¹ := by
    intro y
    rw [abs_of_nonneg (heatKernel_nonneg t x y)]
    exact hb t ht x y
  have hs : Summable fun y : Site 4 => |heatKernel 4 t x y| := by
    simpa [abs_of_nonneg (heatKernel_nonneg (d := 4) t x _)] using
      summable_heatKernel_site (d := 4) t x
  refine le_trans (tsum_sq_le_sup_mul_tsum_abs habs hs) ?_
  have hone : ∑' y : Site 4, |heatKernel 4 t x y| = 1 := by
    rw [tsum_congr (fun y => abs_of_nonneg (heatKernel_nonneg (d := 4) t x y))]
    exact tsum_heatKernel (by norm_num) t x
  rw [hone, mul_one]

/-- **The `ℓ²` size of the truncation defect in dimension four, at every
site.**  For sites of the parity of the base point this is
`exists_heatKernel_tail_l2_four`; for the other parity the tail is compared with
the base point one time later, and the telescoping leaves one term `p_t(0,·)` of
`ℓ²` norm `O(t^{-1})`. -/
theorem exists_heatKernel_tail_l2_four_all (hHK : Sandpile.External.HeatKernelBounds) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 1 ≤ t → ∀ x : Site 4,
      ∑' y : Site 4, ENNReal.ofReal
          ((∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j) 0 y)) ^ 2) ≤
        ENNReal.ofReal
          (C * (Sandpile.External.latticeDist x 0 + 1) * (t : ℝ) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨C1, hC1, hsame⟩ := exists_heatKernel_tail_l2_four hHK
  obtain ⟨C0, hC0, hl2⟩ := exists_heatKernel_increment_l2_four hHK
  obtain ⟨C2, hC2, hdiag⟩ := exists_heatKernel_diag_l2_four hHK
  refine ⟨C1 + 50 * C0 + 2 * C2, by positivity, fun t ht x => ?_⟩
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hdist : (0 : ℝ) ≤ Sandpile.External.latticeDist x 0 := Real.sqrt_nonneg _
  have hpow : (0 : ℝ) ≤ (t : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg ht0.le _
  by_cases hpar : Sandpile.External.SameParity x (0 : Site 4)
  · refine le_trans (hsame t ht x 0 hpar) (ENNReal.ofReal_le_ofReal ?_)
    have h1 : C1 * Sandpile.External.latticeDist x 0 ≤
        (C1 + 50 * C0 + 2 * C2) * (Sandpile.External.latticeDist x 0 + 1) := by nlinarith
    exact mul_le_mul_of_nonneg_right h1 hpow
  · -- the parity-crossing case
    have hB : (0 : ℝ) ≤ C0 * (Sandpile.External.latticeDist x 0 + 1) := by positivity
    have htail : ∑' y : Site 4, ENNReal.ofReal
        ((∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j + 1) 0 y)) ^ 2) ≤
        ENNReal.ofReal (25 * (C0 * (Sandpile.External.latticeDist x 0 + 1)) *
          (t : ℝ) ^ (-(1 : ℝ) / 2)) := by
      refine tsum_sq_tail_l2_le hB t ht
        (fun j y => heatKernel 4 (t + j) x y - heatKernel 4 (t + j + 1) 0 y)
        (fun j => summable_heatKernel_sub_sq (t + j) (t + j + 1) x 0) (fun j => ?_) (fun y => ?_)
      · exact tsum_sq_heatKernel_sub_succ_le hC0 (by norm_num) hl2 (t + j) (by omega) x 0 hpar
      · exact (summable_heatKernel_shift (by norm_num) t x y).sub
          ((summable_heatKernel_transient (by norm_num) (0 : Site 4) y).comp_injective
            (f := fun k : ℕ => heatKernel 4 k 0 y) (i := fun j : ℕ => t + j + 1)
            (fun _ _ hpq => by simpa using hpq))
    have hdg : ∑' y : Site 4, ENNReal.ofReal (heatKernel 4 t 0 y ^ 2) ≤
        ENNReal.ofReal (C2 * (((t : ℝ)) ^ 2)⁻¹) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun y => sq_nonneg _)
        (summable_heatKernel_sq (d := 4) t 0)]
      exact ENNReal.ofReal_le_ofReal (hdiag t ht 0)
    have hptw : ∀ y : Site 4,
        ENNReal.ofReal ((∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j) 0 y)) ^ 2) ≤
          2 * ENNReal.ofReal
              ((∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j + 1) 0 y)) ^ 2) +
            2 * ENNReal.ofReal (heatKernel 4 t 0 y ^ 2) := by
      intro y
      have hEq := tsum_tail_sub_eq_succ (d := 4) (by norm_num) t x y
      rw [hEq]
      have hb : (∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j + 1) 0 y) -
          heatKernel 4 t 0 y) ^ 2 ≤
          2 * (∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j + 1) 0 y)) ^ 2 +
            2 * heatKernel 4 t 0 y ^ 2 := by
        nlinarith [sq_nonneg ((∑' j : ℕ,
          (heatKernel 4 (t + j) x y - heatKernel 4 (t + j + 1) 0 y)) + heatKernel 4 t 0 y)]
      refine le_trans (ENNReal.ofReal_le_ofReal hb) ?_
      have hsplit : ENNReal.ofReal
          (2 * (∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j + 1) 0 y)) ^ 2 +
            2 * heatKernel 4 t 0 y ^ 2) =
          ENNReal.ofReal
              (2 * (∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j + 1) 0 y)) ^ 2) +
            ENNReal.ofReal (2 * heatKernel 4 t 0 y ^ 2) :=
        ENNReal.ofReal_add (by positivity) (by positivity)
      rw [hsplit]
      have hm1 : ENNReal.ofReal
          (2 * (∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j + 1) 0 y)) ^ 2) =
          2 * ENNReal.ofReal
            ((∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j + 1) 0 y)) ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      have hm2 : ENNReal.ofReal (2 * heatKernel 4 t 0 y ^ 2) =
          2 * ENNReal.ofReal (heatKernel 4 t 0 y ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      rw [hm1, hm2]
    calc ∑' y : Site 4, ENNReal.ofReal
          ((∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j) 0 y)) ^ 2)
        ≤ ∑' y : Site 4, (2 * ENNReal.ofReal
              ((∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j + 1) 0 y)) ^ 2) +
            2 * ENNReal.ofReal (heatKernel 4 t 0 y ^ 2)) := ENNReal.tsum_le_tsum hptw
      _ = 2 * (∑' y : Site 4, ENNReal.ofReal
              ((∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j + 1) 0 y)) ^ 2)) +
            2 * ∑' y : Site 4, ENNReal.ofReal (heatKernel 4 t 0 y ^ 2) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ 2 * ENNReal.ofReal (25 * (C0 * (Sandpile.External.latticeDist x 0 + 1)) *
              (t : ℝ) ^ (-(1 : ℝ) / 2)) + 2 * ENNReal.ofReal (C2 * (((t : ℝ)) ^ 2)⁻¹) := by
          gcongr
      _ ≤ ENNReal.ofReal ((C1 + 50 * C0 + 2 * C2) *
              (Sandpile.External.latticeDist x 0 + 1) * (t : ℝ) ^ (-(1 : ℝ) / 2)) := by
          have he1 : (2 : ℝ≥0∞) * ENNReal.ofReal (25 *
              (C0 * (Sandpile.External.latticeDist x 0 + 1)) * (t : ℝ) ^ (-(1 : ℝ) / 2)) =
              ENNReal.ofReal (2 * (25 * (C0 * (Sandpile.External.latticeDist x 0 + 1)) *
                (t : ℝ) ^ (-(1 : ℝ) / 2))) := by
            rw [ENNReal.ofReal_mul (p := 2)
              (q := 25 * (C0 * (Sandpile.External.latticeDist x 0 + 1)) *
                (t : ℝ) ^ (-(1 : ℝ) / 2)) (by norm_num)]
            norm_num
          have he2 : (2 : ℝ≥0∞) * ENNReal.ofReal (C2 * (((t : ℝ)) ^ 2)⁻¹) =
              ENNReal.ofReal (2 * (C2 * (((t : ℝ)) ^ 2)⁻¹)) := by
            rw [ENNReal.ofReal_mul (p := 2) (q := C2 * (((t : ℝ)) ^ 2)⁻¹) (by norm_num)]
            norm_num
          rw [he1, he2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hinv : (((t : ℝ)) ^ 2)⁻¹ ≤ (t : ℝ) ^ (-(1 : ℝ) / 2) := by
            have h2 : (((t : ℝ)) ^ 2)⁻¹ = (t : ℝ) ^ (-(2 : ℝ)) := by
              rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
                Real.rpow_natCast]
            rw [h2]
            exact Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
          have hDu : (0 : ℝ) ≤ (Sandpile.External.latticeDist x 0 + 1) *
              (t : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
          have hvu : (((t : ℝ)) ^ 2)⁻¹ ≤
              (Sandpile.External.latticeDist x 0 + 1) * (t : ℝ) ^ (-(1 : ℝ) / 2) :=
            le_trans hinv (le_mul_of_one_le_left hpow (by linarith))
          calc 2 * (25 * (C0 * (Sandpile.External.latticeDist x 0 + 1)) *
                  (t : ℝ) ^ (-(1 : ℝ) / 2)) + 2 * (C2 * (((t : ℝ)) ^ 2)⁻¹)
              ≤ 50 * C0 * ((Sandpile.External.latticeDist x 0 + 1) *
                  (t : ℝ) ^ (-(1 : ℝ) / 2)) +
                2 * C2 * ((Sandpile.External.latticeDist x 0 + 1) *
                  (t : ℝ) ^ (-(1 : ℝ) / 2)) := by nlinarith [hC2.le, hvu]
            _ ≤ (C1 + 50 * C0 + 2 * C2) * ((Sandpile.External.latticeDist x 0 + 1) *
                  (t : ℝ) ^ (-(1 : ℝ) / 2)) := by nlinarith [hC1.le, hDu]
            _ = (C1 + 50 * C0 + 2 * C2) * (Sandpile.External.latticeDist x 0 + 1) *
                  (t : ℝ) ^ (-(1 : ℝ) / 2) := by ring

end Sandpile
