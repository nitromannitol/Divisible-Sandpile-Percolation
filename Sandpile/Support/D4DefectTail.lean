import Sandpile.Support.D4TruncationDefect

/-!
# The `ℓ²` size of the truncation defect in dimension four

Step 1 of `prop:d4-superdiffusive-limit` needs the time truncation in `V_{t_R}` to wash out
at superdiffusive times, and the quantity that measures it is the `ℓ²` norm in the second
variable of the tail `Δ_t(x,y) = ∑_{j≥t}(p_j(x,y) - p_j(w,y))`. At a single time,
`Sandpile.exists_heatKernel_increment_l2_four` gives `‖p_j(x,·) - p_j(w,·)‖₂² ≤ C|x-w|
j^{-5/2}`. Summing the tail is a weighted Cauchy-Schwarz at the weights `a_j = j^{-5/4}`: the
weight series has tail `∑_{j≥t} j^{-5/4} ≤ 5 t^{-1/4}`, and dividing the single-time bound by
the weight leaves the same series again, so `‖Δ_t(x,·)‖₂² ≤ (∑_{j≥t}a_j)·C|x-w|·(∑_{j≥t}a_j)
≤ 25 C |x-w| t^{-1/2}`. The threshold `t ≫ R²` visible in `R^{1/2}t^{-1/4}` is exactly the
paper's `α > 2`. The sum over the lattice is taken in `ℝ≥0∞`, where no summability hypothesis
is needed to exchange it with the sum over times.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The tail of the series `∑ j^{-5/4}` from `t`: `∑_{k≥0}(t+k)^{-5/4} ≤ 5t^{-1/4}`. -/
theorem tsum_tail_rpow_le (t : ℕ) (ht : 1 ≤ t) :
    ∑' k : ℕ, ((t + k : ℕ) : ℝ) ^ (-(5 : ℝ) / 4) ≤ 5 * (t : ℝ) ^ (-(1 : ℝ) / 4) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hfirst : (t : ℝ) ^ (-(5 : ℝ) / 4) ≤ (t : ℝ) ^ (-(1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have hnn : (0 : ℝ) ≤ (t : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg ht0.le _
  refine Real.tsum_le_of_sum_range_le (fun k => Real.rpow_nonneg (by positivity) _) ?_
  intro N
  match N with
  | 0 => simpa using by linarith
  | (M + 1) =>
    rw [Finset.sum_range_succ']
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-(5 : ℝ) / 4))
        (Set.Icc ((t : ℝ)) ((t : ℝ) + (M : ℕ))) := by
      refine (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono ?_
      intro x hx
      simp only [Set.mem_Icc] at hx
      exact lt_of_lt_of_le ht0 hx.1
    have hsum := AntitoneOn.sum_le_integral hanti
    have hint : ∫ x in (t : ℝ)..((t : ℝ) + (M : ℕ)), x ^ (-(5 : ℝ) / 4) =
        (((t : ℝ) + (M : ℕ)) ^ (-(1 : ℝ) / 4) - (t : ℝ) ^ (-(1 : ℝ) / 4)) / (-(1 : ℝ) / 4) := by
      have h0 : (0 : ℝ) ∉ Set.uIcc ((t : ℝ)) ((t : ℝ) + (M : ℕ)) := by
        simp only [Set.mem_uIcc, not_or]
        constructor <;> rintro ⟨h1, h2⟩ <;> nlinarith [Nat.cast_nonneg (α := ℝ) M]
      have := integral_rpow (a := (t : ℝ)) (b := ((t : ℝ) + (M : ℕ)))
        (r := -(5 : ℝ) / 4) (Or.inr ⟨by norm_num, h0⟩)
      rw [this]
      norm_num
    rw [hint] at hsum
    have hMnn : (0 : ℝ) ≤ ((t : ℝ) + (M : ℕ)) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_nonneg (by positivity) _
    have hcast : ∀ i : ℕ, ((t + (i + 1) : ℕ) : ℝ) ^ (-(5 : ℝ) / 4) =
        (fun x : ℝ => x ^ (-(5 : ℝ) / 4)) ((t : ℝ) + ((i + 1 : ℕ) : ℝ)) := by
      intro i; push_cast; ring_nf
    rw [Finset.sum_congr rfl (fun i _ => hcast i)]
    have : (((t : ℝ) + (M : ℕ)) ^ (-(1 : ℝ) / 4) - (t : ℝ) ^ (-(1 : ℝ) / 4)) / (-(1 : ℝ) / 4)
        ≤ 4 * (t : ℝ) ^ (-(1 : ℝ) / 4) := by
      rw [div_le_iff_of_neg (by norm_num : (-(1:ℝ)/4) < 0)]
      nlinarith
    have hz : ((t + 0 : ℕ) : ℝ) ^ (-(5 : ℝ) / 4) = (t : ℝ) ^ (-(5 : ℝ) / 4) := by norm_num
    simp only [hz]
    linarith

/-- The shifted series `∑ (t+k)^{-5/4}` is summable. -/
theorem summable_tail_rpow (t : ℕ) :
    Summable fun k : ℕ => ((t + k : ℕ) : ℝ) ^ (-(5 : ℝ) / 4) := by
  have hs : Summable fun n : ℕ => ((n : ℝ)) ^ (-(5 : ℝ) / 4) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  exact hs.comp_injective (fun a b hab => by omega)

/-- The square of a heat-kernel increment is finitely supported, hence summable. -/
theorem summable_heatKernel_increment_sq (n : ℕ) (x w : Site d) :
    Summable fun y : Site d => (heatKernel d n x y - heatKernel d n w y) ^ 2 := by
  refine summable_of_ne_finset_zero (s := boxFinset x n ∪ boxFinset w n) fun z hz => ?_
  rw [Finset.mem_union, not_or] at hz
  have h1 : heatKernel d n x z = 0 := by
    by_contra hne; exact hz.1 (mem_boxFinset (heatKernel_support n x hne))
  have h2 : heatKernel d n w z = 0 := by
    by_contra hne; exact hz.2 (mem_boxFinset (heatKernel_support n w hne))
  simp [h1, h2]

/-- **The `ℓ²` size of a time tail, from a single-time `ℓ²` bound.**  If each
time slice `q_j` of a family has `‖q_j‖₂² ≤ B (t+j)^{-5/2}`, then the tail
`∑_j q_j` has `‖∑_j q_j‖₂² ≤ 25 B t^{-1/2}`.  This is the weighted
Cauchy-Schwarz at the weights `a_j = (t+j)^{-5/4}`, whose tail sum is
`≤ 5t^{-1/4}` and which divides the single-time bound back to itself.  The sum
over the lattice is taken in `ℝ≥0∞`, so a family that fails to be square
summable has the value `⊤` and the bound is not satisfied through a junk
value. -/
theorem tsum_sq_tail_l2_le {B : ℝ} (hB : 0 ≤ B) (t : ℕ) (ht : 1 ≤ t)
    (q : ℕ → Site d → ℝ)
    (hsq : ∀ j : ℕ, Summable fun y : Site d => (q j y) ^ 2)
    (hone : ∀ j : ℕ, ∑' y : Site d, (q j y) ^ 2 ≤ B * ((t + j : ℕ) : ℝ) ^ (-(5 : ℝ) / 2))
    (hsg : ∀ y : Site d, Summable fun j => q j y) :
    ∑' y : Site d, ENNReal.ofReal ((∑' j : ℕ, q j y) ^ 2) ≤
      ENNReal.ofReal (25 * B * (t : ℝ) ^ (-(1 : ℝ) / 2)) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  set a : ℕ → ℝ := fun j => ((t + j : ℕ) : ℝ) ^ (-(5 : ℝ) / 4) with ha_def
  have hbpos : ∀ j : ℕ, (0 : ℝ) < ((t + j : ℕ) : ℝ) := by
    intro j
    have : 0 < t + j := by omega
    exact_mod_cast this
  have hapos : ∀ j, 0 < a j := fun j => Real.rpow_pos_of_pos (hbpos j) _
  have hsa : Summable a := summable_tail_rpow t
  have hA : ∑' j, a j ≤ 5 * (t : ℝ) ^ (-(1 : ℝ) / 4) := tsum_tail_rpow_le t ht
  have hAnn : (0 : ℝ) ≤ ∑' j, a j := tsum_nonneg fun j => (hapos j).le
  -- the single-time bound, and its pointwise form at a site
  have hsq_a : ∀ j : ℕ, a j * a j = ((t + j : ℕ) : ℝ) ^ (-(5 : ℝ) / 2) := by
    intro j
    rw [ha_def, ← Real.rpow_add (hbpos j)]
    norm_num
  have hptw : ∀ (y : Site d) (j : ℕ), (q j y) ^ 2 ≤
      B * ((t + j : ℕ) : ℝ) ^ (-(5 : ℝ) / 2) :=
    fun y j => le_trans ((hsq j).le_tsum y fun z _ => sq_nonneg _) (hone j)
  have hdivle : ∀ (y : Site d) (j : ℕ),
      (q j y) ^ 2 / a j ≤ B * a j := by
    intro y j
    rw [div_le_iff₀ (hapos j)]
    have h := hptw y j
    have he : B * a j * a j =
        B * ((t + j : ℕ) : ℝ) ^ (-(5 : ℝ) / 2) := by
      rw [mul_assoc, hsq_a j]
    rw [he]
    exact h
  have hsd : ∀ y : Site d, Summable fun j => (q j y) ^ 2 / a j := by
    intro y
    refine Summable.of_nonneg_of_le (fun j => div_nonneg (sq_nonneg _) (hapos j).le)
      (hdivle y) (hsa.mul_left _)
  have hcs : ∀ y : Site d, (∑' j, q j y) ^ 2 ≤ (∑' j, a j) * ∑' j, (q j y) ^ 2 / a j :=
    fun y => sq_tsum_le_tsum_mul_tsum_div hapos hsa (hsd y) (hsg y)
  -- move to `ℝ≥0∞` and exchange the two sums
  have hstep1 : ∀ y : Site d,
      ENNReal.ofReal ((∑' j, q j y) ^ 2) ≤
        ∑' j : ℕ, ENNReal.ofReal ((∑' j', a j') * ((q j y) ^ 2 / a j)) := by
    intro y
    refine le_trans (ENNReal.ofReal_le_ofReal (hcs y)) ?_
    rw [← (hsd y).tsum_mul_left]
    exact le_of_eq (ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg hAnn (div_nonneg (sq_nonneg _) (hapos j).le))
      ((hsd y).mul_left _))
  have hstep2 : ∀ j : ℕ,
      ∑' y : Site d, ENNReal.ofReal ((∑' j', a j') * ((q j y) ^ 2 / a j)) ≤
        ENNReal.ofReal ((∑' j', a j') * (B * a j)) := by
    intro j
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun y => mul_nonneg hAnn (div_nonneg (sq_nonneg _) (hapos j).le))
      (((hsq j).div_const (a j)).mul_left _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hfac : (fun y : Site d => (∑' j', a j') * ((q j y) ^ 2 / a j)) =
        fun y : Site d => (q j y) ^ 2 * ((∑' j', a j') / a j) := by
      funext y; ring
    rw [hfac, (hsq j).tsum_mul_right]
    have hAq : (0 : ℝ) ≤ (∑' j', a j') / a j := div_nonneg hAnn (hapos j).le
    have hfin : B * ((t + j : ℕ) : ℝ) ^ (-(5 : ℝ) / 2) *
        ((∑' j', a j') / a j) =
        (∑' j', a j') * (B * a j) := by
      rw [← hsq_a j]
      field_simp
    calc (∑' y : Site d, (q j y) ^ 2) * ((∑' j', a j') / a j)
        ≤ B * ((t + j : ℕ) : ℝ) ^ (-(5 : ℝ) / 2) *
            ((∑' j', a j') / a j) := mul_le_mul_of_nonneg_right (hone j) hAq
      _ = (∑' j', a j') * (B * a j) := hfin
  calc ∑' y : Site d, ENNReal.ofReal ((∑' j, q j y) ^ 2)
      ≤ ∑' y : Site d, ∑' j : ℕ, ENNReal.ofReal ((∑' j', a j') * ((q j y) ^ 2 / a j)) :=
        ENNReal.tsum_le_tsum hstep1
    _ = ∑' j : ℕ, ∑' y : Site d, ENNReal.ofReal ((∑' j', a j') * ((q j y) ^ 2 / a j)) :=
        ENNReal.tsum_comm
    _ ≤ ∑' j : ℕ,
          ENNReal.ofReal ((∑' j', a j') * (B * a j)) :=
        ENNReal.tsum_le_tsum hstep2
    _ = ENNReal.ofReal ((∑' j', a j') * (B) *
          ∑' j, a j) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg hAnn (by positivity)) (hsa.mul_left _ |>.mul_left _)]
        congr 1
        rw [← hsa.tsum_mul_left]
        congr 1
        ext j
        ring
    _ ≤ ENNReal.ofReal (25 * B *
          (t : ℝ) ^ (-(1 : ℝ) / 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hsq : (t : ℝ) ^ (-(1 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 4) =
            (t : ℝ) ^ (-(1 : ℝ) / 2) := by
          rw [← Real.rpow_add ht0]; norm_num
        have hu : (0 : ℝ) ≤ (t : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg ht0.le _
        have hAA : (∑' j, a j) * (∑' j, a j) ≤ 25 * (t : ℝ) ^ (-(1 : ℝ) / 2) := by
          nlinarith [hA, hAnn, hu, hsq]
        have hcd : (0 : ℝ) ≤ B := hB
        calc (∑' j', a j') * (B) * ∑' j, a j
            = (B) * ((∑' j, a j) * ∑' j, a j) := by ring
          _ ≤ (B) * (25 * (t : ℝ) ^ (-(1 : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left hAA hcd
          _ = 25 * B * (t : ℝ) ^ (-(1 : ℝ) / 2) := by ring


/-- **The `ℓ²` size of the truncation defect in dimension four**, for two sites
of the same parity: `∑_y (∑_{j≥t}(p_j(x,y) - p_j(w,y)))² ≤ C|x-w| t^{-1/2}`. -/
theorem exists_heatKernel_tail_l2_four (hHK : Sandpile.External.HeatKernelBounds) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 1 ≤ t → ∀ x w : Site 4, Sandpile.External.SameParity x w →
      ∑' y : Site 4, ENNReal.ofReal
          ((∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j) w y)) ^ 2) ≤
        ENNReal.ofReal
          (C * Sandpile.External.latticeDist x w * (t : ℝ) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨C0, hC0, hl2⟩ := exists_heatKernel_increment_l2_four hHK
  refine ⟨25 * C0, by positivity, fun t ht x w hpar => ?_⟩
  have hB : (0 : ℝ) ≤ C0 * Sandpile.External.latticeDist x w :=
    mul_nonneg hC0.le (Real.sqrt_nonneg _)
  have hmain := tsum_sq_tail_l2_le hB t ht
    (fun j y => heatKernel 4 (t + j) x y - heatKernel 4 (t + j) w y)
    (fun j => summable_heatKernel_increment_sq (t + j) x w)
    (fun j => hl2 (t + j) (by omega) x w hpar)
    (fun y => ((summable_heatKernel_transient (d := 4) (by norm_num) x y).comp_injective
      (f := fun k : ℕ => heatKernel 4 k x y) (i := fun j : ℕ => t + j)
      (fun p q hpq => Nat.add_left_cancel hpq)).sub
      ((summable_heatKernel_transient (d := 4) (by norm_num) w y).comp_injective
      (f := fun k : ℕ => heatKernel 4 k w y) (i := fun j : ℕ => t + j)
      (fun p q hpq => Nat.add_left_cancel hpq)))
  refine hmain.trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))

end Sandpile
