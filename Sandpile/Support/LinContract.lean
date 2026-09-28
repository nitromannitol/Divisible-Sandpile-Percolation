import Sandpile.Walk

/-!
# The `ℓ²` contraction of the averaging operator

The averaging operator does not increase the `ℓ²` norm.

`lem:dgt4-linearization-from-survival` uses at `sandpile.tex:5758-5762` the
contraction bound

  "$\sum_{z\in\Z^d}(P^ia_R)(z)^2\leq\sum_{z\in\Z^d}a_R(z)^2$",

which is Cauchy-Schwarz at each site followed by the translation invariance of
the sum: the value of `Pf` at a site is the average of the `2d` neighbouring
values, so its square is at most the average of their squares, and each of the
`2d` shifted copies of `∑_z f(z)^2` is that same sum.
-/

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- Cauchy-Schwarz at one site: the square of the neighbour average is at most
the average of the squares. -/
theorem sq_avg_le (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    (avg f x) ^ 2 ≤ (∑ i : Fin d, ((f (x + unit i)) ^ 2 + (f (x - unit i)) ^ 2)) / (2 * d) := by
  classical
  have hd0 : (0 : ℝ) < 2 * (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  set g : Fin d × Bool → ℝ :=
    fun p => if p.2 then f (x + unit p.1) else f (x - unit p.1) with hg
  have hsum : (∑ i : Fin d, (f (x + unit i) + f (x - unit i))) = ∑ p : Fin d × Bool, g p := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hg]
  have hsq : (∑ i : Fin d, ((f (x + unit i)) ^ 2 + (f (x - unit i)) ^ 2))
      = ∑ p : Fin d × Bool, (g p) ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hg]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d × Bool)) g
    (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul] at hCS
  push_cast at hCS
  simp only [avg, LatticeProb.walkOp, LatticeProb.nbrSum]
  rw [hsum, hsq, div_pow, div_le_div_iff₀ (by positivity) hd0]
  nlinarith [hCS, sq_nonneg (∑ p : Fin d × Bool, g p),
    Finset.sum_nonneg (fun p (_ : p ∈ (Finset.univ : Finset (Fin d × Bool))) => sq_nonneg (g p))]

/-- Translating a field does not change the sum of its squares. -/
theorem tsum_sq_shift (f : Site d → ℝ) (y : Site d) :
    ∑' x : Site d, (f (x + y)) ^ 2 = ∑' x : Site d, (f x) ^ 2 := by
  have h := (Equiv.addRight y).tsum_eq fun z : Site d => (f z) ^ 2
  simpa [Equiv.coe_addRight] using h

/-- Summability of the squares is preserved by translation, transported along
the shift equivalence `Equiv.addRight y`. -/
theorem summable_sq_shift {f : Site d → ℝ} (hf : Summable fun z => (f z) ^ 2) (y : Site d) :
    Summable fun x : Site d => (f (x + y)) ^ 2 := by
  have h := (Equiv.addRight y).summable_iff (f := fun z : Site d => (f z) ^ 2) |>.mpr hf
  have he : ((fun z : Site d => (f z) ^ 2) ∘ fun x : Site d => x + y)
      = fun x : Site d => (f (x + y)) ^ 2 := rfl
  rw [Equiv.coe_addRight, he] at h
  exact h

/-- **The `ℓ²` contraction of the averaging operator**, `sandpile.tex:5755`. -/
theorem summable_sq_avg (hd : 1 ≤ d) {f : Site d → ℝ} (hf : Summable fun z => (f z) ^ 2) :
    Summable fun z => (avg f z) ^ 2 := by
  classical
  have hd0 : (0 : ℝ) < 2 * (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hmaj : Summable fun z : Site d =>
      (∑ i : Fin d, ((f (z + unit i)) ^ 2 + (f (z - unit i)) ^ 2)) / (2 * d) := by
    refine Summable.div_const ?_ _
    refine summable_sum fun i _ => ?_
    exact (summable_sq_shift hf (unit i)).add (by
      simpa [sub_eq_add_neg] using summable_sq_shift hf (-unit i))
  refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => sq_avg_le hd f z) hmaj

/-- **The `ℓ²` contraction of the averaging operator, as a sum inequality**:
`∑ (avg f z)² ≤ ∑ f(z)²`, by comparing term by term to the neighbour-average
majorant of `sq_avg_le` and evaluating that majorant's sum by translation
invariance. -/
theorem tsum_sq_avg_le (hd : 1 ≤ d) {f : Site d → ℝ} (hf : Summable fun z => (f z) ^ 2) :
    ∑' z : Site d, (avg f z) ^ 2 ≤ ∑' z : Site d, (f z) ^ 2 := by
  classical
  have hd0 : (0 : ℝ) < 2 * (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hshift : ∀ i : Fin d,
      (Summable fun x : Site d => (f (x + unit i)) ^ 2) ∧
      (Summable fun x : Site d => (f (x - unit i)) ^ 2) := by
    intro i
    refine ⟨summable_sq_shift hf (unit i), ?_⟩
    simpa [sub_eq_add_neg] using summable_sq_shift hf (-unit i)
  have hmaj : Summable fun z : Site d =>
      (∑ i : Fin d, ((f (z + unit i)) ^ 2 + (f (z - unit i)) ^ 2)) / (2 * d) := by
    refine Summable.div_const ?_ _
    exact summable_sum fun i _ => ((hshift i).1).add ((hshift i).2)
  have hsum : ∑' z : Site d, (∑ i : Fin d, ((f (z + unit i)) ^ 2 + (f (z - unit i)) ^ 2)) / (2 * d)
      = ∑' z : Site d, (f z) ^ 2 := by
    rw [tsum_div_const]
    have hswap : ∑' z : Site d, ∑ i : Fin d, ((f (z + unit i)) ^ 2 + (f (z - unit i)) ^ 2)
        = ∑ i : Fin d, ∑' z : Site d, ((f (z + unit i)) ^ 2 + (f (z - unit i)) ^ 2) :=
      Summable.tsum_finsetSum fun i _ => ((hshift i).1).add ((hshift i).2)
    rw [hswap]
    have hterm : ∀ i : Fin d, ∑' z : Site d, ((f (z + unit i)) ^ 2 + (f (z - unit i)) ^ 2)
        = 2 * ∑' z : Site d, (f z) ^ 2 := by
      intro i
      rw [Summable.tsum_add ((hshift i).1) ((hshift i).2), tsum_sq_shift f (unit i)]
      have : ∑' z : Site d, (f (z - unit i)) ^ 2 = ∑' z : Site d, (f z) ^ 2 := by
        simpa [sub_eq_add_neg] using tsum_sq_shift f (-unit i)
      rw [this]
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  calc ∑' z : Site d, (avg f z) ^ 2
      ≤ ∑' z : Site d, (∑ i : Fin d, ((f (z + unit i)) ^ 2 + (f (z - unit i)) ^ 2)) / (2 * d) :=
        Summable.tsum_le_tsum (fun z => sq_avg_le hd f z) (summable_sq_avg hd hf) hmaj
    _ = ∑' z : Site d, (f z) ^ 2 := hsum

/-- The iterated averaging operator is an `ℓ²` contraction. -/
theorem tsum_sq_avg_iterate_le (hd : 1 ≤ d) {f : Site d → ℝ}
    (hf : Summable fun z => (f z) ^ 2) (n : ℕ) :
    ∑' z : Site d, ((avg^[n] f) z) ^ 2 ≤ ∑' z : Site d, (f z) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsum : ∀ m : ℕ, Summable fun z : Site d => ((avg^[m] f) z) ^ 2 := by
        intro m
        induction m with
        | zero => simpa using hf
        | succ m ihm =>
            rw [Function.iterate_succ_apply']
            exact summable_sq_avg hd ihm
      rw [Function.iterate_succ_apply']
      exact le_trans (tsum_sq_avg_le hd (hsum n)) ih

end Sandpile
