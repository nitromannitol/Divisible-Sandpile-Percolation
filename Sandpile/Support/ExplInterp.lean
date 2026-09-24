/-
The multilinear interpolation from the parabolic mesh `R^{-1}ℤ^d`, and the four
facts about it that Theorem 1.3(i)(b) needs.

The field of Theorem 1.3(i)(b) (`sandpile.tex:217-235`) is the interpolation
from the mesh, not the piecewise-constant embedding `f^{(R)}` of every other
clause; the paper flags the exception just before the theorem.  The definition
lives here rather than beside the theorem because the support chain that proves
the theorem must be able to name it without importing the file that states the
theorem.

The weights `∏_i (fract or 1 - fract)` sum to one over the `2^d` corners, which
is the statement that the interpolation of a constant field is that constant;
the interpolation is linear in the field; and at a mesh point every fractional
part vanishes, so only the corner `ε = 0` survives and the interpolation returns
the value of the field at that mesh point.
-/
import Sandpile.Law
import Sandpile.Continuum.Sobolev

namespace Sandpile.Continuum

variable {d : ℕ}

/-- The multilinear interpolation from the mesh `R^{-1}ℤ^d` of the lattice field
`f`: at `z` it is the multi-affine combination of the values of `f` at the `2^d`
lattice corners of the cell containing `Rz`, with weights the products of the
coordinatewise fractional parts.  At a mesh point `x/R` it returns `f x`.  This
is the field of Theorem 1.3(i)(b); it differs from
`Sandpile.Continuum.embed R f z = f ⌊Rz⌋`, which is the piecewise-constant
embedding `f^{(R)}` used in every other clause, in that it is continuous. -/
noncomputable def multilinearInterp (R : ℝ) (f : Site d → ℝ) (z : Space d) : ℝ :=
  ∑ ε : Fin d → Bool,
    (∏ i : Fin d, if ε i then Int.fract (R * z i) else 1 - Int.fract (R * z i)) *
      f fun i => ⌊R * z i⌋ + if ε i then 1 else 0

/-- The interpolation weights sum to one: the interpolation of a constant field
is that constant. -/
theorem multilinearInterp_const (R : ℝ) (c : ℝ) (z : Space d) :
    multilinearInterp R (fun _ => c) z = c := by
  classical
  unfold multilinearInterp
  rw [← Finset.sum_mul]
  have key : (∑ ε : Fin d → Bool,
      ∏ i : Fin d, if ε i then Int.fract (R * z i) else 1 - Int.fract (R * z i)) = 1 := by
    have hp := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset Bool))
      (fun (i : Fin d) (b : Bool) => if b then Int.fract (R * z i) else 1 - Int.fract (R * z i))
    rw [Fintype.piFinset_univ] at hp
    rw [← hp]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Fintype.sum_bool]
    simp
  rw [key, one_mul]

/-- The interpolation is homogeneous in the field. -/
theorem multilinearInterp_const_mul (R c : ℝ) (f : Site d → ℝ) (z : Space d) :
    multilinearInterp R (fun x => c * f x) z = c * multilinearInterp R f z := by
  unfold multilinearInterp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  ring

/-- The interpolation is additive in the field. -/
theorem multilinearInterp_sub (R : ℝ) (f g : Site d → ℝ) (z : Space d) :
    multilinearInterp R (fun x => f x - g x) z
      = multilinearInterp R f z - multilinearInterp R g z := by
  unfold multilinearInterp
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ε _ => ?_
  ring

/-- At a mesh point the interpolation returns the value of the field there. -/
theorem multilinearInterp_of_fract_eq_zero (R : ℝ) (f : Site d → ℝ) (z : Space d)
    (h : ∀ i, Int.fract (R * z i) = 0) :
    multilinearInterp R f z = f fun i => ⌊R * z i⌋ := by
  classical
  unfold multilinearInterp
  rw [Finset.sum_eq_single (fun _ : Fin d => false)]
  · simp [h]
  · intro ε _ hne
    obtain ⟨i, hi⟩ : ∃ i : Fin d, ε i = true := by
      by_contra hall
      exact hne (funext fun i => by simpa using not_exists.mp hall i)
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) ?_) _
    simp [hi, h i]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- The interpolation weights are nonnegative: each factor is a fractional part or
one minus a fractional part. -/
theorem multilinearInterp_weight_nonneg (R : ℝ) (z : Space d) (ε : Fin d → Bool) :
    0 ≤ ∏ i : Fin d, if ε i then Int.fract (R * z i) else 1 - Int.fract (R * z i) := by
  refine Finset.prod_nonneg fun i _ => ?_
  by_cases h : ε i = true
  · rw [if_pos h]
    exact Int.fract_nonneg _
  · rw [if_neg h]
    have := (Int.fract_lt_one (R * z i)).le
    linarith

/-- The interpolation is bounded by the sup norm of the field: the weights are
nonnegative and sum to one. -/
theorem abs_multilinearInterp_le (R : ℝ) (f : Site d → ℝ) (z : Space d) (M : ℝ)
    (hf : ∀ x, |f x| ≤ M) : |multilinearInterp R f z| ≤ M := by
  have hw := multilinearInterp_weight_nonneg R z
  have hMle : |multilinearInterp R f z| ≤ multilinearInterp R (fun _ => M) z := by
    unfold multilinearInterp
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun ε _ => ?_)
    rw [abs_mul, abs_of_nonneg (hw ε)]
    exact mul_le_mul_of_nonneg_left (hf _) (hw ε)
  rw [multilinearInterp_const] at hMle
  exact hMle

/-- The interpolation at `z` is bounded by the largest value of the field at the `2^d`
corners of the cell containing `Rz`.  This is the local form of the previous bound, and
it is the one the tightness clause of Theorem 1.3(i)(b) needs: it confines the event
`{∃ z ∈ K, M < |𝔪(f)(z)|}` to the lattice box of `K` at scale `R`. -/
theorem abs_multilinearInterp_le_corners (R : ℝ) (f : Site d → ℝ) (z : Space d) (M : ℝ)
    (hf : ∀ ε : Fin d → Bool, |f fun i => ⌊R * z i⌋ + if ε i then 1 else 0| ≤ M) :
    |multilinearInterp R f z| ≤ M := by
  have hw := multilinearInterp_weight_nonneg R z
  have hMle : |multilinearInterp R f z| ≤ multilinearInterp R (fun _ => M) z := by
    unfold multilinearInterp
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun ε _ => ?_)
    rw [abs_mul, abs_of_nonneg (hw ε)]
    exact mul_le_mul_of_nonneg_left (hf ε) (hw ε)
  rw [multilinearInterp_const] at hMle
  exact hMle

end Sandpile.Continuum
