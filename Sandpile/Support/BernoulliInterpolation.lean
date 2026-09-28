import Mathlib

/-!
# Finite Bernoulli product interpolation

Finite Bernoulli product interpolation: coordinate replacement derivatives under one common
product law and the resulting endpoint comparison. `cornerAverage F t` interpolates between
`F (fun _ => false)` at `t = 0` and `F (fun _ => true)` at `t = 1` by averaging `F` over all
Boolean corners against the product Bernoulli weight `cornerWeight`, and its derivative in `t` is
a sum, over coordinates, of `cornerAverage`s of the coordinatewise finite difference of `F`
(`hasDerivAt_cornerAverage`). The main output is a Lindeberg-style replacement bound
(`corner_replacement_bound`, `corner_replacement_bound_pointwise`): if the coordinatewise finite
differences of `F` are controlled at every corner, the fundamental theorem of calculus along this
interpolation bounds the difference between `F`'s two constant corners.
-/

open scoped BigOperators

noncomputable section

namespace Sandpile

/-- The Bernoulli weight at parameter `t`: `t` if `b = true`, `1 - t` if `b = false`. -/
def bernoulliWeight (t : ℝ) (b : Bool) : ℝ := if b then t else 1 - t

/-- The product Bernoulli weight of a corner `s : I → Bool` at parameter `t`,
`∏ i, bernoulliWeight t (s i)`. -/
def cornerWeight {I : Type*} [Fintype I] (t : ℝ) (s : I → Bool) : ℝ :=
  ∏ i, bernoulliWeight t (s i)

/-- The `cornerWeight`-weighted average of `F` over all Boolean corners, at parameter `t`. -/
def cornerAverage {I : Type*} [Fintype I] [DecidableEq I] (F : (I → Bool) → ℝ) (t : ℝ) : ℝ :=
  ∑ s : I → Bool, cornerWeight t s * F s

/-- Inserts the value `b` at coordinate `i` into a Boolean configuration `r` on the complement of
`i`, via `Equiv.funSplitAt`. -/
def booleanInsert {I : Type*} [DecidableEq I] (i : I) (b : Bool)
    (r : {j : I // j ≠ i} → Bool) : I → Bool :=
  (Equiv.funSplitAt i Bool).symm (b, r)

/-- `booleanInsert i b r` takes the value `b` at coordinate `i`. -/
@[simp] lemma booleanInsert_self {I : Type*} [DecidableEq I] (i : I) (b : Bool)
    (r : {j : I // j ≠ i} → Bool) : booleanInsert i b r i = b := by
  simp [booleanInsert, Equiv.funSplitAt, Equiv.piSplitAt]

/-- `booleanInsert i b r` agrees with `r` off the coordinate `i`. -/
@[simp] lemma booleanInsert_other {I : Type*} [DecidableEq I] (i : I) (b : Bool)
    (r : {j : I // j ≠ i} → Bool) (j : {j : I // j ≠ i}) : booleanInsert i b r j = r j := by
  simp [booleanInsert, Equiv.funSplitAt, Equiv.piSplitAt, j.property]

/-- Updating `booleanInsert i b r` at `i` to `c` is the same as inserting `c` directly. -/
@[simp] lemma update_booleanInsert {I : Type*} [DecidableEq I] (i : I) (b c : Bool)
    (r : {j : I // j ≠ i} → Bool) :
    Function.update (booleanInsert i b r) i c = booleanInsert i c r := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simpa [Function.update_of_ne h] using
      (booleanInsert_other i b r ⟨j, h⟩).trans (booleanInsert_other i c r ⟨j, h⟩).symm

/-- The corner weight factors at an inserted coordinate: `cornerWeight t (booleanInsert i b r) =
bernoulliWeight t b * cornerWeight t r`. -/
lemma cornerWeight_insert {I : Type*} [Fintype I] [DecidableEq I]
    (t : ℝ) (i : I) (b : Bool) (r : {j : I // j ≠ i} → Bool) :
    cornerWeight t (booleanInsert i b r) = bernoulliWeight t b * cornerWeight t r := by
  rw [cornerWeight, Fintype.prod_eq_mul_prod_subtype_ne _ i]
  simp only [booleanInsert_self, booleanInsert_other, cornerWeight]

/-- Splitting `cornerAverage F t` into the two values of `F` at a distinguished coordinate `i`,
weighted by `t` and `1 - t` respectively, and averaged over the remaining coordinates. -/
lemma cornerAverage_split {I : Type*} [Fintype I] [DecidableEq I]
    (F : (I → Bool) → ℝ) (t : ℝ) (i : I) :
    cornerAverage F t =
      ∑ r : {j : I // j ≠ i} → Bool, cornerWeight t r *
        (t * F (booleanInsert i true r) + (1 - t) * F (booleanInsert i false r)) := by
  rw [cornerAverage, ← (Equiv.funSplitAt i Bool).symm.sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  change cornerWeight t (booleanInsert i true r) * F (booleanInsert i true r) +
    cornerWeight t (booleanInsert i false r) * F (booleanInsert i false r) = _
  rw [cornerWeight_insert, cornerWeight_insert]
  norm_num [bernoulliWeight]
  ring

/-- The signed sum over corners that computes the `t`-derivative of `cornerWeight` at one
coordinate `i` equals the `cornerAverage` of the coordinate-`i` finite difference of `F`. -/
lemma corner_derivative_identity {I : Type*} [Fintype I] [DecidableEq I]
    (F : (I → Bool) → ℝ) (t : ℝ) (i : I) :
    (∑ s : I → Bool, (∏ j ∈ Finset.univ.erase i, bernoulliWeight t (s j)) *
      (if s i then (1 : ℝ) else -1) * F s) =
      cornerAverage (fun s => F (Function.update s i true) - F (Function.update s i false)) t := by
  rw [← (Equiv.funSplitAt i Bool).symm.sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool, ← Finset.sum_add_distrib, cornerAverage_split _ _ i]
  apply Finset.sum_congr rfl
  intro r _
  have hprod (b : Bool) :
      (∏ j ∈ Finset.univ.erase i, bernoulliWeight t (booleanInsert i b r j)) =
        cornerWeight t r := by
    rw [Finset.prod_subtype (p := fun j : I => j ≠ i) (F := inferInstance) _
      (by simp : ∀ j : I, j ∈ Finset.univ.erase i ↔ j ≠ i)]
    simp only [booleanInsert_other, cornerWeight]
  change (∏ j ∈ Finset.univ.erase i, bernoulliWeight t (booleanInsert i true r j)) *
      (if booleanInsert i true r i then (1 : ℝ) else -1) * F (booleanInsert i true r) +
    (∏ j ∈ Finset.univ.erase i, bernoulliWeight t (booleanInsert i false r j)) *
      (if booleanInsert i false r i then (1 : ℝ) else -1) * F (booleanInsert i false r) = _
  rw [hprod, hprod]
  simp only [booleanInsert_self, update_booleanInsert]
  norm_num
  ring

/-- `bernoulliWeight · b` has derivative `1` at `b = true` and `-1` at `b = false`, independently
of `t`. -/
lemma hasDerivAt_bernoulliWeight (t : ℝ) (b : Bool) :
    HasDerivAt (fun u => bernoulliWeight u b) (if b then (1 : ℝ) else -1) t := by
  cases b
  · change HasDerivAt (fun u : ℝ => 1 - u) (-1) t
    convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) using 1 <;> first | rfl | norm_num
  · exact hasDerivAt_id t

/-- The `t`-derivative of `cornerWeight · s`, by the product rule applied to
`hasDerivAt_bernoulliWeight` at each coordinate. -/
lemma hasDerivAt_cornerWeight {I : Type*} [Fintype I] [DecidableEq I]
    (t : ℝ) (s : I → Bool) :
    HasDerivAt (fun u => cornerWeight u s)
      (∑ i, (∏ j ∈ Finset.univ.erase i, bernoulliWeight t (s j)) *
        (if s i then (1 : ℝ) else -1)) t := by
  simpa only [cornerWeight, smul_eq_mul] using
    HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hasDerivAt_bernoulliWeight t (s i))

/-- The `t`-derivative of `cornerAverage F` is the sum over coordinates of the `cornerAverage` of
the coordinatewise finite difference of `F`, differentiating `cornerWeight` termwise and applying
`corner_derivative_identity`. -/
lemma hasDerivAt_cornerAverage {I : Type*} [Fintype I] [DecidableEq I]
    (F : (I → Bool) → ℝ) (t : ℝ) :
    HasDerivAt (cornerAverage F)
      (∑ i, cornerAverage
        (fun s => F (Function.update s i true) - F (Function.update s i false)) t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun s _ => (hasDerivAt_cornerWeight t s).mul_const (F s))
  have he : (∑ s : I → Bool, (∑ i, (∏ j ∈ Finset.univ.erase i, bernoulliWeight t (s j)) *
      (if s i then (1 : ℝ) else -1)) * F s) =
      ∑ i, cornerAverage
        (fun s => F (Function.update s i true) - F (Function.update s i false)) t := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => corner_derivative_identity F t i)
  rw [he] at h
  convert h using 1 <;> rfl

/-- `cornerWeight t s` is nonnegative for `t ∈ [0, 1]`. -/
lemma cornerWeight_nonneg {I : Type*} [Fintype I] {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (s : I → Bool) : 0 ≤ cornerWeight t s := by
  apply Finset.prod_nonneg
  intro i _
  cases s i <;> simp [bernoulliWeight] <;> linarith [ht.1, ht.2]

/-- The corner weights sum to one for every `t`, since `bernoulliWeight` sums to one over
`Bool` at each coordinate. -/
lemma sum_cornerWeight {I : Type*} [Fintype I] [DecidableEq I] (t : ℝ) :
    ∑ s : I → Bool, cornerWeight t s = 1 := by
  rw [show (∑ s : I → Bool, cornerWeight t s) =
    ∏ i : I, ∑ b : Bool, bernoulliWeight t b from
      (Fintype.prod_sum (fun _ b => bernoulliWeight t b)).symm]
  simp [bernoulliWeight]

/-- `cornerAverage` of a constant function is that constant, since the weights sum to one
(`sum_cornerWeight`). -/
lemma cornerAverage_const {I : Type*} [Fintype I] [DecidableEq I] (a t : ℝ) :
    cornerAverage (fun _ : I → Bool => a) t = a := by
  rw [cornerAverage, ← Finset.sum_mul, sum_cornerWeight, one_mul]

/-- At `t = 0`, the corner weight is `1` at the all-`false` corner and `0` elsewhere. -/
lemma cornerWeight_zero {I : Type*} [Fintype I] [DecidableEq I] (s : I → Bool) :
    cornerWeight 0 s = if s = (fun _ => false) then 1 else 0 := by
  have hw (b : Bool) : bernoulliWeight 0 b = if b = false then 1 else 0 := by
    cases b <;> norm_num [bernoulliWeight]
  simp only [cornerWeight, hw, Finset.prod_boole, Finset.mem_univ, forall_const]
  simp only [funext_iff]

/-- At `t = 1`, the corner weight is `1` at the all-`true` corner and `0` elsewhere. -/
lemma cornerWeight_one {I : Type*} [Fintype I] [DecidableEq I] (s : I → Bool) :
    cornerWeight 1 s = if s = (fun _ => true) then 1 else 0 := by
  have hw (b : Bool) : bernoulliWeight 1 b = if b = true then 1 else 0 := by
    cases b <;> norm_num [bernoulliWeight]
  simp only [cornerWeight, hw, Finset.prod_boole, Finset.mem_univ, forall_const]
  simp only [funext_iff]

/-- At `t = 0`, `cornerAverage F` evaluates `F` at the all-`false` corner. -/
@[simp] lemma cornerAverage_zero {I : Type*} [Fintype I] [DecidableEq I]
    (F : (I → Bool) → ℝ) : cornerAverage F 0 = F (fun _ => false) := by
  simp [cornerAverage, cornerWeight_zero]

/-- At `t = 1`, `cornerAverage F` evaluates `F` at the all-`true` corner. -/
@[simp] lemma cornerAverage_one {I : Type*} [Fintype I] [DecidableEq I]
    (F : (I → Bool) → ℝ) : cornerAverage F 1 = F (fun _ => true) := by
  simp [cornerAverage, cornerWeight_one]

/-- `cornerAverage` is monotone in `F` for `t ∈ [0, 1]`, since the corner weights are
nonnegative. -/
lemma cornerAverage_mono {I : Type*} [Fintype I] [DecidableEq I]
    {F G : (I → Bool) → ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (h : ∀ s, F s ≤ G s) :
    cornerAverage F t ≤ cornerAverage G t := by
  exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h s) (cornerWeight_nonneg ht s))

/-- The triangle inequality for `cornerAverage`: `|cornerAverage F t| ≤ cornerAverage |F| t` for
`t ∈ [0, 1]`. -/
lemma abs_cornerAverage_le {I : Type*} [Fintype I] [DecidableEq I]
    (F : (I → Bool) → ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |cornerAverage F t| ≤ cornerAverage (fun s => |F s|) t := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro s _
  rw [abs_mul, abs_of_nonneg (cornerWeight_nonneg ht s)]

/-- **The corner replacement bound.** If the sum, over coordinates, of the absolute
`cornerAverage` of the coordinatewise finite difference of `F` is bounded by `B` at every
`t ∈ [0, 1]`, then the endpoint difference `F(true,…,true) - F(false,…,false)` is bounded by `B`,
via the mean value inequality applied to the derivative `hasDerivAt_cornerAverage`. -/
lemma corner_replacement_bound {I : Type*} [Fintype I] [DecidableEq I]
    (F : (I → Bool) → ℝ) (B : ℝ)
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∑ i, |cornerAverage
        (fun s => F (Function.update s i true) - F (Function.update s i false)) t| ≤ B) :
    |F (fun _ => true) - F (fun _ => false)| ≤ B := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hasDerivAt_cornerAverage F t).hasDerivWithinAt)
    (fun t ht => (by
      rw [Real.norm_eq_abs]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (hB t ⟨ht.1, ht.2.le⟩)))
  simpa only [Real.norm_eq_abs, cornerAverage_one, cornerAverage_zero] using h


/-- `cornerAverage` commutes with a finite sum over an auxiliary index `j`. -/
lemma cornerAverage_sum {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (F : J → (I → Bool) → ℝ) (t : ℝ) :
    cornerAverage (fun s => ∑ j, F j s) t = ∑ j, cornerAverage (F j) t := by
  simp only [cornerAverage, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The pointwise form of `corner_replacement_bound`: if the sum of the absolute coordinatewise
finite differences of `F` is bounded by `B` at every corner `s`, then the endpoint difference is
bounded by `B`. -/
lemma corner_replacement_bound_pointwise {I : Type*} [Fintype I] [DecidableEq I]
    (F : (I → Bool) → ℝ) (B : ℝ)
    (hB : ∀ s, ∑ i, |F (Function.update s i true) - F (Function.update s i false)| ≤ B) :
    |F (fun _ => true) - F (fun _ => false)| ≤ B := by
  apply corner_replacement_bound F B
  intro t ht
  calc
    _ ≤ ∑ i, cornerAverage
          (fun s => |F (Function.update s i true) - F (Function.update s i false)|) t :=
      Finset.sum_le_sum (fun i _ => abs_cornerAverage_le _ ht)
    _ = cornerAverage
          (fun s => ∑ i, |F (Function.update s i true) - F (Function.update s i false)|) t :=
      (cornerAverage_sum _ _).symm
    _ ≤ cornerAverage (fun _ => B) t := cornerAverage_mono ht hB
    _ = B := cornerAverage_const _ _

end Sandpile
