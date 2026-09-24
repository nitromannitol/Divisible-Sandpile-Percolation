/-
The multilinear interpolation is Lipschitz in each space variable.

`ContInterpLip` proves the one-dimensional statement, that the piecewise-linear
interpolation from the integer mesh of a family of reals bounded by `M` is
`2M`-Lipschitz, and reads the time direction of `linInterp` off it.  This module
does the space direction.

Fix a coordinate `j`.  The `2^d` Boolean corners of the spatial cell split into
`2^{d-1}` pairs differing only in their `j`-th entry, and the multilinear weight
of a corner factors as the `j`-th weight times the product over the other
coordinates.  Summing the pair with the `j`-th weights `1 - t_j` and `t_j`
therefore writes `linInterp` at `(r,w)` as a convex combination, over the
corners of the other `d-1` coordinates, of one-dimensional interpolations in
`R w_j`.  Since the one-dimensional interpolation is linear in its family of
mesh values, the combination is itself a single one-dimensional interpolation,
of the family `sliceInterp`, whose values are convex combinations of mesh values
and so obey the same bound `M`.  The Lipschitz bound of `ContInterpLip` applies
to it verbatim.

Changing the coordinates one at a time then gives the bound for an arbitrary
pair of points, with the constant `2M` and the `ℓ¹` distance of the rescaled
coordinates.
-/
import Sandpile.Support.ContInterpLip
import LatticeProb.Support.ContSums

open LatticeProb

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Frozen.HeatPotentialInvariance

/-- The value of the interpolation in the time variable at one corner of the
spatial cell: the affine combination of the mesh values at the two times
bracketing `R²r`. -/
noncomputable def cellValue (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (a : ℕ) (s : ℝ)
    (z : Site d) : ℝ :=
  (1 - s) * meshValue d R ζ a z + s * meshValue d R ζ (a + 1) z

/-- The family of mesh values whose one-dimensional interpolation in the `j`-th
coordinate is `linInterp`: the convex combination, over the corners of the other
`d-1` coordinates, of the time-interpolated mesh values at the site whose `j`-th
coordinate is `n`.  Neither `t j` nor `b j` occurs. -/
noncomputable def sliceInterp (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (a : ℕ) (s : ℝ)
    (t : Fin d → ℝ) (b : Site d) (j : Fin d) (n : ℤ) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
    (∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
      cellValue d R ζ a s (fun i => if i = j then n else b i + (if c i then 1 else 0))

/-- The weights of the other coordinates are nonnegative. -/
theorem prod_ite_erase_nonneg {d : ℕ} {t : Fin d → ℝ} (ht0 : ∀ i, 0 ≤ t i)
    (ht1 : ∀ i, t i ≤ 1) (j : Fin d) (c : Fin d → Bool) :
    0 ≤ ∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i) := by
  refine Finset.prod_nonneg fun i _ => ?_
  by_cases h : c i
  · rw [if_pos h]
    exact ht0 i
  · rw [if_neg h]
    linarith [ht1 i]

/-- The time interpolation at one corner is a convex combination of two mesh
values, so it obeys their bound. -/
theorem abs_cellValue_le (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (M : ℝ)
    (hM : ∀ (k : ℕ) (z : Site d), |meshValue d R ζ k z| ≤ M)
    (a : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (z : Site d) :
    |cellValue d R ζ a s z| ≤ M := by
  have h1 := hM a z
  have h2 := hM (a + 1) z
  rw [cellValue]
  calc |(1 - s) * meshValue d R ζ a z + s * meshValue d R ζ (a + 1) z|
      ≤ |(1 - s) * meshValue d R ζ a z| + |s * meshValue d R ζ (a + 1) z| := abs_add_le _ _
    _ = (1 - s) * |meshValue d R ζ a z| + s * |meshValue d R ζ (a + 1) z| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
    _ ≤ M := by nlinarith [h1, h2]

/-- The family interpolated in the `j`-th coordinate obeys the bound on the mesh
values, being a convex combination of them. -/
theorem abs_sliceInterp_le (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (M : ℝ)
    (hM : ∀ (k : ℕ) (z : Site d), |meshValue d R ζ k z| ≤ M)
    (a : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {t : Fin d → ℝ}
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) (b : Site d) (j : Fin d) (n : ℤ) :
    |sliceInterp d R ζ a s t b j n| ≤ M := by
  classical
  rw [sliceInterp]
  calc |∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
        (∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
          cellValue d R ζ a s (fun i => if i = j then n else b i + (if c i then 1 else 0))|
      ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
          |(∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
            cellValue d R ζ a s (fun i => if i = j then n else b i + (if c i then 1 else 0))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
          (∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) * M := by
        refine Finset.sum_le_sum fun c _ => ?_
        have hw := prod_ite_erase_nonneg ht0 ht1 j c
        rw [abs_mul, abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_left
          (abs_cellValue_le d R ζ M hM a hs0 hs1 _) hw
    _ = M := by rw [← Finset.sum_mul, sum_filter_prod_ite_erase t j, one_mul]

/-- **The interpolated field, read as a one-dimensional interpolation in one
space coordinate.**  Pairing the Boolean corners on their `j`-th entry and
factoring the multilinear weight there turns `linInterp` into the piecewise
linear interpolation of `sliceInterp` at `R w_j`. -/
theorem linInterp_eq_interp1_slice (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (r : ℝ)
    (w : Sandpile.Continuum.Space d) (j : Fin d) :
    linInterp d R ζ r w
      = interp1 (sliceInterp d R ζ ⌊R ^ 2 * r⌋₊ (R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ))
          (fun i => R * w i - ((⌊R * w i⌋ : ℤ) : ℝ)) (fun i => ⌊R * w i⌋) j) (R * w j) := by
  classical
  set a : ℕ := ⌊R ^ 2 * r⌋₊ with ha
  set s : ℝ := R ^ 2 * r - ((a : ℕ) : ℝ) with hs
  set b : Site d := fun i => ⌊R * w i⌋ with hb
  set t : Fin d → ℝ := fun i => R * w i - ((b i : ℤ) : ℝ) with ht
  have hfl : ⌊R * w j⌋ = b j := rfl
  have hfract : Int.fract (R * w j) = t j := by rw [Int.fract]
  have hL : linInterp d R ζ r w
      = ∑ ε : Fin d → Bool, (∏ i : Fin d, if ε i then t i else 1 - t i) *
          cellValue d R ζ a s (fun i => b i + if ε i then 1 else 0) := rfl
  have hR : interp1 (sliceInterp d R ζ a s t b j) (R * w j)
      = ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
          ((1 - t j) * ((∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
              cellValue d R ζ a s
                (fun i => if i = j then (b j : ℤ) else b i + (if c i then 1 else 0)))
            + t j * ((∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
              cellValue d R ζ a s
                (fun i => if i = j then (b j : ℤ) + 1 else b i + (if c i then 1 else 0)))) := by
    rw [interp1, hfract, hfl, sliceInterp, sliceInterp, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
  rw [hL, hR, sum_pi_bool_split j]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hcj : c j = false := (Finset.mem_filter.mp hc).2
  rw [prod_ite_erase_false t j c hcj, prod_ite_erase_true t j c]
  have h1 : (fun i => b i + if c i then (1:ℤ) else 0)
      = (fun i => if i = j then (b j : ℤ) else b i + (if c i then 1 else 0)) := by
    funext i
    by_cases h : i = j
    · subst h
      simp [hcj]
    · rw [if_neg h]
  have h2 : (fun i => b i + if (Function.update c j true) i then (1:ℤ) else 0)
      = (fun i => if i = j then (b j : ℤ) + 1 else b i + (if c i then 1 else 0)) := by
    funext i
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg h, Function.update_of_ne h]
  rw [h1, h2]
  ring

/-- The interpolated family does not see the `j`-th coordinate of the point. -/
theorem sliceInterp_congr (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (a : ℕ) (s : ℝ)
    {t t' : Fin d → ℝ} {b b' : Site d} (j : Fin d)
    (hts : ∀ i, i ≠ j → t i = t' i) (hbs : ∀ i, i ≠ j → b i = b' i) (n : ℤ) :
    sliceInterp d R ζ a s t b j n = sliceInterp d R ζ a s t' b' j n := by
  classical
  rw [sliceInterp, sliceInterp]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hw : (∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i))
      = ∏ i ∈ Finset.univ.erase j, (if c i then t' i else 1 - t' i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hts i (Finset.ne_of_mem_erase hi)]
  have hz : (fun i => if i = j then n else b i + (if c i then (1:ℤ) else 0))
      = (fun i => if i = j then n else b' i + (if c i then (1:ℤ) else 0)) := by
    funext i
    by_cases h : i = j
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, hbs i h]
  rw [hw, hz]

/-- **The interpolated field is Lipschitz in one space coordinate**, with
constant twice the bound on the mesh values. -/
theorem abs_linInterp_sub_coord_le (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (M : ℝ)
    (hM : ∀ (k : ℕ) (z : Site d), |meshValue d R ζ k z| ≤ M)
    {r : ℝ} (hr : 0 ≤ r) (w w' : Sandpile.Continuum.Space d) (j : Fin d)
    (hagree : ∀ i, i ≠ j → w i = w' i) :
    |linInterp d R ζ r w - linInterp d R ζ r w'| ≤ 2 * M * |R * w j - R * w' j| := by
  classical
  have hr2 : (0:ℝ) ≤ R ^ 2 * r := mul_nonneg (sq_nonneg R) hr
  have hs0 : (0:ℝ) ≤ R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) := by
    have := Nat.floor_le hr2
    linarith
  have hs1 : R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) ≤ 1 := by
    have := Nat.lt_floor_add_one (R ^ 2 * r)
    linarith
  have hFeq : sliceInterp d R ζ ⌊R ^ 2 * r⌋₊
        (R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ))
        (fun i => R * w' i - ((⌊R * w' i⌋ : ℤ) : ℝ)) (fun i => ⌊R * w' i⌋) j
      = sliceInterp d R ζ ⌊R ^ 2 * r⌋₊
        (R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ))
        (fun i => R * w i - ((⌊R * w i⌋ : ℤ) : ℝ)) (fun i => ⌊R * w i⌋) j := by
    funext n
    refine sliceInterp_congr d R ζ _ _ j ?_ ?_ n
    · intro i hi
      rw [hagree i hi]
    · intro i hi
      rw [hagree i hi]
  rw [linInterp_eq_interp1_slice d R ζ r w j, linInterp_eq_interp1_slice d R ζ r w' j, hFeq]
  refine abs_interp1_sub_le _ M ?_ (R * w j) (R * w' j)
  intro n
  exact abs_sliceInterp_le d R ζ M hM _ hs0 hs1
    (fun i => (fract_mem (R * w i)).1) (fun i => (fract_mem (R * w i)).2) _ j n

/-- The point that agrees with `w'` in the first `m` coordinates and with `w`
in the rest.  It interpolates between `w` at `m = 0` and `w'` at `m = d`, one
coordinate at a time. -/
noncomputable def hybridPoint {d : ℕ} (w w' : Sandpile.Continuum.Space d) (m : ℕ) :
    Sandpile.Continuum.Space d :=
  WithLp.toLp 2 (fun i : Fin d => if (i : ℕ) < m then w' i else w i)

/-- The coordinates of the interpolating point. -/
theorem hybridPoint_apply {d : ℕ} (w w' : Sandpile.Continuum.Space d) (m : ℕ) (i : Fin d) :
    hybridPoint w w' m i = if (i : ℕ) < m then w' i else w i := rfl

/-- At `m = 0` the interpolating point is the first point. -/
theorem hybridPoint_zero {d : ℕ} (w w' : Sandpile.Continuum.Space d) :
    hybridPoint w w' 0 = w := by
  ext i
  rw [hybridPoint_apply]
  simp

/-- At `m = d` the interpolating point is the second point. -/
theorem hybridPoint_dim {d : ℕ} (w w' : Sandpile.Continuum.Space d) :
    hybridPoint w w' d = w' := by
  ext i
  rw [hybridPoint_apply, if_pos i.isLt]

/-- Consecutive interpolating points differ in one coordinate only. -/
theorem hybridPoint_agree {d : ℕ} (w w' : Sandpile.Continuum.Space d) {m : ℕ} (hm : m < d)
    (i : Fin d) (hi : i ≠ (⟨m, hm⟩ : Fin d)) :
    hybridPoint w w' m i = hybridPoint w w' (m + 1) i := by
  have hne : (i : ℕ) ≠ m := by
    intro h
    exact hi (Fin.ext h)
  rw [hybridPoint_apply, hybridPoint_apply]
  by_cases hlt : (i : ℕ) < m
  · rw [if_pos hlt, if_pos (by omega)]
  · rw [if_neg hlt, if_neg (by omega)]

/-- The bound along the chain of interpolating points, by induction on the number
of coordinates already changed. -/
theorem abs_linInterp_sub_hybrid_le (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (M : ℝ)
    (hM : ∀ (k : ℕ) (z : Site d), |meshValue d R ζ k z| ≤ M)
    {r : ℝ} (hr : 0 ≤ r) (w w' : Sandpile.Continuum.Space d) :
    ∀ m : ℕ, m ≤ d →
      |linInterp d R ζ r w - linInterp d R ζ r (hybridPoint w w' m)|
        ≤ 2 * M * ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m),
            |R * w i - R * w' i| := by
  classical
  intro m
  induction m with
  | zero =>
      intro _
      rw [hybridPoint_zero, sub_self, abs_zero]
      have hfilt : Finset.univ.filter (fun i : Fin d => (i : ℕ) < 0) = (∅ : Finset (Fin d)) := by
        ext i
        simp
      rw [hfilt, Finset.sum_empty, mul_zero]
  | succ m ih =>
      intro hm
      have hm' : m < d := by omega
      have h1 := ih (by omega)
      have h2 := abs_linInterp_sub_coord_le d R ζ M hM (r := r) hr
        (hybridPoint w w' m) (hybridPoint w w' (m + 1)) (⟨m, hm'⟩ : Fin d)
        (fun i hi => hybridPoint_agree w w' hm' i hi)
      have hva : hybridPoint w w' m (⟨m, hm'⟩ : Fin d) = w (⟨m, hm'⟩ : Fin d) := by
        rw [hybridPoint_apply]
        simp
      have hvb : hybridPoint w w' (m + 1) (⟨m, hm'⟩ : Fin d) = w' (⟨m, hm'⟩ : Fin d) := by
        rw [hybridPoint_apply]
        simp
      rw [hva, hvb] at h2
      have hnot : (⟨m, hm'⟩ : Fin d) ∉ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m) := by
        simp
      have hfilt : Finset.univ.filter (fun i : Fin d => (i : ℕ) < m + 1)
          = insert (⟨m, hm'⟩ : Fin d) (Finset.univ.filter (fun i : Fin d => (i : ℕ) < m)) := by
        ext i
        simp [Fin.ext_iff]
        omega
      rw [hfilt, Finset.sum_insert hnot]
      calc |linInterp d R ζ r w - linInterp d R ζ r (hybridPoint w w' (m + 1))|
          ≤ |linInterp d R ζ r w - linInterp d R ζ r (hybridPoint w w' m)|
            + |linInterp d R ζ r (hybridPoint w w' m)
                - linInterp d R ζ r (hybridPoint w w' (m + 1))| := abs_sub_le _ _ _
        _ ≤ 2 * M * ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m),
                |R * w i - R * w' i|
              + 2 * M * |R * w (⟨m, hm'⟩ : Fin d) - R * w' (⟨m, hm'⟩ : Fin d)| :=
            add_le_add h1 h2
        _ = 2 * M * (|R * w (⟨m, hm'⟩ : Fin d) - R * w' (⟨m, hm'⟩ : Fin d)|
              + ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m),
                |R * w i - R * w' i|) := by ring

/-- **The interpolated field is Lipschitz in the space variable**, with constant
twice the bound on the mesh values and the `ℓ¹` distance of the rescaled
coordinates.  Together with `abs_linInterp_sub_time_le` this is the modulus of
continuity of the interpolant at every scale `R ≥ 1`, which the small scales of
the tightness clause need. -/
theorem abs_linInterp_sub_space_le (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (M : ℝ)
    (hM : ∀ (k : ℕ) (z : Site d), |meshValue d R ζ k z| ≤ M)
    {r : ℝ} (hr : 0 ≤ r) (w w' : Sandpile.Continuum.Space d) :
    |linInterp d R ζ r w - linInterp d R ζ r w'|
      ≤ 2 * M * ∑ i : Fin d, |R * w i - R * w' i| := by
  classical
  have h := abs_linInterp_sub_hybrid_le d R ζ M hM (r := r) hr w w' d le_rfl
  rw [hybridPoint_dim] at h
  have hfilt : Finset.univ.filter (fun i : Fin d => (i : ℕ) < d) = (Finset.univ : Finset (Fin d)) := by
    ext i
    simp
  rw [hfilt] at h
  exact h

/-- **The modulus of continuity of the interpolated field.**  The time and the
space directions together: the interpolant is Lipschitz on the parabolic mesh
scale, with constant twice the bound on the mesh values.  This is the estimate
the small scales of the tightness clause of
`prop:dlt4-heat-potential-invariance` need, where comparing two points through
the corners of their cells is not enough because the mesh diameter is not small
at `R` close to one. -/
theorem abs_linInterp_sub_le' (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (M : ℝ)
    (hM : ∀ (k : ℕ) (z : Site d), |meshValue d R ζ k z| ≤ M)
    {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (w w' : Sandpile.Continuum.Space d) :
    |linInterp d R ζ r w - linInterp d R ζ r' w'|
      ≤ 2 * M * |R ^ 2 * r - R ^ 2 * r'| + 2 * M * ∑ i : Fin d, |R * w i - R * w' i| := by
  have h1 := abs_linInterp_sub_time_le d R ζ M hM hr hr' w
  have h2 := abs_linInterp_sub_space_le d R ζ M hM (r := r') hr' w w'
  calc |linInterp d R ζ r w - linInterp d R ζ r' w'|
      ≤ |linInterp d R ζ r w - linInterp d R ζ r' w|
        + |linInterp d R ζ r' w - linInterp d R ζ r' w'| := abs_sub_le _ _ _
    _ ≤ 2 * M * |R ^ 2 * r - R ^ 2 * r'|
        + 2 * M * ∑ i : Fin d, |R * w i - R * w' i| := add_le_add h1 h2

/-- The modulus in the metric of the product `ℝ × ℝ^d`: the interpolant is
Lipschitz on the parabolic mesh scale, with constant `2M(R² + |R|d)`. -/
theorem abs_linInterp_sub_le_dist (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (M : ℝ)
    (hM : ∀ (k : ℕ) (z : Site d), |meshValue d R ζ k z| ≤ M)
    {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (w w' : Sandpile.Continuum.Space d) :
    |linInterp d R ζ r w - linInterp d R ζ r' w'|
      ≤ 2 * M * (R ^ 2 + |R| * (d : ℝ)) * dist (r, w) (r', w') := by
  classical
  have hM0 : (0:ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0 (fun _ => 0))
  set D : ℝ := dist ((r, w) : ℝ × Sandpile.Continuum.Space d) (r', w') with hD
  have hD0 : (0:ℝ) ≤ D := dist_nonneg
  have htime : dist r r' ≤ D := by
    rw [hD, Prod.dist_eq]
    exact le_max_left _ _
  have hspace : dist w w' ≤ D := by
    rw [hD, Prod.dist_eq]
    exact le_max_right _ _
  have h1 : |R ^ 2 * r - R ^ 2 * r'| ≤ R ^ 2 * D := by
    have hfac : R ^ 2 * r - R ^ 2 * r' = R ^ 2 * (r - r') := by ring
    rw [hfac, abs_mul, abs_of_nonneg (sq_nonneg R)]
    have : |r - r'| ≤ D := by rw [← Real.dist_eq]; exact htime
    nlinarith [sq_nonneg R, this]
  have h2 : ∀ i : Fin d, |R * w i - R * w' i| ≤ |R| * D := by
    intro i
    have hfac : R * w i - R * w' i = R * (w i - w' i) := by ring
    have hco : |w i - w' i| ≤ D := by
      have := PiLp.dist_apply_le w w' i
      rw [Real.dist_eq] at this
      linarith [hspace]
    rw [hfac, abs_mul]
    have hR0 : (0:ℝ) ≤ |R| := abs_nonneg R
    nlinarith [hco, hR0]
  have h3 : ∑ i : Fin d, |R * w i - R * w' i| ≤ (d : ℝ) * (|R| * D) := by
    calc ∑ i : Fin d, |R * w i - R * w' i|
        ≤ ∑ _i : Fin d, |R| * D := Finset.sum_le_sum fun i _ => h2 i
      _ = (d : ℝ) * (|R| * D) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h := abs_linInterp_sub_le' d R ζ M hM hr hr' w w'
  nlinarith [h, h1, h3, hM0, hD0]

/-- **The interpolated field is continuous on the closed half-space of
nonnegative times.**  This is the path continuity the quantitative Kolmogorov
criterion asks of the process it is applied to; here it is not an assumption but
a consequence of the modulus, and it holds for every sample of the scenery. -/
theorem continuousOn_linInterp (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (M : ℝ)
    (hM : ∀ (k : ℕ) (z : Site d), |meshValue d R ζ k z| ≤ M) :
    ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => linInterp d R ζ p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) := by
  classical
  have hM0 : (0:ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0 (fun _ => 0))
  set L : ℝ := 2 * M * (R ^ 2 + |R| * (d : ℝ)) with hL
  have hL0 : (0:ℝ) ≤ L := by
    rw [hL]
    positivity
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  refine ⟨ε / (L + 1), by positivity, ?_⟩
  intro a ha hab
  have hb0 : (0:ℝ) ≤ b.1 := (Set.mem_prod.mp hb).1
  have ha0 : (0:ℝ) ≤ a.1 := (Set.mem_prod.mp ha).1
  have hbound := abs_linInterp_sub_le_dist d R ζ M hM ha0 hb0 a.2 b.2
  have hlt : L * dist a b < ε := by
    have h1 : L * dist a b ≤ L * (ε / (L + 1)) :=
      mul_le_mul_of_nonneg_left hab.le hL0
    have h2 : L * (ε / (L + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith : (0:ℝ) < L + 1)]
      nlinarith [hε, hL0]
    linarith
  rw [Real.dist_eq]
  calc |linInterp d R ζ a.1 a.2 - linInterp d R ζ b.1 b.2|
      ≤ L * dist a b := hbound
    _ < ε := hlt

/-- The time interpolation at one corner moves by at most the largest mesh
increment when the site does. -/
theorem abs_cellValue_sub_le (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (K : ℝ) (a : ℕ)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z z' : Site d}
    (h0 : |meshValue d R ζ a z' - meshValue d R ζ a z| ≤ K)
    (h1 : |meshValue d R ζ (a + 1) z' - meshValue d R ζ (a + 1) z| ≤ K) :
    |cellValue d R ζ a s z' - cellValue d R ζ a s z| ≤ K := by
  rw [cellValue, cellValue]
  have hsplit : (1 - s) * meshValue d R ζ a z' + s * meshValue d R ζ (a + 1) z'
      - ((1 - s) * meshValue d R ζ a z + s * meshValue d R ζ (a + 1) z)
      = (1 - s) * (meshValue d R ζ a z' - meshValue d R ζ a z)
        + s * (meshValue d R ζ (a + 1) z' - meshValue d R ζ (a + 1) z) := by ring
  rw [hsplit]
  calc |(1 - s) * (meshValue d R ζ a z' - meshValue d R ζ a z)
        + s * (meshValue d R ζ (a + 1) z' - meshValue d R ζ (a + 1) z)|
      ≤ |(1 - s) * (meshValue d R ζ a z' - meshValue d R ζ a z)|
        + |s * (meshValue d R ζ (a + 1) z' - meshValue d R ζ (a + 1) z)| := abs_add_le _ _
    _ = (1 - s) * |meshValue d R ζ a z' - meshValue d R ζ a z|
        + s * |meshValue d R ζ (a + 1) z' - meshValue d R ζ (a + 1) z| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
    _ ≤ K := by nlinarith [h0, h1]

/-- The interpolated family moves by at most the largest mesh increment when its
index does, being a convex combination of the increments of the mesh values. -/
theorem abs_sliceInterp_succ_sub (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (K : ℝ)
    (hK : ∀ (k : ℕ) (z : Site d) (i : Fin d),
      |meshValue d R ζ k (Function.update z i (z i + 1)) - meshValue d R ζ k z| ≤ K)
    (a : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {t : Fin d → ℝ}
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) (b : Site d) (j : Fin d) (n : ℤ) :
    |sliceInterp d R ζ a s t b j (n + 1) - sliceInterp d R ζ a s t b j n| ≤ K := by
  classical
  have hK0 : (0:ℝ) ≤ K := le_trans (abs_nonneg _) (hK a b j)
  rw [sliceInterp, sliceInterp, ← Finset.sum_sub_distrib]
  calc |∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
        ((∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
            cellValue d R ζ a s (fun i => if i = j then n + 1 else b i + (if c i then 1 else 0))
          - (∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
            cellValue d R ζ a s (fun i => if i = j then n else b i + (if c i then 1 else 0)))|
      ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
          |(∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
              cellValue d R ζ a s (fun i => if i = j then n + 1 else b i + (if c i then 1 else 0))
            - (∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
              cellValue d R ζ a s (fun i => if i = j then n else b i + (if c i then 1 else 0))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
          (∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) * K := by
        refine Finset.sum_le_sum fun c _ => ?_
        have hw := prod_ite_erase_nonneg ht0 ht1 j c
        rw [← mul_sub, abs_mul, abs_of_nonneg hw]
        refine mul_le_mul_of_nonneg_left ?_ hw
        have hupd : (fun i => if i = j then n + 1 else b i + (if c i then (1:ℤ) else 0))
            = Function.update
                (fun i => if i = j then n else b i + (if c i then (1:ℤ) else 0)) j
                ((fun i => if i = j then n else b i + (if c i then (1:ℤ) else 0)) j + 1) := by
          funext i
          by_cases h : i = j
          · subst h
            simp
          · rw [if_neg h, Function.update_of_ne h, if_neg h]
        rw [hupd]
        exact abs_cellValue_sub_le d R ζ K a hs0 hs1
          (hK a (fun i => if i = j then n else b i + (if c i then (1:ℤ) else 0)) j)
          (hK (a + 1) (fun i => if i = j then n else b i + (if c i then (1:ℤ) else 0)) j)
    _ = K := by rw [← Finset.sum_mul, sum_filter_prod_ite_erase t j, one_mul]

/-- **The interpolated field moves in one space coordinate by at most the largest
mesh increment times the displacement.**  This is the form the small scales of
the tightness clause need: at separations below the mesh spacing the quantity
that is small is the increment of the mesh values, not their size. -/
theorem abs_linInterp_sub_coord_le_incr (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (K : ℝ)
    (hK : ∀ (k : ℕ) (z : Site d) (i : Fin d),
      |meshValue d R ζ k (Function.update z i (z i + 1)) - meshValue d R ζ k z| ≤ K)
    {r : ℝ} (hr : 0 ≤ r) (w w' : Sandpile.Continuum.Space d) (j : Fin d)
    (hagree : ∀ i, i ≠ j → w i = w' i) :
    |linInterp d R ζ r w - linInterp d R ζ r w'| ≤ K * |R * w j - R * w' j| := by
  classical
  have hr2 : (0:ℝ) ≤ R ^ 2 * r := mul_nonneg (sq_nonneg R) hr
  have hs0 : (0:ℝ) ≤ R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) := by
    have := Nat.floor_le hr2
    linarith
  have hs1 : R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) ≤ 1 := by
    have := Nat.lt_floor_add_one (R ^ 2 * r)
    linarith
  have hFeq : sliceInterp d R ζ ⌊R ^ 2 * r⌋₊
        (R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ))
        (fun i => R * w' i - ((⌊R * w' i⌋ : ℤ) : ℝ)) (fun i => ⌊R * w' i⌋) j
      = sliceInterp d R ζ ⌊R ^ 2 * r⌋₊
        (R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ))
        (fun i => R * w i - ((⌊R * w i⌋ : ℤ) : ℝ)) (fun i => ⌊R * w i⌋) j := by
    funext n
    refine sliceInterp_congr d R ζ _ _ j ?_ ?_ n
    · intro i hi
      rw [hagree i hi]
    · intro i hi
      rw [hagree i hi]
  rw [linInterp_eq_interp1_slice d R ζ r w j, linInterp_eq_interp1_slice d R ζ r w' j, hFeq]
  refine abs_interp1_sub_le_incr _ K ?_ (R * w j) (R * w' j)
  intro n
  exact abs_sliceInterp_succ_sub d R ζ K hK _ hs0 hs1
    (fun i => (fract_mem (R * w i)).1) (fun i => (fract_mem (R * w i)).2) _ j n

/-- **Changing the coordinates one at a time**, from any bound on the increment
in a single coordinate.  `abs_linInterp_sub_space_le` is the case `c = 2M` and
`abs_linInterp_sub_space_le_incr` the case `c = K`. -/
theorem abs_linInterp_sub_space_le_of_coord (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) {c r : ℝ}
    (hstep : ∀ (u v : Sandpile.Continuum.Space d) (j : Fin d),
      (∀ i, i ≠ j → u i = v i) →
      |linInterp d R ζ r u - linInterp d R ζ r v| ≤ c * |R * u j - R * v j|)
    (w w' : Sandpile.Continuum.Space d) :
    |linInterp d R ζ r w - linInterp d R ζ r w'|
      ≤ c * ∑ i : Fin d, |R * w i - R * w' i| := by
  classical
  have key : ∀ m : ℕ, m ≤ d →
      |linInterp d R ζ r w - linInterp d R ζ r (hybridPoint w w' m)|
        ≤ c * ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m),
            |R * w i - R * w' i| := by
    intro m
    induction m with
    | zero =>
        intro _
        rw [hybridPoint_zero, sub_self, abs_zero]
        have hfilt : Finset.univ.filter (fun i : Fin d => (i : ℕ) < 0) = (∅ : Finset (Fin d)) := by
          ext i
          simp
        rw [hfilt, Finset.sum_empty, mul_zero]
    | succ m ih =>
        intro hm
        have hm' : m < d := by omega
        have h1 := ih (by omega)
        have h2 := hstep (hybridPoint w w' m) (hybridPoint w w' (m + 1)) (⟨m, hm'⟩ : Fin d)
          (fun i hi => hybridPoint_agree w w' hm' i hi)
        have hva : hybridPoint w w' m (⟨m, hm'⟩ : Fin d) = w (⟨m, hm'⟩ : Fin d) := by
          rw [hybridPoint_apply]
          simp
        have hvb : hybridPoint w w' (m + 1) (⟨m, hm'⟩ : Fin d) = w' (⟨m, hm'⟩ : Fin d) := by
          rw [hybridPoint_apply]
          simp
        rw [hva, hvb] at h2
        have hnot : (⟨m, hm'⟩ : Fin d) ∉ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m) := by
          simp
        have hfilt : Finset.univ.filter (fun i : Fin d => (i : ℕ) < m + 1)
            = insert (⟨m, hm'⟩ : Fin d) (Finset.univ.filter (fun i : Fin d => (i : ℕ) < m)) := by
          ext i
          simp [Fin.ext_iff]
          omega
        rw [hfilt, Finset.sum_insert hnot]
        calc |linInterp d R ζ r w - linInterp d R ζ r (hybridPoint w w' (m + 1))|
            ≤ |linInterp d R ζ r w - linInterp d R ζ r (hybridPoint w w' m)|
              + |linInterp d R ζ r (hybridPoint w w' m)
                  - linInterp d R ζ r (hybridPoint w w' (m + 1))| := abs_sub_le _ _ _
          _ ≤ c * ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m),
                  |R * w i - R * w' i|
                + c * |R * w (⟨m, hm'⟩ : Fin d) - R * w' (⟨m, hm'⟩ : Fin d)| :=
              add_le_add h1 h2
          _ = c * (|R * w (⟨m, hm'⟩ : Fin d) - R * w' (⟨m, hm'⟩ : Fin d)|
                + ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m),
                  |R * w i - R * w' i|) := by ring
  have h := key d le_rfl
  rw [hybridPoint_dim] at h
  have hfilt : Finset.univ.filter (fun i : Fin d => (i : ℕ) < d) = (Finset.univ : Finset (Fin d)) := by
    ext i
    simp
  rw [hfilt] at h
  exact h

/-- **The sharp space modulus of the interpolated field**: the constant is the
largest mesh increment, not twice the largest mesh value.  At separations at or
below the mesh spacing `1/R` this is the estimate that is small, and it is what
the tightness clause of `prop:dlt4-heat-potential-invariance` needs at the small
scales, where comparing two points through the corners of their cells gives
nothing. -/
theorem abs_linInterp_sub_space_le_incr (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (K : ℝ)
    (hK : ∀ (k : ℕ) (z : Site d) (i : Fin d),
      |meshValue d R ζ k (Function.update z i (z i + 1)) - meshValue d R ζ k z| ≤ K)
    {r : ℝ} (hr : 0 ≤ r) (w w' : Sandpile.Continuum.Space d) :
    |linInterp d R ζ r w - linInterp d R ζ r w'|
      ≤ K * ∑ i : Fin d, |R * w i - R * w' i| := by
  exact abs_linInterp_sub_space_le_of_coord d R ζ
    (fun u v j h => abs_linInterp_sub_coord_le_incr d R ζ K hK hr u v j h) w w'

/-- **The sharp time modulus of the interpolated field**: the constant is the
largest increment of the mesh values in the time index. -/
theorem abs_linInterp_sub_time_le_incr (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (K : ℝ)
    (hK : ∀ (k : ℕ) (z : Site d), |meshValue d R ζ (k + 1) z - meshValue d R ζ k z| ≤ K)
    {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (w : Sandpile.Continuum.Space d) :
    |linInterp d R ζ r w - linInterp d R ζ r' w|
      ≤ K * |R ^ 2 * r - R ^ 2 * r'| := by
  classical
  have hK0 : (0:ℝ) ≤ K := le_trans (abs_nonneg _) (hK 0 (fun _ => 0))
  set b : Site d := fun i => ⌊R * w i⌋ with hb
  set t : Fin d → ℝ := fun i => R * w i - (b i : ℝ) with ht
  have ht0 : ∀ i, 0 ≤ t i := fun i => (fract_mem (R * w i)).1
  have ht1 : ∀ i, t i ≤ 1 := fun i => (fract_mem (R * w i)).2
  set F : (Fin d → Bool) → ℤ → ℝ := fun ε k =>
    meshValue d R ζ k.toNat (fun i => b i + if ε i then 1 else 0) with hF
  have key : ∀ u : ℝ, 0 ≤ u → ∀ ε : Fin d → Bool,
      (1 - (u - ((⌊u⌋₊ : ℕ) : ℝ))) * meshValue d R ζ ⌊u⌋₊ (fun i => b i + if ε i then 1 else 0)
        + (u - ((⌊u⌋₊ : ℕ) : ℝ))
            * meshValue d R ζ (⌊u⌋₊ + 1) (fun i => b i + if ε i then 1 else 0)
      = interp1 (F ε) u := by
    intro u hu ε
    have hfl0 : (0:ℤ) ≤ ⌊u⌋ := Int.floor_nonneg.mpr hu
    have hfl : (⌊u⌋).toNat = ⌊u⌋₊ := Int.floor_toNat u
    have hz : ((⌊u⌋₊ : ℕ) : ℤ) = ⌊u⌋ := by
      rw [← hfl]
      exact Int.toNat_of_nonneg hfl0
    have hcast : ((⌊u⌋₊ : ℕ) : ℝ) = ((⌊u⌋ : ℤ) : ℝ) := by exact_mod_cast hz
    have hsucc : (⌊u⌋ + 1).toNat = ⌊u⌋₊ + 1 := by omega
    rw [interp1, hF]
    simp only [hfl, hsucc]
    rw [Int.fract, hcast]
  have hdiff : linInterp d R ζ r w - linInterp d R ζ r' w
      = ∑ ε : Fin d → Bool, (∏ i : Fin d, if ε i then t i else 1 - t i) *
          (interp1 (F ε) (R ^ 2 * r) - interp1 (F ε) (R ^ 2 * r')) := by
    show (∑ ε : Fin d → Bool, (∏ i : Fin d, if ε i then t i else 1 - t i) *
        ((1 - (R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ)))
            * meshValue d R ζ ⌊R ^ 2 * r⌋₊ (fun i => b i + if ε i then 1 else 0) +
          (R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ))
            * meshValue d R ζ (⌊R ^ 2 * r⌋₊ + 1) (fun i => b i + if ε i then 1 else 0)))
        - (∑ ε : Fin d → Bool, (∏ i : Fin d, if ε i then t i else 1 - t i) *
        ((1 - (R ^ 2 * r' - ((⌊R ^ 2 * r'⌋₊ : ℕ) : ℝ)))
            * meshValue d R ζ ⌊R ^ 2 * r'⌋₊ (fun i => b i + if ε i then 1 else 0) +
          (R ^ 2 * r' - ((⌊R ^ 2 * r'⌋₊ : ℕ) : ℝ))
            * meshValue d R ζ (⌊R ^ 2 * r'⌋₊ + 1) (fun i => b i + if ε i then 1 else 0))) = _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [key _ (mul_nonneg (sq_nonneg R) hr) ε, key _ (mul_nonneg (sq_nonneg R) hr') ε]
    ring
  rw [hdiff]
  refine abs_sum_weight_mul_le _ _ (fun ε => prod_ite_nonneg t ht0 ht1 ε)
    (sum_prod_ite d t) _ ?_
  intro ε
  have hFincr : ∀ n : ℤ, |F ε (n + 1) - F ε n| ≤ K := by
    intro n
    rw [hF]
    by_cases hn : 0 ≤ n
    · have hsucc : (n + 1).toNat = n.toNat + 1 := by omega
      simp only [hsucc]
      exact hK n.toNat (fun i => b i + if ε i then 1 else 0)
    · have h1 : (n + 1).toNat = 0 := by omega
      have h2 : n.toNat = 0 := by omega
      simp only [h1, h2, sub_self, abs_zero]
      exact hK0
  exact abs_interp1_sub_le_incr (F ε) K hFincr (R ^ 2 * r) (R ^ 2 * r')

/-- **The sharp modulus of continuity of the interpolated field.**  Both
directions with the constant the largest mesh increment.  Together with
`abs_linInterp_sub_le'`, whose constant is twice the largest mesh value, this
covers both regimes of the tightness clause: the coarse scales, where the mesh
values at two points are compared directly, and the scales at or below the mesh
spacing `1/R`, where only the increment is small. -/
theorem abs_linInterp_sub_le_incr (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (K : ℝ)
    (hKt : ∀ (k : ℕ) (z : Site d), |meshValue d R ζ (k + 1) z - meshValue d R ζ k z| ≤ K)
    (hKs : ∀ (k : ℕ) (z : Site d) (i : Fin d),
      |meshValue d R ζ k (Function.update z i (z i + 1)) - meshValue d R ζ k z| ≤ K)
    {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (w w' : Sandpile.Continuum.Space d) :
    |linInterp d R ζ r w - linInterp d R ζ r' w'|
      ≤ K * |R ^ 2 * r - R ^ 2 * r'| + K * ∑ i : Fin d, |R * w i - R * w' i| := by
  have h1 := abs_linInterp_sub_time_le_incr d R ζ K hKt hr hr' w
  have h2 := abs_linInterp_sub_space_le_incr d R ζ K hKs (r := r') hr' w w'
  calc |linInterp d R ζ r w - linInterp d R ζ r' w'|
      ≤ |linInterp d R ζ r w - linInterp d R ζ r' w|
        + |linInterp d R ζ r' w - linInterp d R ζ r' w'| := abs_sub_le _ _ _
    _ ≤ K * |R ^ 2 * r - R ^ 2 * r'|
        + K * ∑ i : Fin d, |R * w i - R * w' i| := add_le_add h1 h2

end Sandpile.Support
