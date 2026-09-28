import Sandpile.Support.RectangleDuality

/-!
# Ray parity along a nearest-neighbor walk

`edgeRay v x y` is the mod-2 indicator that the unit horizontal edge `{x, y}` is crossed by the
downward vertical ray from `v` (the edge lies at or below `v`'s row, directly under `v`'s
column). Summing it over the edges of a walk with `walkEdgeSum` gives `walkRay p v`, the parity
of the number of times the walk `p` crosses that ray. The bulk of the module
(`edgeRay_horizontal_coboundary`, `edgeRay_vertical_right`, `edgeRay_vertical_left` and their
`walkRay_*` counterparts) shows this parity does not change when `v` is moved to a neighboring
lattice point that the walk avoids, so `walkRay_four_faces` and `walkRay_star_step` establish
that `walkRay p` is constant on the four corners of a unit cell, and hence on star-lattice
neighbors, as long as the walk stays away from all of them. `walkRay_below` and `walkRay_above`
compute the parity directly (`0` resp. `1`) when the walk stays entirely below, or entirely
above, `v`'s row.
-/

open scoped BigOperators
noncomputable section
namespace Sandpile

/-- The mod-2 indicator that the unit edge `{x, y}` is a horizontal edge lying at or below `v`'s
row, whose column lies directly below `v` (`x 0 ≤ v 0 < y 0` or the reverse). This is the
parity contribution of `{x, y}` to the downward vertical ray from `v`. -/
def edgeRay (v x y : Site 2) : ZMod 2 := by
  classical
  exact if ((x 0 ≤ v 0 ∧ v 0 < y 0) ∨ (y 0 ≤ v 0 ∧ v 0 < x 0)) ∧
      max (x 1) (y 1) ≤ v 1 then 1 else 0

/-- The mod-2 indicator that `x` lies in `v`'s column, at or below `v`'s row. -/
def columnBelow (v x : Site 2) : ZMod 2 := by
  classical
  exact if x 0 = v 0 ∧ x 1 ≤ v 1 then 1 else 0

/-- Splits adjacency in `lattice 2` into the four possible unit-step directions between `x`
and `y` (right, left, up, down), read off the two coordinate projections of the witnessing
`unit i` difference. -/
lemma lattice_two_adj_cases {x y : Site 2} (hxy : (lattice 2).Adj x y) :
    (y 0 = x 0 + 1 ∧ y 1 = x 1) ∨ (x 0 = y 0 + 1 ∧ x 1 = y 1) ∨
    (y 1 = x 1 + 1 ∧ y 0 = x 0) ∨ (x 1 = y 1 + 1 ∧ x 0 = y 0) := by
  obtain ⟨i, hi | hi⟩ := hxy
  · have h0 := congrArg (fun z : Site 2 => z 0) hi
    have h1 := congrArg (fun z : Site 2 => z 1) hi
    fin_cases i <;> simp [unit] at h0 h1 <;> omega
  · have h0 := congrArg (fun z : Site 2 => z 0) hi
    have h1 := congrArg (fun z : Site 2 => z 1) hi
    fin_cases i <;> simp [unit] at h0 h1 <;> omega

/-- Two points of `Site 2` are unequal iff they differ in coordinate `0` or coordinate `1`. -/
lemma site_two_ne_iff (x y : Site 2) : x ≠ y ↔ x 0 ≠ y 0 ∨ x 1 ≠ y 1 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    apply h
    ext i
    fin_cases i
    · exact hn.1
    · exact hn.2
  · rintro (h | h) he <;> exact h (congrFun he _)

/-- For an edge `{x, y}` avoiding `v`, the sum of the ray parities at `v` and at `v` shifted one
column left equals the coboundary `columnBelow v x + columnBelow v y`. Proved by the case split
`lattice_two_adj_cases` followed by direct arithmetic on each of the four edge orientations. -/
lemma edgeRay_horizontal_coboundary {v x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x ≠ v) (hy : y ≠ v) :
    edgeRay v x y + edgeRay (v - unit (0 : Fin 2)) x y = columnBelow v x + columnBelow v y := by
  have hx' := (site_two_ne_iff x v).mp hx
  have hy' := (site_two_ne_iff y v).mp hy
  obtain h | h | h | h := lattice_two_adj_cases hxy
  all_goals
    simp only [edgeRay, columnBelow, Pi.sub_apply, unit, Pi.single_apply, Fin.isValue,
      ite_true, max_le_iff]
    split_ifs <;> norm_num <;> first | exact CharTwo.two_eq_zero.symm | omega

/-- For an edge `{x, y}` avoiding `v`, the ray parity at `v` equals the ray parity at `v` shifted
one row down. Proved by the same case split on the edge orientation as
`edgeRay_horizontal_coboundary`. -/
lemma edgeRay_vertical_right {v x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x ≠ v) (hy : y ≠ v) : edgeRay v x y = edgeRay (v - unit (1 : Fin 2)) x y := by
  have hx' := (site_two_ne_iff x v).mp hx
  have hy' := (site_two_ne_iff y v).mp hy
  obtain h | h | h | h := lattice_two_adj_cases hxy
  all_goals
    simp only [edgeRay, Pi.sub_apply, unit, Pi.single_apply, Fin.isValue,
      ite_true, max_le_iff]
    split_ifs <;> norm_num [CharTwo.two_eq_zero] <;> omega

/-- The row-shift invariance of `edgeRay_vertical_right`, applied at the point `v` shifted one
column left instead of at `v` itself. -/
lemma edgeRay_vertical_left {v x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x ≠ v) (hy : y ≠ v) :
    edgeRay (v - unit (0 : Fin 2)) x y =
      edgeRay (v - unit (0 : Fin 2) - unit (1 : Fin 2)) x y := by
  have hx' := (site_two_ne_iff x v).mp hx
  have hy' := (site_two_ne_iff y v).mp hy
  obtain h | h | h | h := lattice_two_adj_cases hxy
  all_goals
    simp only [edgeRay, Pi.sub_apply, unit, Pi.single_apply, Fin.isValue,
      ite_true, max_le_iff]
    split_ifs <;> norm_num [CharTwo.two_eq_zero] <;> omega

/-- The sum of `f` over the consecutive edges of a walk `p`, by recursion on `p`. -/
def walkEdgeSum {V : Type*} {G : SimpleGraph V} (f : V → V → ZMod 2)
    {a b : V} (p : G.Walk a b) : ZMod 2 :=
  match p with
  | .nil => 0
  | .cons (v := c) _ q => f a c + walkEdgeSum f q

/-- Summing a coboundary `f x + f y` over the edges of a walk from `a` to `b` telescopes to
`f a + f b`, the interior terms cancelling in characteristic `2`. -/
lemma walkEdgeSum_coboundary {V : Type*} {G : SimpleGraph V} (f : V → ZMod 2)
    {a b : V} (p : G.Walk a b) : walkEdgeSum (fun x y => f x + f y) p = f a + f b := by
  induction p with
  | nil => exact (CharTwo.add_self_eq_zero _).symm
  | @cons a b c hab p ih =>
    simp only [walkEdgeSum, ih]
    linear_combination CharTwo.add_self_eq_zero (f b)

/-- `walkEdgeSum` is additive in its edge-function argument. -/
lemma walkEdgeSum_add {V : Type*} {G : SimpleGraph V} (f g : V → V → ZMod 2)
    {a b : V} (p : G.Walk a b) :
    walkEdgeSum (fun x y => f x y + g x y) p = walkEdgeSum f p + walkEdgeSum g p := by
  induction p with
  | nil => simp [walkEdgeSum]
  | @cons a b c hab p ih => simp only [walkEdgeSum, ih]; ring

/-- `walkEdgeSum f p = walkEdgeSum g p` whenever `f` and `g` agree on adjacent pairs both lying
in the support of `p`, by induction on `p`. -/
lemma walkEdgeSum_congr_on_support {V : Type*} {G : SimpleGraph V} (f g : V → V → ZMod 2)
    {a b : V} (p : G.Walk a b)
    (hfg : ∀ x ∈ p.support, ∀ y ∈ p.support, G.Adj x y → f x y = g x y) :
    walkEdgeSum f p = walkEdgeSum g p := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
    change f a b + walkEdgeSum f p = g a b + walkEdgeSum g p
    rw [hfg a (by simp) b (by simp), ih]
    · intro x hx y hy hxy
      exact hfg x (by simp [hx]) y (by simp [hy]) hxy
    · exact hab

/-- The parity of the number of times the nearest-neighbor walk `p` crosses the downward
vertical ray from `v`, i.e. `walkEdgeSum (edgeRay v) p`. -/
def walkRay {a b : Site 2} (p : (lattice 2).Walk a b) (v : Site 2) : ZMod 2 :=
  walkEdgeSum (edgeRay v) p

/-- If `v` avoids the support of `p` and both endpoints of `p` avoid `v`'s column, the ray
parity at `v` equals the ray parity one column to the left. Derived from
`edgeRay_horizontal_coboundary` via `walkEdgeSum_coboundary`, using that `columnBelow v a` and
`columnBelow v b` vanish since `a` and `b` are off `v`'s column. -/
lemma walkRay_horizontal {a b v : Site 2} (p : (lattice 2).Walk a b)
    (hv : v ∉ p.support) (ha : a 0 ≠ v 0) (hb : b 0 ≠ v 0) :
    walkRay p v = walkRay p (v - unit (0 : Fin 2)) := by
  have he := walkEdgeSum_congr_on_support
    (fun x y => edgeRay v x y + edgeRay (v - unit (0 : Fin 2)) x y)
    (fun x y => columnBelow v x + columnBelow v y) p
    (fun x hx y hy hxy => edgeRay_horizontal_coboundary hxy
      (fun he => hv (he ▸ hx)) (fun he => hv (he ▸ hy)))
  rw [walkEdgeSum_add, walkEdgeSum_coboundary] at he
  have hh : walkRay p v + walkRay p (v - unit (0 : Fin 2)) = 0 := by
    simpa only [columnBelow, ha, hb, false_and, if_false, zero_add, walkRay] using he
  have hc := congrArg (fun z => z + walkRay p (v - unit (0 : Fin 2))) hh
  simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using hc

/-- If `v` avoids the support of `p`, the ray parity at `v` equals the ray parity one row below,
by `edgeRay_vertical_right` and `walkEdgeSum_congr_on_support`. -/
lemma walkRay_vertical_right {a b v : Site 2} (p : (lattice 2).Walk a b)
    (hv : v ∉ p.support) : walkRay p v = walkRay p (v - unit (1 : Fin 2)) := by
  exact walkEdgeSum_congr_on_support _ _ p (fun x hx y hy hxy =>
    edgeRay_vertical_right hxy (fun he => hv (he ▸ hx)) (fun he => hv (he ▸ hy)))

/-- The row-shift invariance `walkRay_vertical_right`, applied at `v` shifted one column left,
via `edgeRay_vertical_left`. -/
lemma walkRay_vertical_left {a b v : Site 2} (p : (lattice 2).Walk a b)
    (hv : v ∉ p.support) :
    walkRay p (v - unit (0 : Fin 2)) = walkRay p (v - unit (0 : Fin 2) - unit (1 : Fin 2)) := by
  exact walkEdgeSum_congr_on_support _ _ p (fun x hx y hy hxy =>
    edgeRay_vertical_left hxy (fun he => hv (he ▸ hx)) (fun he => hv (he ▸ hy)))

/-- The mod-2 indicator that `x` lies at or to the left of `v`'s column. -/
def leftOfCut (v x : Site 2) : ZMod 2 := by
  classical
  exact if x 0 ≤ v 0 then 1 else 0

/-- If both endpoints of an edge lie at or below `v`'s row, the `max (x 1) (y 1) ≤ v 1` clause
of `edgeRay` is automatic, so the ray parity reduces to the coboundary
`leftOfCut v x + leftOfCut v y`. -/
lemma edgeRay_above {v x y : Site 2} (hx : x 1 ≤ v 1) (hy : y 1 ≤ v 1) :
    edgeRay v x y = leftOfCut v x + leftOfCut v y := by
  simp only [edgeRay, leftOfCut, max_le_iff, hx, hy, and_self, and_true]
  split_ifs <;> norm_num
  all_goals first | exact CharTwo.two_eq_zero.symm | omega

/-- If an edge `{x, y}` avoiding `v` has both endpoints at or above `v`'s row, it contributes
`0` to the ray parity at `v`, by the case split `lattice_two_adj_cases`. -/
lemma edgeRay_below {v x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x ≠ v) (hy : y ≠ v) (hvx : v 1 ≤ x 1) (hvy : v 1 ≤ y 1) : edgeRay v x y = 0 := by
  have hx' := (site_two_ne_iff x v).mp hx
  have hy' := (site_two_ne_iff y v).mp hy
  obtain h | h | h | h := lattice_two_adj_cases hxy
  all_goals
    simp only [edgeRay, max_le_iff]
    split_ifs <;> norm_num
    all_goals omega

/-- Summing the identically-zero edge function over any walk gives `0`. -/
lemma walkEdgeSum_zero {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    walkEdgeSum (fun _ _ => 0) p = 0 := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [walkEdgeSum, ih]

/-- If `v` avoids the support of `p` and every vertex of `p` lies at or above `v`'s row, the walk
never crosses the downward ray from `v`, so `walkRay p v = 0`. Follows from `edgeRay_below` and
`walkEdgeSum_zero`. -/
lemma walkRay_below {a b v : Site 2} (p : (lattice 2).Walk a b)
    (hv : v ∉ p.support) (hbelow : ∀ z ∈ p.support, v 1 ≤ z 1) : walkRay p v = 0 := by
  have he := walkEdgeSum_congr_on_support (edgeRay v) (fun _ _ => 0) p
    (fun x hx y hy hxy => edgeRay_below hxy (fun he => hv (he ▸ hx))
      (fun he => hv (he ▸ hy)) (hbelow x hx) (hbelow y hy))
  exact he.trans (walkEdgeSum_zero p)

/-- If every vertex of `p` lies at or below `v`'s row, and the endpoints straddle `v`'s column
(`a` weakly left, `b` strictly right), the walk crosses the downward ray from `v` exactly once,
so `walkRay p v = 1`. Follows from `edgeRay_above` and `walkEdgeSum_coboundary`. -/
lemma walkRay_above {a b v : Site 2} (p : (lattice 2).Walk a b)
    (habove : ∀ z ∈ p.support, z 1 ≤ v 1) (ha : a 0 ≤ v 0) (hb : v 0 < b 0) : walkRay p v = 1 := by
  have he := walkEdgeSum_congr_on_support (edgeRay v)
    (fun x y => leftOfCut v x + leftOfCut v y) p
    (fun x hx y hy _ => edgeRay_above (habove x hx) (habove y hy))
  rw [walkEdgeSum_coboundary] at he
  simpa only [walkRay, leftOfCut, ha, not_le.mpr hb, if_true, if_false, add_zero] using he

/-- If `v` avoids the support of `p` and both endpoints avoid `v`'s column, the ray parity at `v`
agrees with the ray parity at any of the three other corners `u` of the unit cell with `v` as one
corner (`u 0 ∈ {v 0, v 0 - 1}`, `u 1 ∈ {v 1, v 1 - 1}`). Assembled from `walkRay_horizontal`,
`walkRay_vertical_right` and `walkRay_vertical_left`. -/
lemma walkRay_four_faces {a b v u : Site 2} (p : (lattice 2).Walk a b)
    (hv : v ∉ p.support) (ha : a 0 ≠ v 0) (hb : b 0 ≠ v 0)
    (hu0 : u 0 = v 0 ∨ u 0 = v 0 - 1) (hu1 : u 1 = v 1 ∨ u 1 = v 1 - 1) :
    walkRay p v = walkRay p u := by
  obtain hu0 | hu0 := hu0
  · obtain hu1 | hu1 := hu1
    · have he : u = v := by ext i; fin_cases i <;> assumption
      rw [he]
    · have he : u = v - unit (1 : Fin 2) := by
        ext i
        fin_cases i <;> simp [unit, hu0, hu1]
      rw [he]
      exact walkRay_vertical_right p hv
  · obtain hu1 | hu1 := hu1
    · have he : u = v - unit (0 : Fin 2) := by
        ext i
        fin_cases i <;> simp [unit, hu0, hu1]
      rw [he]
      exact walkRay_horizontal p hv ha hb
    · have he : u = v - unit (0 : Fin 2) - unit (1 : Fin 2) := by
        ext i
        fin_cases i <;> simp [unit, hu0, hu1]
      rw [he]
      exact (walkRay_horizontal p hv ha hb).trans (walkRay_vertical_left p hv)

/-- If `v` and `w` are star-lattice adjacent (differ by at most one in each coordinate) and both
avoid the support of `p` and both endpoints' columns, the ray parity at `v` equals the ray
parity at `w`. Both are related to the shared corner `u = (min (v 0) (w 0), min (v 1) (w 1))` of
their common unit cell via `walkRay_four_faces`. -/
lemma walkRay_star_step {a b v w : Site 2} (p : (lattice 2).Walk a b)
    (hv : v ∉ p.support) (hw : w ∉ p.support)
    (hav : a 0 ≠ v 0) (hbv : b 0 ≠ v 0) (haw : a 0 ≠ w 0) (hbw : b 0 ≠ w 0)
    (hvw : (starLatticeGraph 2).Adj v w) : walkRay p v = walkRay p w := by
  let u : Site 2 := ![min (v 0) (w 0), min (v 1) (w 1)]
  have hdist (i : Fin 2) : |v i - w i| ≤ 1 := by
    have hh := hvw.2 i
    simpa only [Int.natCast_natAbs, Nat.cast_one] using
      (show ((v i - w i).natAbs : ℤ) ≤ (1 : ℕ) from by exact_mod_cast hh)
  have hfaces (i : Fin 2) :
      (min (v i) (w i) = v i ∨ min (v i) (w i) = v i - 1) ∧
      (min (v i) (w i) = w i ∨ min (v i) (w i) = w i - 1) := by
    have hh := abs_le.mp (hdist i)
    omega
  exact (walkRay_four_faces p hv hav hbv (u := u) (hfaces 0).1 (hfaces 1).1).trans
    (walkRay_four_faces p hw haw hbw (u := u) (hfaces 0).2 (hfaces 1).2).symm

end Sandpile
