import Sandpile.Walk

/-!
# Nonnegativity and finite propagation speed of the lattice heat kernel

The lattice heat kernel of `Sandpile/Walk.lean` is nonnegative and has finite propagation speed:
`p_k(x, y) = 0` once the box distance from `x` to `y` exceeds `k`. Finite propagation speed is
what makes `g_t(x, ·)` finitely supported, and that in turn is what keeps every `tsum` against a
Green kernel in the frozen statements away from its junk value.
-/

namespace Sandpile

variable {d : ℕ}

/-- The box distance `max_i |x_i - y_i|`, the metric in which the boxes `Q(x, L)`
are balls. -/
def boxDist (x y : Site d) : ℕ := Finset.univ.sup fun i => (x i - y i).natAbs

/-- `boxDist x x = 0`: a site is at box distance zero from itself. -/
theorem boxDist_self (x : Site d) : boxDist x x = 0 := by
  simp [boxDist]

/-- If `boxDist x y = 0` then `x = y`, since every coordinate difference must vanish. -/
theorem boxDist_eq_zero {x y : Site d} (h : boxDist x y = 0) : x = y := by
  funext i
  have : (x i - y i).natAbs ≤ 0 := h ▸ Finset.le_sup (f := fun i => (x i - y i).natAbs)
    (Finset.mem_univ i)
  omega

/-- Moving by one unit vector changes the box distance by at most one. -/
theorem boxDist_add_unit_le (x y : Site d) (i : Fin d) :
    boxDist x y ≤ boxDist (x + unit i) y + 1 := by
  refine Finset.sup_le fun j _ => ?_
  have hj : (x j + unit i j - y j).natAbs ≤ boxDist (x + unit i) y :=
    Finset.le_sup (f := fun j => ((x + unit i) j - y j).natAbs) (Finset.mem_univ j)
  have hu : unit i j = 0 ∨ unit i j = 1 := by
    by_cases h : i = j
    · right; simp [unit, h]
    · left; simp [unit, Pi.single_eq_of_ne (Ne.symm h)]
  rcases hu with hu | hu <;> rw [hu] at hj <;> omega

/-- Moving by minus one unit vector changes the box distance by at most one. -/
theorem boxDist_sub_unit_le (x y : Site d) (i : Fin d) :
    boxDist x y ≤ boxDist (x - unit i) y + 1 := by
  refine Finset.sup_le fun j _ => ?_
  have hj : (x j - unit i j - y j).natAbs ≤ boxDist (x - unit i) y :=
    Finset.le_sup (f := fun j => ((x - unit i) j - y j).natAbs) (Finset.mem_univ j)
  have hu : unit i j = 0 ∨ unit i j = 1 := by
    by_cases h : i = j
    · right; simp [unit, h]
    · left; simp [unit, Pi.single_eq_of_ne (Ne.symm h)]
  rcases hu with hu | hu <;> rw [hu] at hj <;> omega

/-- The box distance obeys the triangle inequality. -/
theorem boxDist_trans (x y z : Site d) : boxDist x z ≤ boxDist x y + boxDist y z := by
  refine Finset.sup_le fun j _ => ?_
  have h1 : (x j - y j).natAbs ≤ boxDist x y :=
    Finset.le_sup (f := fun j => (x j - y j).natAbs) (Finset.mem_univ j)
  have h2 : (y j - z j).natAbs ≤ boxDist y z :=
    Finset.le_sup (f := fun j => (y j - z j).natAbs) (Finset.mem_univ j)
  omega

/-- Finite propagation speed: the walk cannot reach beyond box distance `k` in
`k` steps. -/
theorem heatKernel_eq_zero_of_lt : ∀ (k : ℕ) (x y : Site d), k < boxDist x y →
    heatKernel d k x y = 0 := by
  intro k
  induction k with
  | zero =>
      intro x y h
      have hxy : x ≠ y := fun hxy => by simp [hxy, boxDist_self] at h
      simp [heatKernel, LatticeProb.LocalCLT.heatKernel, hxy]
  | succ n ih =>
      intro x y h
      have hz : ∀ i : Fin d,
          heatKernel d n (x + unit i) y + heatKernel d n (x - unit i) y = 0 := by
        intro i
        have h1 : n < boxDist (x + unit i) y := by
          have := boxDist_add_unit_le x y i; omega
        have h2 : n < boxDist (x - unit i) y := by
          have := boxDist_sub_unit_le x y i; omega
        rw [ih _ _ h1, ih _ _ h2, add_zero]
      show (∑ i : Fin d, (heatKernel d n (x + unit i) y + heatKernel d n (x - unit i) y))
        / (2 * d) = 0
      rw [Finset.sum_congr rfl fun i _ => hz i]
      simp

/-- `p_k(x, ·)` is supported in the box of radius `k` about `x`. -/
theorem heatKernel_support (k : ℕ) (x : Site d) :
    Function.support (heatKernel d k x) ⊆ {y | boxDist x y ≤ k} := by
  intro y hy
  by_contra hk
  exact hy (heatKernel_eq_zero_of_lt k x y (by simpa using Nat.lt_of_not_le hk))

/-- `g_t(x, ·)` is supported in the box of radius `t` about `x`. -/
theorem greenTime_support (t : ℕ) (x : Site d) :
    Function.support (greenTime d t x) ⊆ {y | boxDist x y ≤ t} := by
  intro y hy
  by_contra hk
  refine hy ?_
  refine Finset.sum_eq_zero fun k hk' => heatKernel_eq_zero_of_lt k x y ?_
  have ht : t < boxDist x y := by simpa using Nat.lt_of_not_le hk
  have hkt : k < t := Finset.mem_range.mp hk'
  omega

/-- The heat kernel is nonnegative. -/
theorem heatKernel_nonneg : ∀ (k : ℕ) (x y : Site d), 0 ≤ heatKernel d k x y := by
  intro k
  induction k with
  | zero => intro x y; by_cases h : x = y <;> simp [heatKernel, LatticeProb.LocalCLT.heatKernel, h]
  | succ n ih =>
      intro x y
      show 0 ≤ (∑ i : Fin d, (heatKernel d n (x + unit i) y + heatKernel d n (x - unit i) y))
        / (2 * d)
      apply div_nonneg _ (by positivity)
      exact Finset.sum_nonneg fun i _ => add_nonneg (ih _ _) (ih _ _)

/-- The finite-time Green kernel is nonnegative. -/
theorem greenTime_nonneg (t : ℕ) (x y : Site d) : 0 ≤ greenTime d t x y :=
  Finset.sum_nonneg fun k _ => heatKernel_nonneg k x y

/-- The box of radius `r` about `x`, as a finset. -/
noncomputable def boxFinset (x : Site d) (r : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun i => Finset.Icc (x i - r) (x i + r)

/-- If `y` is within box distance `r` of `x`, then `y` belongs to `boxFinset x r`. -/
theorem mem_boxFinset {x y : Site d} {r : ℕ} (h : boxDist x y ≤ r) : y ∈ boxFinset x r := by
  refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_
  have : (x i - y i).natAbs ≤ r :=
    le_trans (Finset.le_sup (f := fun i => (x i - y i).natAbs) (Finset.mem_univ i)) h
  omega

/-- A field summed against the finite-time Green kernel is summable, whatever the
field: the kernel is supported in a finite box. -/
theorem summable_greenTime_mul (t : ℕ) (x : Site d) (f : Site d → ℝ) :
    Summable fun y => greenTime d t x y * f y := by
  refine summable_of_ne_finset_zero (s := boxFinset x t) fun y hy => ?_
  have : greenTime d t x y = 0 := by
    by_contra hne
    exact hy (mem_boxFinset (greenTime_support t x hne))
  simp [this]

/-- The heat kernel is translation invariant. -/
theorem heatKernel_add_right : ∀ (k : ℕ) (x y w : Site d),
    heatKernel d k (x + w) (y + w) = heatKernel d k x y := by
  intro k
  induction k with
  | zero =>
      intro x y w
      show (if x + w = y + w then (1 : ℝ) else 0) = if x = y then 1 else 0
      by_cases h : x = y
      · simp [h]
      · simp [h]
  | succ j ih =>
      intro x y w
      show (∑ i : Fin d, (heatKernel d j (x + w + unit i) (y + w)
              + heatKernel d j (x + w - unit i) (y + w))) / (2 * d)
          = (∑ i : Fin d, (heatKernel d j (x + unit i) y
              + heatKernel d j (x - unit i) y)) / (2 * d)
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : x + w + unit i = (x + unit i) + w := by abel
      have h2 : x + w - unit i = (x - unit i) + w := by abel
      rw [h1, h2, ih (x + unit i) y w, ih (x - unit i) y w]

/-- The finite-time Green kernel is translation invariant. -/
theorem greenTime_add_right (t : ℕ) (x y w : Site d) :
    greenTime d t (x + w) (y + w) = greenTime d t x y :=
  Finset.sum_congr rfl fun k _ => heatKernel_add_right k x y w

/-- The `ℓ²` mass of the Green coefficients does not depend on the base point. -/
theorem tsum_greenTime_sq_eq (t : ℕ) (x : Site d) :
    ∑' z : Site d, greenTime d t x z ^ 2 = ∑' z : Site d, greenTime d t 0 z ^ 2 := by
  rw [← (Equiv.addRight x).tsum_eq fun z : Site d => greenTime d t x z ^ 2]
  refine tsum_congr fun c => ?_
  have hg : greenTime d t x (c + x) = greenTime d t 0 c := by
    simpa using greenTime_add_right t 0 c x
  simpa using congrArg (fun r : ℝ => r ^ 2) hg

end Sandpile
