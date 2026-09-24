/-
The walk killed on leaving a set: the elementary bounds on `p_k^D` and `g_t^D`.

`ssec:d4-percolation` builds the finite-time killed Green field
`𝓑_{r,N}(z) = ∑_u g_N^{Q(0,r)}(0,u) ζ(z+u)` of `sandpile.tex:3863-3866` and
uses three properties of the killed kernel: it is dominated by the free kernel,
so it inherits the support in the box of radius `k`; its total mass at each
time is at most one, so `∑_y g_N^D(x,y) ≤ N`, which is the bound the influence
weights of `lem:d4-exit-average-concentration` are read against; and it is
translation covariant, which is what turns the field at `z` into the field at
the origin.
-/
import Sandpile.Support.Iterate

namespace Sandpile

variable {d : ℕ}

theorem killedKernel_nonneg (D : Set (Site d)) :
    ∀ (k : ℕ) (x y : Site d), 0 ≤ killedKernel D k x y := by
  intro k
  induction k with
  | zero =>
      intro x y
      show 0 ≤ Set.indicator D (fun z => if z = y then (1:ℝ) else 0) x
      by_cases hx : x ∈ D
      · rw [Set.indicator_of_mem hx]
        by_cases h : x = y <;> simp [h]
      · rw [Set.indicator_of_notMem hx]
  | succ n ih =>
      intro x y
      show 0 ≤ Set.indicator D (fun z => (∑ i : Fin d,
          (killedKernel D n (z + unit i) y + killedKernel D n (z - unit i) y)) / (2 * d)) x
      by_cases hx : x ∈ D
      · rw [Set.indicator_of_mem hx]
        apply div_nonneg _ (by positivity)
        exact Finset.sum_nonneg fun i _ => add_nonneg (ih _ _) (ih _ _)
      · rw [Set.indicator_of_notMem hx]

theorem killedKernel_le_heatKernel (D : Set (Site d)) :
    ∀ (k : ℕ) (x y : Site d), killedKernel D k x y ≤ heatKernel d k x y := by
  intro k
  induction k with
  | zero =>
      intro x y
      show Set.indicator D (fun z => if z = y then (1:ℝ) else 0) x ≤ (if x = y then (1:ℝ) else 0)
      by_cases hx : x ∈ D
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        by_cases h : x = y <;> simp [h]
  | succ n ih =>
      intro x y
      show Set.indicator D (fun z => (∑ i : Fin d,
          (killedKernel D n (z + unit i) y + killedKernel D n (z - unit i) y)) / (2 * d)) x
        ≤ (∑ i : Fin d,
          (heatKernel d n (x + unit i) y + heatKernel d n (x - unit i) y)) / (2 * d)
      have hle : (∑ i : Fin d,
          (killedKernel D n (x + unit i) y + killedKernel D n (x - unit i) y)) / (2 * d)
        ≤ (∑ i : Fin d,
          (heatKernel d n (x + unit i) y + heatKernel d n (x - unit i) y)) / (2 * d) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact Finset.sum_le_sum fun i _ => add_le_add (ih _ _) (ih _ _)
      have hnn : (0:ℝ) ≤ (∑ i : Fin d,
          (heatKernel d n (x + unit i) y + heatKernel d n (x - unit i) y)) / (2 * d) := by
        apply div_nonneg _ (by positivity)
        exact Finset.sum_nonneg fun i _ =>
          add_nonneg (heatKernel_nonneg _ _ _) (heatKernel_nonneg _ _ _)
      by_cases hx : x ∈ D
      · rw [Set.indicator_of_mem hx]; exact hle
      · rw [Set.indicator_of_notMem hx]; exact hnn

theorem killedKernel_eq_zero_of_lt (D : Set (Site d)) (k : ℕ) (x y : Site d)
    (h : k < boxDist x y) : killedKernel D k x y = 0 := by
  have h1 := killedKernel_le_heatKernel D k x y
  have h2 := killedKernel_nonneg D k x y
  rw [heatKernel_eq_zero_of_lt k x y h] at h1
  linarith

theorem killedKernel_support (D : Set (Site d)) (k : ℕ) (x : Site d) {y : Site d}
    (h : killedKernel D k x y ≠ 0) : boxDist x y ≤ k := by
  by_contra hk
  exact h (killedKernel_eq_zero_of_lt D k x y (by simpa using Nat.lt_of_not_le hk))

theorem killedGreenTime_nonneg (D : Set (Site d)) (N : ℕ) (x y : Site d) :
    0 ≤ killedGreenTime D N x y :=
  Finset.sum_nonneg fun k _ => killedKernel_nonneg D k x y

theorem killedGreenTime_le_greenTime (D : Set (Site d)) (N : ℕ) (x y : Site d) :
    killedGreenTime D N x y ≤ greenTime d N x y :=
  Finset.sum_le_sum fun k _ => killedKernel_le_heatKernel D k x y

theorem killedGreenTime_support (D : Set (Site d)) (N : ℕ) (x : Site d) {y : Site d}
    (h : killedGreenTime D N x y ≠ 0) : boxDist x y ≤ N := by
  by_contra hk
  refine h (Finset.sum_eq_zero fun k hk' => killedKernel_eq_zero_of_lt D k x y ?_)
  have hN : N < boxDist x y := by simpa using Nat.lt_of_not_le hk
  have hkN : k < N := Finset.mem_range.mp hk'
  omega

theorem tsum_killedKernel_le_one (hd : 1 ≤ d) (D : Set (Site d)) (k : ℕ) (x : Site d) :
    ∑' y : Site d, killedKernel D k x y ≤ 1 := by
  classical
  have hsupp : ∀ y ∉ boxFinset x k, killedKernel D k x y = 0 := by
    intro y hy
    by_contra hne
    exact hy (mem_boxFinset (killedKernel_support D k x hne))
  have hsupp' : ∀ y ∉ boxFinset x k, heatKernel d k x y = 0 := by
    intro y hy
    by_contra hne
    exact hy (mem_boxFinset (heatKernel_support k x hne))
  have hh : ∑' y : Site d, heatKernel d k x y = ∑ y ∈ boxFinset x k, heatKernel d k x y :=
    tsum_eq_sum hsupp'
  rw [tsum_heatKernel hd k x] at hh
  rw [tsum_eq_sum hsupp]
  calc ∑ y ∈ boxFinset x k, killedKernel D k x y
      ≤ ∑ y ∈ boxFinset x k, heatKernel d k x y :=
        Finset.sum_le_sum fun y _ => killedKernel_le_heatKernel D k x y
    _ = 1 := hh.symm

theorem summable_killedGreenTime_mul (D : Set (Site d)) (N : ℕ) (x : Site d)
    (f : Site d → ℝ) : Summable fun y : Site d => killedGreenTime D N x y * f y := by
  classical
  refine summable_of_ne_finset_zero (s := boxFinset x N) fun y hy => ?_
  have hz : killedGreenTime D N x y = 0 := by
    by_contra hne
    exact hy (mem_boxFinset (killedGreenTime_support D N x hne))
  simp [hz]

theorem tsum_killedGreenTime_le (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ) (x : Site d) :
    ∑' y : Site d, killedGreenTime D N x y ≤ (N : ℝ) := by
  classical
  have hsupp : ∀ y ∉ boxFinset x N, killedGreenTime D N x y = 0 := by
    intro y hy
    by_contra hne
    exact hy (mem_boxFinset (killedGreenTime_support D N x hne))
  rw [tsum_eq_sum hsupp]
  have hexp : ∑ y ∈ boxFinset x N, killedGreenTime D N x y
      = ∑ k ∈ Finset.range N, ∑ y ∈ boxFinset x N, killedKernel D k x y := by
    simp only [killedGreenTime]
    exact Finset.sum_comm
  rw [hexp]
  calc ∑ k ∈ Finset.range N, ∑ y ∈ boxFinset x N, killedKernel D k x y
      ≤ ∑ _k ∈ Finset.range N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkN : k < N := Finset.mem_range.mp hk
        have hsub : ∀ y ∉ boxFinset x N, killedKernel D k x y = 0 := by
          intro y hy
          by_contra hne
          exact hy (mem_boxFinset
            (le_trans (killedKernel_support D k x hne) (le_of_lt hkN)))
        have heq : ∑ y ∈ boxFinset x N, killedKernel D k x y
            = ∑' y : Site d, killedKernel D k x y := (tsum_eq_sum hsub).symm
        rw [heq]
        exact tsum_killedKernel_le_one hd D k x
    _ = (N : ℝ) := by simp

/-- The killed kernel is translation covariant: shifting the domain and both
arguments by `w` changes nothing. -/
theorem killedKernel_translate (D : Set (Site d)) (w : Site d) :
    ∀ (k : ℕ) (x y : Site d),
      killedKernel {u : Site d | u + w ∈ D} k x y = killedKernel D k (x + w) (y + w) := by
  intro k
  induction k with
  | zero =>
      intro x y
      simp only [killedKernel]
      by_cases hx : x + w ∈ D
      · rw [Set.indicator_of_mem (by exact hx : x ∈ {u : Site d | u + w ∈ D}),
          Set.indicator_of_mem hx]
        by_cases h : x = y
        · simp [h]
        · have h' : x + w ≠ y + w := fun hc => h (by exact add_right_cancel hc)
          simp [h, h']
      · rw [Set.indicator_of_notMem (by exact hx : x ∉ {u : Site d | u + w ∈ D}),
          Set.indicator_of_notMem hx]
  | succ n ih =>
      intro x y
      simp only [killedKernel]
      by_cases hx : x + w ∈ D
      · rw [Set.indicator_of_mem (by exact hx : x ∈ {u : Site d | u + w ∈ D}),
          Set.indicator_of_mem hx]
        have hsum : (∑ i : Fin d,
            (killedKernel {u : Site d | u + w ∈ D} n (x + unit i) y
              + killedKernel {u : Site d | u + w ∈ D} n (x - unit i) y))
          = ∑ i : Fin d,
            (killedKernel D n ((x + w) + unit i) (y + w)
              + killedKernel D n ((x + w) - unit i) (y + w)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ih (x + unit i) y, ih (x - unit i) y]
          congr 2 <;> abel
        rw [hsum]
      · rw [Set.indicator_of_notMem (by exact hx : x ∉ {u : Site d | u + w ∈ D}),
          Set.indicator_of_notMem hx]

theorem killedGreenTime_translate (D : Set (Site d)) (w : Site d) (N : ℕ) (x y : Site d) :
    killedGreenTime {u : Site d | u + w ∈ D} N x y = killedGreenTime D N (x + w) (y + w) :=
  Finset.sum_congr rfl fun k _ => killedKernel_translate D w k x y

/-! ### The killed pairing

`𝓑_{r,N}` of `sandpile.tex:3858-3861` is the scenery paired with the killed
Green kernel.  The pairing with the killed heat kernel obeys two recursions: the
FIRST-step one, which is the definition of `killedKernel`, and the LAST-step
one, which is what the walk supplies.  The second follows from the first because
the operator `g ↦ 1_D · Pg` commutes with its own iterates, and it is the form
the strong Markov property of the walk produces. -/

/-- `A_k(f)(x) = ∑_y p_k^D(x,y) f(y)`. -/
noncomputable def killedPair (D : Set (Site d)) (k : ℕ) (f : Site d → ℝ) (x : Site d) : ℝ :=
  ∑' y : Site d, killedKernel D k x y * f y

theorem killedPair_eq_sum (D : Set (Site d)) (k : ℕ) (f : Site d → ℝ) (x : Site d) :
    killedPair D k f x = ∑ y ∈ boxFinset x k, killedKernel D k x y * f y := by
  classical
  refine tsum_eq_sum fun y hy => ?_
  have hz : killedKernel D k x y = 0 := by
    by_contra hne
    exact hy (mem_boxFinset (killedKernel_support D k x hne))
  simp [hz]

/-- The pairing at a neighbour of `x`, read on the box of radius `k + 1`. -/
theorem killedPair_eq_sum_of_near (D : Set (Site d)) (k : ℕ) (f : Site d → ℝ)
    (x w : Site d) (hw : boxDist x w ≤ 1) :
    killedPair D k f w = ∑ y ∈ boxFinset x (k + 1), killedKernel D k w y * f y := by
  classical
  refine tsum_eq_sum fun y hy => ?_
  have hz : killedKernel D k w y = 0 := by
    by_contra hne
    refine hy (mem_boxFinset ?_)
    calc boxDist x y ≤ boxDist x w + boxDist w y := boxDist_trans _ _ _
      _ ≤ 1 + k := add_le_add hw (killedKernel_support D k w hne)
      _ = k + 1 := by omega
  simp [hz]

theorem boxDist_add_unit_self (x : Site d) (i : Fin d) : boxDist x (x + unit i) ≤ 1 := by
  have h := boxDist_add_unit_le x (x + unit i) i
  rw [boxDist_self] at h
  omega

theorem boxDist_sub_unit_self (x : Site d) (i : Fin d) : boxDist x (x - unit i) ≤ 1 := by
  have h := boxDist_sub_unit_le x (x - unit i) i
  rw [boxDist_self] at h
  omega

theorem killedPair_zero (D : Set (Site d)) (f : Site d → ℝ) (x : Site d) :
    killedPair D 0 f x = D.indicator f x := by
  classical
  have hsingle : ∀ y : Site d, y ≠ x → killedKernel D 0 x y * f y = 0 := by
    intro y hy
    have hz : killedKernel D 0 x y = 0 := by
      show Set.indicator D (fun z => if z = y then (1 : ℝ) else 0) x = 0
      by_cases hx : x ∈ D
      · rw [Set.indicator_of_mem hx, if_neg (fun hc => hy hc.symm)]
      · rw [Set.indicator_of_notMem hx]
    simp [hz]
  rw [killedPair, tsum_eq_single x hsingle]
  by_cases hx : x ∈ D
  · have hdiag : killedKernel D 0 x x = 1 := by
      show Set.indicator D (fun z => if z = x then (1 : ℝ) else 0) x = 1
      rw [Set.indicator_of_mem hx, if_pos rfl]
    rw [hdiag, one_mul, Set.indicator_of_mem hx]
  · have hdiag : killedKernel D 0 x x = 0 := by
      show Set.indicator D (fun z => if z = x then (1 : ℝ) else 0) x = 0
      rw [Set.indicator_of_notMem hx]
    rw [hdiag, zero_mul, Set.indicator_of_notMem hx]

/-- **The first-step recursion** `A_{k+1}(f) = 1_D · P A_k(f)`, which is the
definition of the killed kernel read against a field. -/
theorem killedPair_succ (D : Set (Site d)) (k : ℕ) (f : Site d → ℝ) (x : Site d) :
    killedPair D (k + 1) f x = D.indicator (fun z => avg (killedPair D k f) z) x := by
  classical
  by_cases hx : x ∈ D
  · rw [Set.indicator_of_mem hx]
    have hterm : ∀ y : Site d, killedKernel D (k + 1) x y
        = (∑ i : Fin d,
            (killedKernel D k (x + unit i) y + killedKernel D k (x - unit i) y)) / (2 * d) := by
      intro y
      show Set.indicator D (fun z => (∑ i : Fin d,
          (killedKernel D k (z + unit i) y + killedKernel D k (z - unit i) y)) / (2 * d)) x = _
      rw [Set.indicator_of_mem hx]
    have hswap : ∑ y ∈ boxFinset x (k + 1),
          ((∑ i : Fin d,
            (killedKernel D k (x + unit i) y + killedKernel D k (x - unit i) y)) / (2 * d))
            * f y
        = (∑ i : Fin d,
            ((∑ y ∈ boxFinset x (k + 1), killedKernel D k (x + unit i) y * f y)
              + ∑ y ∈ boxFinset x (k + 1), killedKernel D k (x - unit i) y * f y))
          / (2 * d) := by
      simp only [div_mul_eq_mul_div]
      rw [← Finset.sum_div]
      congr 1
      simp only [Finset.sum_mul, add_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    rw [killedPair_eq_sum, Finset.sum_congr rfl (fun y _ => by rw [hterm y]), hswap]
    show _ = (∑ i : Fin d,
      (killedPair D k f (x + unit i) + killedPair D k f (x - unit i))) / (2 * d)
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [killedPair_eq_sum_of_near D k f x (x + unit i) (boxDist_add_unit_self x i),
      killedPair_eq_sum_of_near D k f x (x - unit i) (boxDist_sub_unit_self x i)]
  · rw [Set.indicator_of_notMem hx, killedPair]
    have hz : ∀ y : Site d, killedKernel D (k + 1) x y * f y = 0 := by
      intro y
      have h0 : killedKernel D (k + 1) x y = 0 := by
        show Set.indicator D (fun z => (∑ i : Fin d,
            (killedKernel D k (z + unit i) y + killedKernel D k (z - unit i) y)) / (2 * d)) x = 0
        rw [Set.indicator_of_notMem hx]
      simp [h0]
    simp [hz]

/-- **The last-step recursion** `A_{k+1}(f) = A_k(P(1_D f))`, which is the form
the strong Markov property of the walk produces. -/
theorem killedPair_succ_shift (D : Set (Site d)) :
    ∀ (k : ℕ) (f : Site d → ℝ) (x : Site d),
      killedPair D (k + 1) f x = killedPair D k (fun z => avg (D.indicator f) z) x := by
  intro k
  induction k with
  | zero =>
      intro f x
      rw [killedPair_succ, killedPair_zero]
      refine congrArg (fun g : Site d → ℝ => D.indicator g x) ?_
      funext z
      exact congrArg (fun g : Site d → ℝ => avg g z) (funext fun w => killedPair_zero D f w)
  | succ n ih =>
      intro f x
      rw [killedPair_succ (k := n + 1)]
      have hfun : killedPair D (n + 1) f
          = killedPair D n (fun z => avg (D.indicator f) z) := funext fun w => ih f w
      rw [hfun, ← killedPair_succ]

/-- `∑_y g_N^D(x,y) f(y)`, the killed Green field of `sandpile.tex:3858-3861`. -/
noncomputable def killedGreenPair (D : Set (Site d)) (N : ℕ) (f : Site d → ℝ)
    (x : Site d) : ℝ :=
  ∑' y : Site d, killedGreenTime D N x y * f y

theorem killedGreenPair_eq_sum (D : Set (Site d)) (N : ℕ) (f : Site d → ℝ) (x : Site d) :
    killedGreenPair D N f x = ∑ k ∈ Finset.range N, killedPair D k f x := by
  classical
  have hbox : killedGreenPair D N f x
      = ∑ y ∈ boxFinset x N, killedGreenTime D N x y * f y := by
    refine tsum_eq_sum fun y hy => ?_
    have hz : killedGreenTime D N x y = 0 := by
      by_contra hne
      exact hy (mem_boxFinset (killedGreenTime_support D N x hne))
    simp [hz]
  have hswap : ∑ y ∈ boxFinset x N, killedGreenTime D N x y * f y
      = ∑ k ∈ Finset.range N, ∑ y ∈ boxFinset x N, killedKernel D k x y * f y := by
    simp only [killedGreenTime, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hbox, hswap]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkN : k < N := Finset.mem_range.mp hk
  refine (tsum_eq_sum fun y hy => ?_).symm
  have hz : killedKernel D k x y = 0 := by
    by_contra hne
    exact hy (mem_boxFinset (le_trans (killedKernel_support D k x hne) (le_of_lt hkN)))
  simp [hz]

/-- The killed Green field written at the origin.  This is the shape
`𝓑_{r,N}(z) = ∑_u g_N^{Q(0,r)}(0,u) ζ(z+u)` of `sandpile.tex:3858-3861`, and it
is the pairing of the scenery with the kernel killed on the translated domain. -/
theorem tsum_killedGreenTime_shift (D : Set (Site d)) (N : ℕ) (z : Site d)
    (ζ : Site d → ℝ) :
    (∑' u : Site d, killedGreenTime {w : Site d | w + z ∈ D} N 0 u * ζ (z + u))
      = killedGreenPair D N ζ z := by
  have hstep : ∀ u : Site d,
      killedGreenTime {w : Site d | w + z ∈ D} N 0 u * ζ (z + u)
        = killedGreenTime D N z (u + z) * ζ (u + z) := by
    intro u
    rw [killedGreenTime_translate D z N 0 u, zero_add, add_comm z u]
  rw [tsum_congr hstep, killedGreenPair]
  exact (Equiv.addRight z).tsum_eq (fun y => killedGreenTime D N z y * ζ y)

end Sandpile
