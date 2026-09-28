import Sandpile.Support.Kernel

/-!
# Parity of simple random walk on `ℤ^d`

Each step of the simple random walk on `ℤ^d` changes the coordinate sum by exactly one, so the
coordinate sums of the two endpoints together with the number of steps always add up to an even
number (`SameParity`); equivalently, the `n`-step transition kernel `Sandpile.heatKernel`
vanishes off this parity class (`heatKernel_eq_zero_of_not_sameParity`). Restricting a lattice
sum to the parity class is the same as averaging the full sum against the alternating parity
sign `parSign` (`sum_filter_sameParity_eq`), and for fixed endpoints the admissible pairs of
times in a double sum form one parity class of their total (`filter_sameParity_eq_or`,
`sum_time_double_eq_filter`). This is the only property of the parity class the local central
limit theorem needs when summed against the cells of the time mesh.
-/

open Sandpile

namespace Sandpile.Support

variable {d : ℕ}

/-- One step in a positive direction raises the coordinate sum by one. -/
theorem sum_coord_add_unit (x : Site d) (i : Fin d) :
    (∑ j, (x + Sandpile.unit i) j) = (∑ j, x j) + 1 := by
  simp [Sandpile.unit, Finset.sum_add_distrib]

/-- One step in a negative direction lowers the coordinate sum by one. -/
theorem sum_coord_sub_unit (x : Site d) (i : Fin d) :
    (∑ j, (x - Sandpile.unit i) j) = (∑ j, x j) - 1 := by
  simp [Sandpile.unit, Finset.sum_sub_distrib]

/-- The parity class of a pair of sites at a given number of steps: the walk can
join `x` to `y` in `n` steps only inside this class. -/
def SameParity (n : ℕ) (x y : Site d) : Prop :=
  ((∑ i, x i) + (∑ i, y i) + (n : ℤ)) % 2 = 0

/-- `SameParity n x y` is decidable, since it unfolds to a decidable equality on `ℤ`. -/
instance (n : ℕ) (x y : Site d) : Decidable (SameParity n x y) := by
  unfold SameParity; infer_instance

/-- **Parity of the walk.**  A positive `n`-step transition probability forces
the coordinate sums of the two endpoints and `n` to add up to an even number. -/
theorem sameParity_of_heatKernel_ne_zero :
    ∀ (n : ℕ) (x y : Site d), Sandpile.heatKernel d n x y ≠ 0 → SameParity n x y := by
  intro n
  induction n with
  | zero =>
      intro x y hxy
      have hx : x = y := by
        by_contra h
        exact hxy (by simp [Sandpile.heatKernel, LatticeProb.LocalCLT.heatKernel, h])
      subst hx
      unfold SameParity
      simp only [Nat.cast_zero, add_zero]
      omega
  | succ k ih =>
      intro x y hxy
      have hsum : (∑ i : Fin d, (Sandpile.heatKernel d k (x + Sandpile.unit i) y
          + Sandpile.heatKernel d k (x - Sandpile.unit i) y)) ≠ 0 := by
        intro h
        apply hxy
        show (∑ i : Fin d, (Sandpile.heatKernel d k (x + Sandpile.unit i) y
          + Sandpile.heatKernel d k (x - Sandpile.unit i) y)) / (2 * (d : ℝ)) = 0
        rw [h, zero_div]
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
      have hor : Sandpile.heatKernel d k (x + Sandpile.unit i) y ≠ 0
          ∨ Sandpile.heatKernel d k (x - Sandpile.unit i) y ≠ 0 := by
        by_contra hc
        simp only [not_or, ne_eq, not_not] at hc
        rw [hc.1, hc.2, add_zero] at hi
        exact hi rfl
      rcases hor with h | h
      · have hp := ih (x + Sandpile.unit i) y h
        rw [SameParity, sum_coord_add_unit] at hp
        show ((∑ i, x i) + (∑ i, y i) + ((k + 1 : ℕ) : ℤ)) % 2 = 0
        push_cast at hp ⊢
        omega
      · have hp := ih (x - Sandpile.unit i) y h
        rw [SameParity, sum_coord_sub_unit] at hp
        show ((∑ i, x i) + (∑ i, y i) + ((k + 1 : ℕ) : ℤ)) % 2 = 0
        push_cast at hp ⊢
        omega

/-- The transition probability vanishes off the parity class. -/
theorem heatKernel_eq_zero_of_not_sameParity (n : ℕ) (x y : Site d)
    (h : ¬ SameParity n x y) : Sandpile.heatKernel d n x y = 0 := by
  by_contra hne
  exact h (sameParity_of_heatKernel_ne_zero n x y hne)


/-- The sign of the parity class: `+1` inside it, `-1` outside.  Averaging
against it is what restricts a lattice sum to the class. -/
noncomputable def parSign (n : ℕ) (x y : Site d) : ℝ :=
  if SameParity n x y then 1 else -1

/-- **Restricting a sum to the parity class is averaging against the parity
sign.**  This is the "density `1/2`" of the parity class quoted at
`sandpile.tex:1157-1161`, in the form in which it is used: the restricted sum is
half the full sum plus half an alternating sum. -/
theorem sum_filter_sameParity_eq (n : ℕ) (x : Site d) (s : Finset (Site d))
    (f : Site d → ℝ) :
    ∑ y ∈ s.filter (fun y => SameParity n x y), f y
      = (∑ y ∈ s, f y + ∑ y ∈ s, parSign n x y * f y) / 2 := by
  classical
  rw [Finset.sum_filter, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : SameParity n x y
  · simp only [h, if_true, parSign]
    ring
  · simp only [h, if_false, parSign]
    ring

/-! ### The parity class of the time pairs

For fixed endpoints the admissible times are one parity class of `ℕ`, so the
pairs `(a,b)` whose total is admissible are one parity class of the total.  This
is the form in which the "density `1/2`" of `sandpile.tex:1157-1161` enters the
double time sum of `prop:weighted-membrane-limit`. -/

/-- **For fixed endpoints the admissible time pairs are one parity class of the
total.** -/
theorem filter_sameParity_eq_or (x y : Site d) (N : ℕ) :
    ((Finset.range N) ×ˢ (Finset.range N)).filter
        (fun p : ℕ × ℕ => SameParity (p.1 + p.2) x y)
      = ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p : ℕ × ℕ => Even (p.1 + p.2))
    ∨ ((Finset.range N) ×ˢ (Finset.range N)).filter
        (fun p : ℕ × ℕ => SameParity (p.1 + p.2) x y)
      = ((Finset.range N) ×ˢ (Finset.range N)).filter
        (fun p : ℕ × ℕ => ¬ Even (p.1 + p.2)) := by
  classical
  by_cases hk : ((∑ i, x i) + (∑ i, y i)) % 2 = 0
  · refine Or.inl (Finset.filter_congr fun p _ => ?_)
    show SameParity (p.1 + p.2) x y ↔ Even (p.1 + p.2)
    rw [SameParity, Nat.even_iff]
    have hc : ((p.1 + p.2 : ℕ) : ℤ) = (p.1 : ℤ) + (p.2 : ℤ) := by push_cast; ring
    omega
  · refine Or.inr (Finset.filter_congr fun p _ => ?_)
    show SameParity (p.1 + p.2) x y ↔ ¬ Even (p.1 + p.2)
    rw [SameParity, Nat.even_iff]
    have hc : ((p.1 + p.2 : ℕ) : ℤ) = (p.1 : ℤ) + (p.2 : ℤ) := by push_cast; ring
    omega

/-- **The double time sum of the transition kernel is carried by the parity class
of the total.** -/
theorem sum_time_double_eq_filter (x y : Site d) (N : ℕ) (w : ℕ → ℕ → ℝ) :
    ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, w a b * Sandpile.heatKernel d (a + b) x y
      = ∑ p ∈ ((Finset.range N) ×ˢ (Finset.range N)).filter
          (fun p : ℕ × ℕ => SameParity (p.1 + p.2) x y),
          w p.1 p.2 * Sandpile.heatKernel d (p.1 + p.2) x y := by
  classical
  rw [← Finset.sum_product']
  refine (Finset.sum_filter_of_ne ?_).symm
  intro p _ hne
  refine sameParity_of_heatKernel_ne_zero (p.1 + p.2) x y ?_
  intro h0
  exact hne (by rw [h0, mul_zero])

end Sandpile.Support
