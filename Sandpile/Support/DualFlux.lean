import Sandpile.Support.BoundaryParity
import Sandpile.Support.IntervalFlux

/-! # Dual Grid Mod-Two Flux and Connectivity

Mod-two conservation and bottom-to-top connectivity in a finite rectangular dual grid. Given
a `ZMod 2`-valued labelling `C` of the `(m+1) × (n+1)` primal vertices, `dualWeight` labels
each edge of the dual grid `dualGraph` by the mod-two sum of the two primal values it
separates, and `dual_flux_identity` records that summing this weight against any test
function `f` on the endpoints of every dual edge collapses, by telescoping along each row and
column, to a boundary term depending only on `f` at the two poles. When the labelling `C`
equals `1` on the left boundary column and `0` on the right, this identity forces some
nonzero-weight edge on every horizontal path from bottom pole to top pole, which
`dualGraph_bottom_reachable_top` turns into the stated bottom-to-top reachability in
`dualGraph`.
-/

open scoped BigOperators
namespace Sandpile

/-- The vertex set of the dual grid graph: two poles (`Bool`, for "bottom" and "top") plus
the `m × n` grid of interior dual cells. -/
abbrev dualVertex (m n : ℕ) := Bool ⊕ (Fin m × Fin n)

/-- The edge set of the dual grid graph: `m` rows of `n + 1` horizontal-type edges plus
`m + 1` columns of `n` vertical-type edges. -/
abbrev dualEdge (m n : ℕ) := (Fin m × Fin (n + 1)) ⊕ (Fin (m + 1) × Fin n)

/-- The source vertex of a dual edge, with the bottom pole `.inl false` as the source of the
first cell in each row or column and interior cells otherwise given by `Fin.cons`. -/
def dualSrc {m n : ℕ} : dualEdge m n → dualVertex m n
  | .inl p => Fin.cons (α := fun _ => dualVertex m n) (.inl false) (fun j => .inr (p.1, j)) p.2
  | .inr p => Fin.cons (α := fun _ => dualVertex m n) (.inl false) (fun i => .inr (i, p.2)) p.1

/-- The destination vertex of a dual edge, with the top pole `.inl true` as the destination
of the last cell in each row or column and interior cells otherwise given by `Fin.snoc`. -/
def dualDst {m n : ℕ} : dualEdge m n → dualVertex m n
  | .inl p => Fin.snoc (α := fun _ => dualVertex m n) (fun j => .inr (p.1, j)) (.inl true) p.2
  | .inr p => Fin.snoc (α := fun _ => dualVertex m n) (fun i => .inr (i, p.2)) (.inl true) p.1

/-- The mod-two weight of a dual edge from a primal labelling `C`: the sum of the two
adjacent primal values it separates. -/
def dualWeight {m n : ℕ} (C : Fin (m + 1) → Fin (n + 1) → ZMod 2) : dualEdge m n → ZMod 2
  | .inl p => C p.1.castSucc p.2 + C p.1.succ p.2
  | .inr p => C p.1 p.2.castSucc + C p.1 p.2.succ

/-- Summing the weighted endpoint values `dualWeight C e * (f (dualSrc e) + f (dualDst e))`
over every dual edge collapses, by telescoping each row and column, to `f` evaluated at the
two poles, provided `C` is identically `1` on the left boundary column and `0` on the
right. -/
lemma dual_flux_identity {m n : ℕ} (C : Fin (m + 1) → Fin (n + 1) → ZMod 2)
    (hleft : ∀ j, C 0 j = 1) (hright : ∀ j, C (Fin.last m) j = 0)
    (f : dualVertex m n → ZMod 2) :
    (∑ e : dualEdge m n, dualWeight C e * (f (dualSrc e) + f (dualDst e))) =
      f (.inl false) + f (.inl true) := by
  let I : ZMod 2 := ∑ i : Fin m, ∑ j : Fin n,
    ((C i.castSucc j.castSucc + C i.succ j.castSucc) +
      (C i.castSucc j.succ + C i.succ j.succ)) * f (.inr (i, j))
  have hH : (∑ i : Fin m, ∑ j : Fin (n + 1),
      dualWeight C (.inl (i, j)) * (f (dualSrc (.inl (i, j))) + f (dualDst (.inl (i, j))))) =
        f (.inl false) + f (.inl true) + I := by
    calc
      _ = ∑ i : Fin m, ((C i.castSucc 0 + C i.succ 0) * f (.inl false) +
          (C i.castSucc (Fin.last n) + C i.succ (Fin.last n)) * f (.inl true) +
          ∑ j : Fin n, ((C i.castSucc j.castSucc + C i.succ j.castSucc) +
            (C i.castSucc j.succ + C i.succ j.succ)) * f (.inr (i, j))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_interval_mapped_incidence (fun j => C i.castSucc j + C i.succ j)
          (.inl false : dualVertex m n) (.inl true) (fun j => .inr (i, j)) f
      _ = (∑ i : Fin m, (C i.castSucc 0 + C i.succ 0)) * f (.inl false) +
          (∑ i : Fin m, (C i.castSucc (Fin.last n) + C i.succ (Fin.last n))) * f (.inl true) +
            I := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, I]
      _ = _ := by
        rw [sum_interval_differences_mod_two (fun i => C i 0),
          sum_interval_differences_mod_two (fun i => C i (Fin.last n))]
        simp only [hleft, hright, add_zero, one_mul]
  have hV : (∑ i : Fin (m + 1), ∑ j : Fin n,
      dualWeight C (.inr (i, j)) * (f (dualSrc (.inr (i, j))) + f (dualDst (.inr (i, j))))) =
        I := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j : Fin n, ∑ i : Fin m,
          ((C i.castSucc j.castSucc + C i.castSucc j.succ) +
            (C i.succ j.castSucc + C i.succ j.succ)) * f (.inr (i, j)) := by
        apply Finset.sum_congr rfl
        intro j _
        have hh := sum_interval_mapped_incidence (fun i => C i j.castSucc + C i j.succ)
          (.inl false : dualVertex m n) (.inl true) (fun i => .inr (i, j)) f
        simpa only [dualWeight, dualSrc, dualDst, hleft, hright, CharTwo.add_self_eq_zero,
          zero_add, zero_mul] using hh
      _ = I := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [hH, hV, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The dual grid graph on `dualVertex m n`: two vertices are adjacent when some dual edge of
nonzero `dualWeight C` runs between them. -/
def dualGraph {m n : ℕ} (C : Fin (m + 1) → Fin (n + 1) → ZMod 2) : SimpleGraph (dualVertex m n) :=
  SimpleGraph.fromRel (fun a b => ∃ e : dualEdge m n, dualWeight C e ≠ 0 ∧
    dualSrc e = a ∧ dualDst e = b)

/-- Any dual edge of nonzero weight witnesses reachability in `dualGraph` between its source
and destination. -/
lemma dualGraph_edge_reachable {m n : ℕ} (C : Fin (m + 1) → Fin (n + 1) → ZMod 2)
    (e : dualEdge m n) (he : dualWeight C e ≠ 0) :
    (dualGraph C).Reachable (dualSrc e) (dualDst e) := by
  by_cases h : dualSrc e = dualDst e
  · rw [h]
  · apply SimpleGraph.Adj.reachable
    exact ⟨h, Or.inl ⟨e, he, rfl, rfl⟩⟩

/-- **Bottom-to-top connectivity of the dual grid.**  When the labelling `C` is `1` on the
left boundary column and `0` on the right, the bottom pole is reachable from the top pole in
`dualGraph C`, by the mod-two flux argument applied to `dual_flux_identity`. -/
lemma dualGraph_bottom_reachable_top {m n : ℕ} (C : Fin (m + 1) → Fin (n + 1) → ZMod 2)
    (hleft : ∀ j, C 0 j = 1) (hright : ∀ j, C (Fin.last m) j = 0) :
    (dualGraph C).Reachable (.inl false) (.inl true) := by
  exact reachable_of_mod_two_flux (dualGraph C) dualSrc dualDst (dualWeight C)
    (.inl false) (.inl true) (dualGraph_edge_reachable C) (dual_flux_identity C hleft hright)

end Sandpile
