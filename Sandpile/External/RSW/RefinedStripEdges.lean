import Sandpile.External.RSW.RefinedDualEdges

/-!
# Refined intersections inside a strip

A dual edge inside a strip that does not run along its top boundary can only
cross a primal edge contained in the strip.
-/

namespace Sandpile.External.RSW

/-- A crossed primal edge remains in the strip under the dual boundary condition. -/
theorem crossed_edge_in_strip (k : ℕ) {e f : Sym2 (Site 2)}
    (he : e ∈ (lattice 2).edgeSet)
    (hf : ∀ z ∈ f, -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k)
    (htop : ¬ ∀ z ∈ f, z 1 = k)
    (hm : refinedMidpoint 0 e = refinedMidpoint (fun _ => 1) f) :
    ∀ z ∈ e, -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k := by
  induction e using Sym2.ind with
  | h x y =>
    induction f using Sym2.ind with
    | h u v =>
      have hadj : (lattice 2).Adj x y := he
      have hcoord := congrFun hm 1
      simp only [refinedMidpoint, Sym2.lift_mk, Pi.zero_apply] at hcoord
      simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hf htop ⊢
      obtain hh | hh | hh | hh := lattice_two_adj_cases hadj <;> omega

end Sandpile.External.RSW
