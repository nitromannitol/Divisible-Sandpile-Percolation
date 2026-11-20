import Sandpile.External.RSW.DualCrossing
import LatticeProb.Vendor.FormalMathPercolation.Literature.RSWLemma

/-!
# First exit from a rectangle

A lattice walk starting inside a rectangle and reaching its top has an initial segment
ending on the top, left, or right side and remaining inside the rectangle.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- If no step source lies on a coordinate hyperplane, a walk starting above it stays
above it. -/
theorem apply_ge_of_darts {x y : LatticeModels.Site 2} (p : (LatticeModels.zdGraph 2).Walk x y)
    (i : Fin 2) (c : ℤ) (hx : c ≤ x i) (h : ∀ d ∈ p.darts, d.fst i ≠ c) :
    ∀ z ∈ p.support, c ≤ z i := by
  induction p with
  | nil =>
    intro z hz
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    rw [hz]
    exact hx
  | @cons x w y hadj p ih =>
    have hxc : x i ≠ c := h ⟨(x, w), hadj⟩ (by simp)
    have hw : c ≤ w i := by
      have hh := (zdGraph_adj_apply_le hadj i).2
      omega
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact ih hw (fun d hd => h d (by simp [hd])) z hz

/-- The initial segment up to the first top or side hit stays inside the rectangle. -/
theorem exists_first_rectangle_exit {L R B T : ℤ} {a b : Site 2}
    (p : (LatticeModels.zdGraph 2).Walk a b)
    (haL : L ≤ a 0) (haR : a 0 ≤ R) (haT : a 1 ≤ T) (hbT : T ≤ b 1)
    (hbottom : ∀ z ∈ p.support, B ≤ z 1) :
    ∃ (c : Site 2) (q : (LatticeModels.zdGraph 2).Walk a c),
      (c 0 = L ∨ c 0 = R ∨ c 1 = T) ∧
      (∀ z ∈ q.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T) ∧
      (∀ z ∈ q.support, z ∈ p.support) ∧ (∀ e ∈ q.edges, e ∈ p.edges) := by
  let O : Set (Site 2) := {z | z 0 = L ∨ z 0 = R ∨ z 1 = T}
  obtain ⟨z, hz, hzt⟩ := exists_mem_support_apply_eq p 1 T haT hbT
  obtain ⟨c, hc, q, hqs, hqe, hqd⟩ := exists_prefix_first_mem (O := O) p
    ⟨z, hz, Or.inr (Or.inr hzt)⟩
  have hL : ∀ z ∈ q.support, L ≤ z 0 :=
    apply_ge_of_darts q 0 L haL (fun d hd he => hqd d hd (Or.inl he))
  have hR : ∀ z ∈ q.support, z 0 ≤ R :=
    apply_le_of_darts q 0 R haR (fun d hd he => hqd d hd (Or.inr (Or.inl he)))
  have hT : ∀ z ∈ q.support, z 1 ≤ T :=
    apply_le_of_darts q 1 T haT (fun d hd he => hqd d hd (Or.inr (Or.inr he)))
  exact ⟨c, q, hc, fun z hz => ⟨hL z hz, hR z hz, hbottom z (hqs z hz), hT z hz⟩, hqs, hqe⟩

end Sandpile.External.RSW
