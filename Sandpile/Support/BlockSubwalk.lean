import Sandpile.Support.BlockGeometry
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Subwalk extraction

Subwalk extraction: between any two sites on the support of a walk there is
a walk whose support is contained in the original one's.
-/

open scoped NNReal
noncomputable section
namespace Sandpile

/-- Between any two sites on the support of a walk there is a walk whose
support is contained in the original walk's support. -/
theorem exists_subwalk {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) {u v : V} (hu : u ∈ p.support) (hv : v ∈ p.support) :
    ∃ q : G.Walk u v, ∀ t ∈ q.support, t ∈ p.support := by
  induction p with
  | @nil x =>
    have hu' : u = x := List.mem_singleton.mp hu
    have hv' : v = x := List.mem_singleton.mp hv
    subst hu'
    subst hv'
    refine ⟨.nil, ?_⟩
    intro t ht
    simpa using ht
  | @cons a b w hab p ih =>
    rw [SimpleGraph.Walk.support_cons] at hu hv
    obtain rfl | hup : u = a ∨ u ∈ p.support := List.mem_cons.mp hu
    · obtain rfl | hvp : v = u ∨ v ∈ p.support := List.mem_cons.mp hv
      · refine ⟨.nil, ?_⟩
        intro t ht
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at ht
        rw [SimpleGraph.Walk.support_cons, List.mem_cons]
        exact Or.inl ht
      · refine ⟨.cons hab (p.takeUntil v hvp), ?_⟩
        intro t ht
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at ht
        rcases ht with rfl | ht
        · rw [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inl rfl
        · rw [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inr (p.support_takeUntil_subset_support hvp ht)
    · obtain hvp | hvp : v = a ∨ v ∈ p.support := List.mem_cons.mp hv
      · subst hvp
        refine ⟨(p.takeUntil u hup).reverse.append hab.symm.toWalk, ?_⟩
        intro t ht
        rw [SimpleGraph.Walk.mem_support_append_iff] at ht
        rcases ht with ht | ht
        · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at ht
          rw [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inr (p.support_takeUntil_subset_support hup ht)
        · simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil] at ht
          rcases List.mem_cons.mp ht with ht | ht
          · rw [SimpleGraph.Walk.support_cons, List.mem_cons]
            exact Or.inr (ht ▸ p.start_mem_support)
          · rw [SimpleGraph.Walk.support_cons, List.mem_cons]
            exact Or.inl (List.mem_singleton.mp ht)
      · obtain ⟨q, hq⟩ := ih hup hvp
        refine ⟨q, ?_⟩
        intro t ht
        rw [SimpleGraph.Walk.support_cons, List.mem_cons]
        exact Or.inr (hq t ht)

end Sandpile