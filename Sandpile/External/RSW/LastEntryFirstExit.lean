import Sandpile.External.RSW.FirstHitWalk
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Subpaths between two vertex sets

A walk from one set to a disjoint set contains a contiguous subwalk that leaves the
first set for the last time and reaches the second set for the first time.
-/

namespace Sandpile.External.RSW

/-- A walk between disjoint vertex sets has a subwalk meeting them only at its endpoints. -/
theorem exists_subwalk_between_disjoint_sets {V : Type*} {G : SimpleGraph V}
    (A B : V → Prop) [DecidablePred A] [DecidablePred B]
    (hdis : ∀ z, A z → ¬ B z) {a b : V} (p : G.Walk a b)
    (ha : A a) (hb : B b) :
    ∃ (c d : V) (q : G.Walk c d), q.IsSubwalk p ∧ A c ∧ B d ∧
      ∀ z ∈ q.support, (A z → z = c) ∧ (B z → z = d) := by
  obtain ⟨d, first, rest, hsplit, hd, hfirst⟩ :=
    exists_walk_first_hit B p (hdis a ha) hb
  obtain ⟨c, last, before, hsplit', hc, hlast⟩ :=
    exists_walk_first_hit A first.reverse (fun h => hdis d h hd) ha
  have hq : last.reverse.IsSubwalk p := by
    refine ⟨before.reverse, rest, ?_⟩
    rw [hsplit]
    have heq := congrArg SimpleGraph.Walk.reverse hsplit'
    simpa only [SimpleGraph.Walk.reverse_reverse, SimpleGraph.Walk.reverse_append] using
      congrArg (fun w => w.append rest) heq
  refine ⟨c, d, last.reverse, hq, hc, hd, ?_⟩
  intro z hz
  have hzlast : z ∈ last.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
  have hzfirst : z ∈ first.support := by
    have hzrev : z ∈ first.reverse.support := by
      rw [hsplit', SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl hzlast
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzrev
  constructor
  · intro hzA
    exact (hlast z hzlast).resolve_right (not_not_intro hzA)
  · intro hzB
    exact (hfirst z hzfirst).resolve_right (not_not_intro hzB)

end Sandpile.External.RSW
