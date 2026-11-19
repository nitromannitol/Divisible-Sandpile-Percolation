import Sandpile.Support.BlockSubwalk

/-!
# Gluing walks through a connecting walk

Two walks that each meet a third can be joined through it, without using vertices outside the
three original walks. This is the deterministic concatenation underlying crossing gluing.
-/

namespace Sandpile.External.RSW

/-- If two walks meet a third walk, their outer endpoints are joined by a walk supported on the
union of the three original walks. -/
theorem exists_walk_of_three_walks {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b c d e f x y : V} (p : G.Walk a b) (q : G.Walk c d) (r : G.Walk e f)
    (hx₁ : x ∈ p.support) (hx₂ : x ∈ q.support)
    (hy₁ : y ∈ q.support) (hy₂ : y ∈ r.support) :
    ∃ s : G.Walk a f, ∀ z ∈ s.support,
      z ∈ p.support ∨ z ∈ q.support ∨ z ∈ r.support := by
  obtain ⟨p', hp⟩ := exists_subwalk p p.start_mem_support hx₁
  obtain ⟨q', hq⟩ := exists_subwalk q hx₂ hy₁
  obtain ⟨r', hr⟩ := exists_subwalk r hy₂ r.end_mem_support
  refine ⟨(p'.append q').append r', ?_⟩
  intro z hz
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
    · exact Or.inl (hp z hz)
    · exact Or.inr (Or.inl (hq z hz))
  · exact Or.inr (Or.inr (hr z hz))

end Sandpile.External.RSW
