import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Trimming endpoints of a path

If every interior vertex lies in a set, a path with nonadjacent endpoints can
be restricted to that set by dropping whichever endpoints lie outside it.
-/

namespace Sandpile.External.RSW

/-- Trim endpoints outside a set from a simple path with nonadjacent endpoints. -/
theorem exists_subwalk_trim_endpoints {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (hne : a ≠ b) (hsep : ¬ G.Adj a b)
    (C : V → Prop) (hs : ∀ z ∈ p.support, z ≠ a → z ≠ b → C z) :
    ∃ (c d : V) (q : G.Walk c d), q.IsSubwalk p ∧
      ((C a ∧ c = a) ∨ (¬ C a ∧ G.Adj a c)) ∧
      ((C b ∧ d = b) ∨ (¬ C b ∧ G.Adj d b)) ∧
      (∀ z ∈ q.support, C z) := by
  classical
  have hnil : ¬ p.Nil := fun h => hne h.eq
  have htailnil : ¬ p.tail.Nil := by
    intro h
    exact hsep (h.eq ▸ p.adj_snd hnil)
  have htailSub := (SimpleGraph.Walk.isSubwalk_rfl p).tail
  have hdropSub := (SimpleGraph.Walk.isSubwalk_rfl p).dropLast
  have hmidSub := htailSub.dropLast
  have haTail : a ∉ p.tail.support := by
    have h := hp
    rw [← p.cons_tail_eq hnil, SimpleGraph.Walk.cons_isPath_iff] at h
    exact h.2
  have hbDrop : b ∉ p.dropLast.support := by
    have h := hp
    rw [← SimpleGraph.Walk.concat_dropLast (p.adj_penultimate hnil),
      SimpleGraph.Walk.isPath_concat] at h
    exact h.2
  have hbMid : b ∉ p.tail.dropLast.support := by
    have h := hp.tail
    rw [← SimpleGraph.Walk.concat_dropLast (p.tail.adj_penultimate htailnil),
      SimpleGraph.Walk.isPath_concat] at h
    exact h.2
  by_cases ha : C a
  · by_cases hb : C b
    · refine ⟨a, b, p, SimpleGraph.Walk.isSubwalk_rfl p, Or.inl ⟨ha, rfl⟩,
        Or.inl ⟨hb, rfl⟩, ?_⟩
      intro z hz
      by_cases hza : z = a
      · simpa only [hza] using ha
      by_cases hzb : z = b
      · simpa only [hzb] using hb
      exact hs z hz hza hzb
    · refine ⟨a, p.penultimate, p.dropLast, hdropSub, Or.inl ⟨ha, rfl⟩,
        Or.inr ⟨hb, p.adj_penultimate hnil⟩, ?_⟩
      intro z hz
      by_cases hza : z = a
      · simpa only [hza] using ha
      have hzb : z ≠ b := fun h => hbDrop (h ▸ hz)
      exact hs z (hdropSub.support_subset hz) hza hzb
  · by_cases hb : C b
    · refine ⟨p.snd, b, p.tail, htailSub, Or.inr ⟨ha, p.adj_snd hnil⟩,
        Or.inl ⟨hb, rfl⟩, ?_⟩
      intro z hz
      by_cases hzb : z = b
      · simpa only [hzb] using hb
      have hza : z ≠ a := fun h => haTail (h ▸ hz)
      exact hs z (htailSub.support_subset hz) hza hzb
    · refine ⟨p.snd, p.tail.penultimate, p.tail.dropLast, hmidSub,
        Or.inr ⟨ha, p.adj_snd hnil⟩, Or.inr ⟨hb, p.tail.adj_penultimate htailnil⟩, ?_⟩
      intro z hz
      have hzTail := (SimpleGraph.Walk.isSubwalk_rfl p.tail).dropLast.support_subset hz
      have hza : z ≠ a := fun h => haTail (h ▸ hzTail)
      have hzb : z ≠ b := fun h => hbMid (h ▸ hz)
      exact hs z (hmidSub.support_subset hz) hza hzb

end Sandpile.External.RSW
