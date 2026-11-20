import Sandpile.External.RSW.LastEntryFirstExit

/-!
# Connections between wired boundaries

A path between two disjoint boundary sets contains an interior path between their
respective entrance sets, provided the two boundary sets are not adjacent.
-/

namespace Sandpile.External.RSW

/-- Extract an interior path between the entrance sets of two wired boundaries. -/
theorem exists_interior_path_between_boundaries {V : Type*} {G : SimpleGraph V}
    (A B C U W : V → Prop) [DecidablePred A] [DecidablePred B]
    (E : Set (Sym2 V))
    (hdis : ∀ z, A z → ¬ B z)
    (hsep : ∀ x y, A x → B y → ¬ G.Adj x y)
    (hinner : ∀ z, ¬ A z → ¬ B z → C z)
    (hupper : ∀ x y, A x → ¬ A y → G.Adj x y → s(x, y) ∈ E → U y)
    (hlower : ∀ x y, B y → ¬ B x → G.Adj x y → s(x, y) ∈ E → W x)
    {a b : V} (p : G.Walk a b) (ha : A a) (hb : B b)
    (hp : ∀ e ∈ p.edges, e ∈ E) :
    ∃ (x y : V) (q : G.Walk x y), U x ∧ W y ∧
      (∀ z ∈ q.support, C z) ∧ ∀ e ∈ q.edges, e ∈ E := by
  classical
  have hp' : ∀ e ∈ p.bypass.edges, e ∈ E :=
    fun e he => hp e (p.edges_bypass_subset_edges he)
  obtain ⟨c, d, r, hrs, hc, hd, hrends⟩ :=
    exists_subwalk_between_disjoint_sets A B hdis p.bypass ha hb
  have hrpath : r.IsPath := SimpleGraph.Walk.isPath_of_isSubwalk hrs p.bypass_isPath
  have hropen : ∀ e ∈ r.edges, e ∈ E := fun e he => hp' e (hrs.edges_subset he)
  have hrnil : ¬ r.Nil := fun h => hdis c hc (h.eq ▸ hd)
  have hrtailnil : ¬ r.tail.Nil := by
    intro h
    exact hsep c d hc hd (h.eq ▸ r.adj_snd hrnil)
  have htailSub : r.tail.IsSubwalk r := (SimpleGraph.Walk.isSubwalk_rfl r).tail
  have hmidSub : r.tail.dropLast.IsSubwalk r := htailSub.dropLast
  have hfirst : s(c, r.snd) ∈ E := by
    apply hropen
    have he : r.edges = s(c, r.snd) :: r.tail.edges := by
      conv_lhs => rw [← r.cons_tail_eq hrnil]
      rfl
    rw [he]
    exact List.mem_cons_self
  have hlast : s(r.tail.penultimate, d) ∈ E := by
    apply hropen
    apply htailSub.edges_subset
    have he : r.tail.edges = r.tail.dropLast.edges.concat s(r.tail.penultimate, d) := by
      conv_lhs => rw [← SimpleGraph.Walk.concat_dropLast (r.tail.adj_penultimate hrtailnil)]
      exact SimpleGraph.Walk.edges_concat _ _
    rw [he]
    rw [List.concat_eq_append]
    exact List.mem_concat_self
  have htailpath : r.tail.IsPath := SimpleGraph.Walk.isPath_of_isSubwalk htailSub hrpath
  have hcnot : c ∉ r.tail.support := by
    have h := hrpath
    rw [← r.cons_tail_eq hrnil, SimpleGraph.Walk.cons_isPath_iff] at h
    exact h.2
  have hdnot : d ∉ r.tail.dropLast.support := by
    have h := htailpath
    rw [← SimpleGraph.Walk.concat_dropLast (r.tail.adj_penultimate hrtailnil),
      SimpleGraph.Walk.isPath_concat] at h
    exact h.2
  have hxA : ¬ A r.snd := by
    intro hx
    have he := (hrends r.snd (htailSub.support_subset r.tail.start_mem_support)).1 hx
    exact (r.adj_snd hrnil).ne he.symm
  have hyB : ¬ B r.tail.penultimate := by
    intro hy
    have he := (hrends r.tail.penultimate
      (hmidSub.support_subset r.tail.dropLast.end_mem_support)).2 hy
    exact (r.tail.adj_penultimate hrtailnil).ne he
  refine ⟨r.snd, r.tail.penultimate, r.tail.dropLast,
    hupper c r.snd hc hxA (r.adj_snd hrnil) hfirst,
    hlower _ d hd hyB (r.tail.adj_penultimate hrtailnil) hlast, ?_, ?_⟩
  · intro z hz
    have hzR := hmidSub.support_subset hz
    have hzTail := (SimpleGraph.Walk.isSubwalk_rfl r.tail).dropLast.support_subset hz
    apply hinner z
    · intro hA
      have he := (hrends z hzR).1 hA
      exact hcnot (he ▸ hzTail)
    · intro hB
      have he := (hrends z hzR).2 hB
      exact hdnot (he ▸ hz)
  · intro e he
    exact hropen e (hmidSub.edges_subset he)

end Sandpile.External.RSW
