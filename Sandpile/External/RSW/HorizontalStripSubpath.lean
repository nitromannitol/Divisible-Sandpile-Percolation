import Sandpile.External.RSW.LastEntryFirstExit
import Sandpile.Support.WalkRay

/-!
# Horizontal strip subpaths

A lattice path crossing two vertical lines contains a subpath confined to the
strip between them, with only its endpoints on the two boundary lines.
-/

namespace Sandpile.External.RSW

/-- Extract the last departure from the left line and the first arrival at the right line. -/
theorem exists_horizontal_strip_subpath {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b) (hp : p.IsPath) {L R : ℤ} (hLR : L < R)
    (ha : (a : Site 2) 0 ≤ L) (hb : R ≤ (b : Site 2) 0) :
    ∃ (c d : Q) (q : (rectangleGraph Q).Walk c d),
      q.IsSubwalk p ∧ q.IsPath ∧ (c : Site 2) 0 = L ∧ (d : Site 2) 0 = R ∧
      (∀ z ∈ q.support, L ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ R) ∧
      ∀ z ∈ q.support, ((z : Site 2) 0 = L → z = c) ∧
        ((z : Site 2) 0 = R → z = d) := by
  classical
  let A : Q → Prop := fun z => (z : Site 2) 0 ≤ L
  let B : Q → Prop := fun z => R ≤ (z : Site 2) 0
  obtain ⟨c, d, q, hsub, hc, hd, hends⟩ :=
    exists_subwalk_between_disjoint_sets A B (by intro z hz hz'; dsimp [A, B] at *; omega)
      p ha hb
  have hnil : ¬ q.Nil := by
    intro h
    have he : c = d := h.eq
    have := congrArg (fun z : Q => (z : Site 2) 0) he
    dsimp [A, B] at hc hd
    omega
  have hsnd : q.snd ∈ q.support :=
    (SimpleGraph.Walk.isSubwalk_rfl q).tail.support_subset q.tail.start_mem_support
  have hpen : q.penultimate ∈ q.support :=
    (SimpleGraph.Walk.isSubwalk_rfl q).dropLast.support_subset q.dropLast.end_mem_support
  have hsnd_not : ¬ A q.snd := by
    intro h
    exact (q.adj_snd hnil).ne ((hends q.snd hsnd).1 h).symm
  have hpen_not : ¬ B q.penultimate := by
    intro h
    exact (q.adj_penultimate hnil).ne ((hends q.penultimate hpen).2 h)
  have hadjfirst : (lattice 2).Adj (c : Site 2) (q.snd : Site 2) := q.adj_snd hnil
  have hadjlast : (lattice 2).Adj (q.penultimate : Site 2) (d : Site 2) := q.adj_penultimate hnil
  have hfirst := lattice_two_adj_cases hadjfirst
  have hlast := lattice_two_adj_cases hadjlast
  have hcL : (c : Site 2) 0 = L := by
    dsimp [A] at hc hsnd_not
    rcases hfirst with h | h | h | h <;> omega
  have hdR : (d : Site 2) 0 = R := by
    dsimp [B] at hd hpen_not
    rcases hlast with h | h | h | h <;> omega
  refine ⟨c, d, q, hsub, SimpleGraph.Walk.isPath_of_isSubwalk hsub hp, hcL, hdR, ?_, ?_⟩
  · intro z hz
    constructor
    · by_contra hn
      have heq : z = c := (hends z hz).1 (by dsimp [A]; omega)
      have := congrArg (fun x : Q => (x : Site 2) 0) heq
      omega
    · by_contra hn
      have heq : z = d := (hends z hz).2 (by dsimp [B]; omega)
      have := congrArg (fun x : Q => (x : Site 2) 0) heq
      omega
  · intro z hz
    exact ⟨fun h => (hends z hz).1 (by dsimp [A]; omega),
      fun h => (hends z hz).2 (by dsimp [B]; omega)⟩

end Sandpile.External.RSW
