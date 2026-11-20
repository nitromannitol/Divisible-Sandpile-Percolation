import Sandpile.External.RSW.QuasiCascadeCover

/-!
# Unoriented subpaths in quasi-crossings

A smaller path found in either traversal direction of a wall gives a wall at the
smaller scale.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- An open KST path without a smaller KST subpath in either direction. -/
def kstUnorientedExceptionalPathEvent (n m k : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  let Q := centeredPlaneRectangle (n + 3 * (n / 12)) n
  {ω | ∃ (a b : Q) (p : (rectangleGraph Q).Walk a b),
    IsKSTPath m p ∧ ¬ HasKSTSubpath k p ∧ ¬ HasKSTSubpath k p.reverse ∧
      IsBondOpenWalk ω p}

/-- The unoriented exceptional path event is increasing. -/
theorem isUpperSet_kstUnorientedExceptionalPathEvent (n m k : ℕ) :
    IsUpperSet (kstUnorientedExceptionalPathEvent n m k) := by
  intro ω η hωη
  rintro ⟨a, b, p, hp, hforward, hreverse, hopen⟩
  exact ⟨a, b, p, hp, hforward, hreverse, hopen.mono hωη p⟩

/-- The unoriented exceptional path event is measurable. -/
theorem measurableSet_kstUnorientedExceptionalPathEvent (n m k : ℕ) :
    MeasurableSet (kstUnorientedExceptionalPathEvent n m k) := by
  let Q := centeredPlaneRectangle (n + 3 * (n / 12)) n
  let (a b : Q) : Countable ((rectangleGraph Q).Walk a b) :=
    SimpleGraph.Walk.support_injective.countable
  have hm (a b : Q) (p : (rectangleGraph Q).Walk a b) :
      MeasurableSet {ω : Sym2 (Site 2) → Bool |
        IsKSTPath m p ∧ ¬ HasKSTSubpath k p ∧ ¬ HasKSTSubpath k p.reverse ∧
          IsBondOpenWalk ω p} :=
    (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      ((MeasurableSet.const _).inter (measurableSet_isBondOpenWalk p)))
  change MeasurableSet {ω : Sym2 (Site 2) → Bool | ∃ (a b : Q)
    (p : (rectangleGraph Q).Walk a b),
      IsKSTPath m p ∧ ¬ HasKSTSubpath k p ∧ ¬ HasKSTSubpath k p.reverse ∧
        IsBondOpenWalk ω p}
  simpa only [ofPred_exists] using
    (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      MeasurableSet.iUnion fun p => hm a b p)

/-- A wall remains a wall at a smaller scale if its path or its reverse contains a
smaller KST subpath. -/
theorem kstWallEvent_of_unoriented_subpaths (n m k : ℕ) (left : Bool)
    (ω : Sym2 (Site 2) → Bool) (hwall : ω ∈ kstWallEvent n m left)
    (hsub : ∀ {a b : centeredPlaneRectangle (n + 3 * (n / 12)) n}
      (p : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b),
      IsKSTPath m p → IsBondOpenWalk ω p →
        HasKSTSubpath k p ∨ HasKSTSubpath k p.reverse) :
    ω ∈ kstWallEvent n k left := by
  obtain ⟨a, b, x, c, p, q, hp, hx, hc, hpo, hqo⟩ := hwall
  rcases hsub p hp hpo with hforward | hreverse
  · obtain ⟨a', b', p', hp'sub, hp'⟩ := hforward
    have ha' : a' ∈ p.support := hp'sub.support_subset p'.start_mem_support
    obtain ⟨r, hro, _⟩ := exists_openWalk_of_mem_support p hpo ha' hx
    exact ⟨a', b', a', c, p', r.append q, hp', p'.start_mem_support, hc,
      hpo.subwalk hp'sub, hro.append hqo⟩
  · obtain ⟨a', b', p', hp'sub, hp'⟩ := hreverse
    have ha'rev : a' ∈ p.reverse.support := hp'sub.support_subset p'.start_mem_support
    have ha' : a' ∈ p.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using ha'rev
    obtain ⟨r, hro, _⟩ := exists_openWalk_of_mem_support p hpo ha' hx
    exact ⟨a', b', a', c, p', r.append q, hp', p'.start_mem_support, hc,
      hpo.reverse.subwalk hp'sub, hro.append hqo⟩

/-- A quasi-crossing reaches the smaller scale or contains an unoriented exceptional path. -/
theorem kstQuasiCrossing_subset_smaller_union_unoriented_exceptional (n m k : ℕ) :
    kstQuasiCrossingEvent n m ⊆
      kstQuasiCrossingEvent n k ∪ kstUnorientedExceptionalPathEvent n m k := by
  classical
  intro ω hω
  by_cases hbad : ω ∈ kstUnorientedExceptionalPathEvent n m k
  · exact Or.inr hbad
  · apply Or.inl
    have hsub {a b : centeredPlaneRectangle (n + 3 * (n / 12)) n}
        (p : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b)
        (hp : IsKSTPath m p) (hpo : IsBondOpenWalk ω p) :
        HasKSTSubpath k p ∨ HasKSTSubpath k p.reverse := by
      by_contra hn
      exact hbad ⟨a, b, p, hp, fun h => hn (Or.inl h), fun h => hn (Or.inr h), hpo⟩
    exact ⟨kstWallEvent_of_unoriented_subpaths n m k true ω hω.1 hsub,
      kstWallEvent_of_unoriented_subpaths n m k false ω hω.2 hsub⟩

end Sandpile.External.RSW
