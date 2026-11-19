import Sandpile.External.RSW.QuasiCrossing
import Sandpile.External.RSW.BondWalk

/-!
# The quasi-crossing cascade cover

A wall whose scale-`m` path contains a scale-`k` subpath is also a scale-`k` wall.
Consequently a quasi-crossing either reaches the smaller scale or contains an open path
without such a subpath.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A walk contains a contiguous subpath of the designated KST scale. -/
def HasKSTSubpath (k : ℕ) {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b) : Prop :=
  ∃ (c d : Q) (q : (rectangleGraph Q).Walk c d), q.IsSubwalk p ∧ IsKSTPath k q

/-- The exceptional event contains an open `m`-path without any `k`-subpath. -/
def kstExceptionalPathEvent (n m k : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  let Q := centeredPlaneRectangle (n + 3 * (n / 12)) n
  {ω | ∃ (a b : Q) (p : (rectangleGraph Q).Walk a b),
    IsKSTPath m p ∧ ¬ HasKSTSubpath k p ∧ IsBondOpenWalk ω p}

/-- The exceptional path event is increasing. -/
theorem isUpperSet_kstExceptionalPathEvent (n m k : ℕ) :
    IsUpperSet (kstExceptionalPathEvent n m k) := by
  intro ω η hωη
  rintro ⟨a, b, p, hp, hbad, hopen⟩
  exact ⟨a, b, p, hp, hbad, hopen.mono hωη p⟩

/-- The exceptional path event is measurable. -/
theorem measurableSet_kstExceptionalPathEvent (n m k : ℕ) :
    MeasurableSet (kstExceptionalPathEvent n m k) := by
  let Q := centeredPlaneRectangle (n + 3 * (n / 12)) n
  let (a b : Q) : Countable ((rectangleGraph Q).Walk a b) :=
    SimpleGraph.Walk.support_injective.countable
  have hm (a b : Q) (p : (rectangleGraph Q).Walk a b) :
      MeasurableSet {ω : Sym2 (Site 2) → Bool |
        IsKSTPath m p ∧ ¬ HasKSTSubpath k p ∧ IsBondOpenWalk ω p} :=
    (MeasurableSet.const _).inter ((MeasurableSet.const _).inter (measurableSet_isBondOpenWalk p))
  change MeasurableSet {ω : Sym2 (Site 2) → Bool | ∃ (a b : Q)
    (p : (rectangleGraph Q).Walk a b),
      IsKSTPath m p ∧ ¬ HasKSTSubpath k p ∧ IsBondOpenWalk ω p}
  simpa only [ofPred_exists] using
    (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      MeasurableSet.iUnion fun p => hm a b p)

/-- A wall remains a wall at a smaller scale when its path contains a smaller subpath. -/
theorem kstWallEvent_of_subpaths (n m k : ℕ) (left : Bool)
    (ω : Sym2 (Site 2) → Bool) (hwall : ω ∈ kstWallEvent n m left)
    (hsub : ∀ {a b : centeredPlaneRectangle (n + 3 * (n / 12)) n}
      (p : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b),
      IsKSTPath m p → IsBondOpenWalk ω p → HasKSTSubpath k p) :
    ω ∈ kstWallEvent n k left := by
  obtain ⟨a, b, x, c, p, q, hp, hx, hc, hpo, hqo⟩ := hwall
  obtain ⟨a', b', p', hp'sub, hp'⟩ := hsub p hp hpo
  have ha' : a' ∈ p.support := hp'sub.support_subset p'.start_mem_support
  obtain ⟨r, hro, _⟩ := exists_openWalk_of_mem_support p hpo ha' hx
  exact ⟨a', b', a', c, p', r.append q, hp', p'.start_mem_support, hc,
    hpo.subwalk hp'sub, hro.append hqo⟩

/-- A quasi-crossing either reaches the smaller scale or has an exceptional path. -/
theorem kstQuasiCrossing_subset_smaller_union_exceptional (n m k : ℕ) :
    kstQuasiCrossingEvent n m ⊆
      kstQuasiCrossingEvent n k ∪ kstExceptionalPathEvent n m k := by
  classical
  intro ω hω
  by_cases hbad : ω ∈ kstExceptionalPathEvent n m k
  · exact Or.inr hbad
  · apply Or.inl
    have hsub {a b : centeredPlaneRectangle (n + 3 * (n / 12)) n}
        (p : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b)
        (hp : IsKSTPath m p) (hpo : IsBondOpenWalk ω p) : HasKSTSubpath k p := by
      by_contra hn
      exact hbad ⟨a, b, p, hp, hn, hpo⟩
    exact ⟨kstWallEvent_of_subpaths n m k true ω hω.1 hsub,
      kstWallEvent_of_subpaths n m k false ω hω.2 hsub⟩

end Sandpile.External.RSW
