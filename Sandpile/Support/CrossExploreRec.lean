import Sandpile.Support.CrossStoppingSet

/-! # Abstract exploration recursion

The exploration of Step 2 of `prop:fixed-scale-crossings` (`sandpile.tex:2255-2262`) in the
abstract:

  "We construct a rule which reveals the white noise in unit cubes, one at a time, choosing
   each new cube from the information already revealed, and stops after determining whether
   `E_R(θ)` occurs."

A rule is a function `next` which, from the set of indices already revealed, returns either the
next index to reveal or `none`; it is admissible when the decision is measurable for the
coordinates already revealed and never returns an index already revealed.  `exploreStep next n`
is the set revealed after `n` steps.

Two facts are proved.

* `isIndepStoppingSet_exploreStep`: the revealed set is a stopping set for the independent
  family, at every step.  The predecessor's refutation is what makes this delicate: a rule that
  decides whether to reveal a coordinate by LOOKING at that coordinate is not a stopping set and
  the martingale identity fails for it, so the recursion must read only the revealed cells,
  which is exactly what the `meas` clause of `IsExplorationRule` asks and what the induction
  uses.
* `exploreStep_stabilises`: after as many steps as there are indices the rule has stopped, so
  `exploreSet` is the set the rule reveals before stopping.

`indepBlockDecides_of_local` is the practical criterion for the second clause: an event the
revealed cells decide, in the sense that on `{S = A}` membership in it agrees with a set read
off the coordinates in `A`, is decided by the exploration.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

variable {Ω ι : Type*}

/-- An admissible exploration rule for the family `G`: from the set already revealed it names
the next index to reveal, or stops; the decision is measurable for the revealed coordinates and
never names an index already revealed. -/
structure IsExplorationRule (G : ι → MeasurableSpace Ω)
    (next : Finset ι → Ω → Option ι) : Prop where
  /-- The decision to reveal `i` next is read off the coordinates already revealed. -/
  meas : ∀ (A : Finset ι) (i : ι), MeasurableSet[indepAlg G (↑A : Set ι)] {ω | next A ω = some i}
  /-- The rule never names an index it has already revealed. -/
  fresh : ∀ (A : Finset ι) (ω : Ω) (i : ι), next A ω = some i → i ∉ A

/-- The set of indices revealed after `n` steps of the rule. -/
def exploreStep [DecidableEq ι] (next : Finset ι → Ω → Option ι) : ℕ → Ω → Finset ι
  | 0, _ => ∅
  | (n + 1), ω =>
      match next (exploreStep next n ω) ω with
      | none => exploreStep next n ω
      | some i => insert i (exploreStep next n ω)

/-- `exploreStep next 0` reveals nothing: the empty set, by definition. -/
@[simp] theorem exploreStep_zero [DecidableEq ι] (next : Finset ι → Ω → Option ι) (ω : Ω) :
    exploreStep next 0 ω = ∅ := rfl

/-- If the rule stops at the set revealed after `n` steps (`next ... = none`), the set
revealed after `n + 1` steps is unchanged. -/
theorem exploreStep_succ_of_none [DecidableEq ι] (next : Finset ι → Ω → Option ι) (n : ℕ)
    (ω : Ω) (h : next (exploreStep next n ω) ω = none) :
    exploreStep next (n + 1) ω = exploreStep next n ω := by
  show (match next (exploreStep next n ω) ω with
      | none => exploreStep next n ω
      | some i => insert i (exploreStep next n ω)) = exploreStep next n ω
  rw [h]

/-- If the rule names `i` next at the set revealed after `n` steps, the set revealed
after `n + 1` steps is that set with `i` inserted. -/
theorem exploreStep_succ_of_some [DecidableEq ι] (next : Finset ι → Ω → Option ι) (n : ℕ)
    (ω : Ω) {i : ι} (h : next (exploreStep next n ω) ω = some i) :
    exploreStep next (n + 1) ω = insert i (exploreStep next n ω) := by
  show (match next (exploreStep next n ω) ω with
      | none => exploreStep next n ω
      | some j => insert j (exploreStep next n ω)) = insert i (exploreStep next n ω)
  rw [h]

/-- The event that the rule has stopped is read off the revealed coordinates. -/
theorem measurableSet_next_none [Fintype ι] {G : ι → MeasurableSpace Ω}
    {next : Finset ι → Ω → Option ι} (h : IsExplorationRule G next) (A : Finset ι) :
    MeasurableSet[indepAlg G (↑A : Set ι)] {ω | next A ω = none} := by
  classical
  have hcompl : {ω : Ω | next A ω = none} = (⋃ i : ι, {ω : Ω | next A ω = some i})ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · intro hn i hi
      rw [hn] at hi
      simp at hi
    · intro hn
      cases hv : next A ω with
      | none => rfl
      | some i => exact absurd hv (hn i)
  rw [hcompl]
  exact (MeasurableSet.iUnion fun i => h.meas A i).compl

/-- **The revealed set is a stopping set.**  At every step, the event that the set revealed so
far is exactly `A` is decided by the coordinates in `A`. -/
theorem isIndepStoppingSet_exploreStep [Fintype ι] [DecidableEq ι] {G : ι → MeasurableSpace Ω}
    {next : Finset ι → Ω → Option ι} (h : IsExplorationRule G next) (n : ℕ) :
    IsIndepStoppingSet G (exploreStep next n) := by
  classical
  induction n with
  | zero =>
      intro A
      by_cases hA : A = ∅
      · have : {ω : Ω | exploreStep next 0 ω = A} = Set.univ := by
          ext ω; simp [hA]
        rw [this]
        exact @MeasurableSet.univ Ω (indepAlg G (↑A : Set ι))
      · have : {ω : Ω | exploreStep next 0 ω = A} = (∅ : Set Ω) := by
          ext ω
          simp only [exploreStep_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact fun hc => hA hc.symm
        rw [this]
        exact @MeasurableSet.empty Ω (indepAlg G (↑A : Set ι))
  | succ n ih =>
      intro A
      have hsplit : {ω : Ω | exploreStep next (n + 1) ω = A}
          = ({ω : Ω | exploreStep next n ω = A} ∩ {ω : Ω | next A ω = none})
            ∪ ⋃ i ∈ A, ({ω : Ω | exploreStep next n ω = A.erase i}
              ∩ {ω : Ω | next (A.erase i) ω = some i}) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion,
          exists_prop]
        constructor
        · intro hA
          cases hv : next (exploreStep next n ω) ω with
          | none =>
              have hstep := exploreStep_succ_of_none next n ω hv
              rw [hstep] at hA
              exact Or.inl ⟨hA, by rw [← hA]; exact hv⟩
          | some i =>
              have hstep := exploreStep_succ_of_some next n ω hv
              rw [hstep] at hA
              have hfresh : i ∉ exploreStep next n ω := h.fresh _ ω i hv
              have hiA : i ∈ A := by rw [← hA]; exact Finset.mem_insert_self i _
              have hbase : exploreStep next n ω = A.erase i := by
                rw [← hA, Finset.erase_insert hfresh]
              exact Or.inr ⟨i, hiA, hbase, by rw [← hbase]; exact hv⟩
        · rintro (⟨hbase, hnone⟩ | ⟨i, hiA, hbase, hsome⟩)
          · rw [exploreStep_succ_of_none next n ω (by rw [hbase]; exact hnone), hbase]
          · have hv : next (exploreStep next n ω) ω = some i := by rw [hbase]; exact hsome
            rw [exploreStep_succ_of_some next n ω hv, hbase, Finset.insert_erase hiA]
      rw [hsplit]
      refine MeasurableSet.union ((ih A).inter (measurableSet_next_none h A)) ?_
      refine MeasurableSet.biUnion (Finset.countable_toSet A) fun i hi => ?_
      have hsub : (↑(A.erase i) : Set ι) ⊆ (↑A : Set ι) := by
        intro j hj
        exact Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp hj))
      have hle := indepAlg_mono G hsub
      exact (hle _ (ih (A.erase i))).inter (hle _ (h.meas (A.erase i) i))

/-- After as many steps as there are indices, the rule has stopped. -/
theorem exploreStep_stabilises [Fintype ι] [DecidableEq ι] {G : ι → MeasurableSpace Ω}
    {next : Finset ι → Ω → Option ι} (h : IsExplorationRule G next) (ω : Ω) :
    next (exploreStep next (Fintype.card ι) ω) ω = none := by
  classical
  have hstep : ∀ n : ℕ, n ≤ (exploreStep next n ω).card
      ∨ next (exploreStep next n ω) ω = none := by
    intro n
    induction n with
    | zero => exact Or.inl (Nat.zero_le _)
    | succ n ih =>
        rcases ih with hcard | hnone
        · cases hv : next (exploreStep next n ω) ω with
          | none =>
              refine Or.inr ?_
              rw [exploreStep_succ_of_none next n ω hv]
              exact hv
          | some i =>
              refine Or.inl ?_
              rw [exploreStep_succ_of_some next n ω hv,
                Finset.card_insert_of_notMem (h.fresh _ ω i hv)]
              exact Nat.succ_le_succ hcard
        · refine Or.inr ?_
          rw [exploreStep_succ_of_none next n ω hnone]
          exact hnone
  rcases hstep (Fintype.card ι) with hcard | hnone
  · have huniv : exploreStep next (Fintype.card ι) ω = Finset.univ := by
      refine Finset.eq_univ_of_card _ ?_
      exact le_antisymm (Finset.card_le_univ _) hcard
    cases hv : next (exploreStep next (Fintype.card ι) ω) ω with
    | none => rfl
    | some i =>
        exact absurd (huniv ▸ Finset.mem_univ i) (h.fresh _ ω i hv)
  · exact hnone

/-- The set the rule reveals before stopping. -/
def exploreSet [Fintype ι] [DecidableEq ι] (next : Finset ι → Ω → Option ι) (ω : Ω) :
    Finset ι := exploreStep next (Fintype.card ι) ω

/-- `exploreSet next` (the set the rule reveals before stopping) is a stopping set for
the independent family `G`, specializing `isIndepStoppingSet_exploreStep` at the step
count `Fintype.card ι`. -/
theorem isIndepStoppingSet_exploreSet [Fintype ι] [DecidableEq ι] {G : ι → MeasurableSpace Ω}
    {next : Finset ι → Ω → Option ι} (h : IsExplorationRule G next) :
    IsIndepStoppingSet G (exploreSet next) :=
  isIndepStoppingSet_exploreStep h _

/-- **The practical criterion for an event the exploration decides.**  If on the event that the
revealed set is `A` membership in `E` agrees with a set read off the coordinates in `A`, then
the exploration decides `E`. -/
theorem indepBlockDecides_of_local {G : ι → MeasurableSpace Ω} {S : Ω → Finset ι}
    (hS : IsIndepStoppingSet G S) {E : Set Ω} (F : Finset ι → Set Ω)
    (hF : ∀ A : Finset ι, MeasurableSet[indepAlg G (↑A : Set ι)] (F A))
    (hEF : ∀ (A : Finset ι) (ω : Ω), S ω = A → (ω ∈ E ↔ ω ∈ F A)) :
    IndepBlockDecides G S E := by
  intro A
  have hrw : E ∩ {ω | S ω = A} = F A ∩ {ω | S ω = A} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hE, hSA⟩
      exact ⟨(hEF A ω hSA).mp hE, hSA⟩
    · rintro ⟨hF', hSA⟩
      exact ⟨(hEF A ω hSA).mpr hF', hSA⟩
  rw [hrw]
  exact (hF A).inter (hS A)

end Sandpile.Support
