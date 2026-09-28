import Sandpile.Support.CrossSquare
import Sandpile.Support.CrossExploreRec
import Sandpile.Support.CrossUnion

/-! # The exploration rule of Step 2

The exploration rule of Step 2 of `prop:fixed-scale-crossings` (`sandpile.tex:2255-2262`),
written as a recursion on the cells it has already revealed.

The rule processes the unit squares whose closure meets the rectangle, one at a time.  A
square is DISCOVERED when it lies on the starting side of the rectangle, or when it neighbours
a point the exploration has already found to be joined to that side by a chain of short
segments on which the field stays at the level, every point of the chain sitting in a square
already processed.  Processing a square means revealing the cells of `ℤ^d` that carry the
field on that square and on its neighbours, one cell at a time.  The rule stops when every
discovered square has been processed.

The chains are indexed by the countable set `sampPts` of points of segments between admissible
vertices, so the discovered set is a countable union of events about single field values, each
of which the cells of the square carrying it already decide.  That is what makes the rule
admissible in the sense of `IsExplorationRule`, hence its revealed set a stopping set.
-/

open MeasureTheory ProbabilityTheory
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

namespace Sandpile.Support

attribute [local instance 0] Classical.propDecidable

/-- The points of segments between admissible vertices of the rectangle: a countable set
containing every point at which a chain event reads the field. -/
def sampPts (a b : Fin 2 → ℝ) : Set (Space 2) :=
  {p | ∃ v w : Space 2, VertexOK a b v ∧ VertexOK a b w ∧ ∃ q : ℚ, p = segPt v w (q : ℝ)}

/-- `sampPts a b` is countable, as the image of the countable set of pairs of admissible
vertices and rationals under `segPt`. -/
theorem countable_sampPts (a b : Fin 2 → ℝ) : (sampPts a b).Countable := by
  classical
  have hc : Countable {p : Space 2 // VertexOK a b p} := (countable_vertexOK a b).to_subtype
  have hsub : sampPts a b ⊆
      Set.range (fun t : {p : Space 2 // VertexOK a b p} × {p : Space 2 // VertexOK a b p} × ℚ =>
        segPt (t.1 : Space 2) (t.2.1 : Space 2) ((t.2.2 : ℚ) : ℝ)) := by
    rintro p ⟨v, w, hv, hw, q, rfl⟩
    exact ⟨(⟨v, hv⟩, ⟨w, hw⟩, q), rfl⟩
  exact Set.Countable.mono hsub (Set.countable_range _)

/-- The subtype `↥(sampPts a b)` is countable, transferred from `countable_sampPts`. -/
instance countable_sampPts_coe (a b : Fin 2 → ℝ) : Countable ↥(sampPts a b) :=
  (countable_sampPts a b).to_subtype

/-- Every rational-parameter point of a segment between two admissible vertices `v, w`
lies in `sampPts a b`, directly from the definition. -/
theorem segPt_mem_sampPts {a b : Fin 2 → ℝ} {v w : Space 2} (hv : VertexOK a b v)
    (hw : VertexOK a b w) (q : ℚ) : segPt v w (q : ℝ) ∈ sampPts a b :=
  ⟨v, w, hv, hw, q, rfl⟩

/-- A sub-segment of a segment is parametrised by the same segment. -/
theorem segPt_segPt (v w : Space 2) (q q' r : ℝ) :
    segPt (segPt v w q) (segPt v w q') r = segPt v w (q + r * (q' - q)) := by
  simp only [segPt]
  module

variable {Ω : Type} [MeasurableSpace Ω]

/-- One step of a discovered chain: neighbouring squares, a segment inside the rectangle, and
the field at least the level at every rational parameter of the segment. -/
def stepOK (a b : Fin 2 → ℝ) (lev : ℝ) (bf : Space 2 → Ω → ℝ) (ω : Ω) (p p' : Space 2) : Prop :=
  sqAdj (sqOf p) (sqOf p') ∧ segSet p p' ⊆ rectSet a b ∧
    ∀ q : ℚ, 0 ≤ q → q ≤ 1 → lev ≤ bf (segPt p p' (q : ℝ)) ω

/-- A point the exploration has discovered: the end of a chain of steps from the starting side
of the rectangle, every point of which lies in a square already processed. -/
def reachedPt (a b : Fin 2 → ℝ) (lev : ℝ) (bf : Space 2 → Ω → ℝ)
    (D : Finset (Sandpile.Site 2)) (ω : Ω) (p : Space 2) : Prop :=
  ∃ (k : ℕ) (v : Fin (k + 1) → ↥(sampPts a b)),
    ((v 0 : Space 2) 0 = a 0) ∧ ((v 0 : Space 2) ∈ rectSet a b) ∧
    (∀ j : Fin (k + 1), sqOf (v j : Space 2) ∈ D) ∧
    (∀ j : Fin k, stepOK a b lev bf ω (v j.castSucc : Space 2) (v j.succ : Space 2)) ∧
    (v (Fin.last k) : Space 2) = p

omit [MeasurableSpace Ω] in
/-- `reachedPt` is monotone in the set `D` of processed squares: a point reached using
only squares in `D` is still reached using any larger set `D'`. -/
theorem reachedPt_mono {a b : Fin 2 → ℝ} {lev : ℝ} {bf : Space 2 → Ω → ℝ}
    {D D' : Finset (Sandpile.Site 2)} (hD : D ⊆ D') {ω : Ω} {p : Space 2}
    (h : reachedPt a b lev bf D ω p) : reachedPt a b lev bf D' ω p := by
  obtain ⟨k, v, h0, hr, hD0, hs, hlast⟩ := h
  exact ⟨k, v, h0, hr, fun j => hD (hD0 j), hs, hlast⟩

/-- The squares the exploration has discovered: those on the starting side of the rectangle,
and the neighbours of the discovered points. -/
noncomputable def reachSq (a b : Fin 2 → ℝ) (lev : ℝ) (bf : Space 2 → Ω → ℝ)
    (D : Finset (Sandpile.Site 2)) (ω : Ω) : Finset (Sandpile.Site 2) :=
  (rectSq a b).filter
    (fun z => z 0 = ⌊a 0⌋ ∨ ∃ p : ↥(sampPts a b),
      reachedPt a b lev bf D ω (p : Space 2) ∧ sqAdj (sqOf (p : Space 2)) z)

omit [MeasurableSpace Ω] in
/-- Membership in `reachSq`, unfolded: `z` is discovered iff it lies among the squares of
the rectangle and either sits on the starting side or neighbours an already-reached
point. -/
theorem mem_reachSq {a b : Fin 2 → ℝ} {lev : ℝ} {bf : Space 2 → Ω → ℝ}
    {D : Finset (Sandpile.Site 2)} {ω : Ω} {z : Sandpile.Site 2} :
    z ∈ reachSq a b lev bf D ω ↔ z ∈ rectSq a b ∧
      (z 0 = ⌊a 0⌋ ∨ ∃ p : ↥(sampPts a b),
        reachedPt a b lev bf D ω (p : Space 2) ∧ sqAdj (sqOf (p : Space 2)) z) := by
  rw [reachSq, Finset.mem_filter]

omit [MeasurableSpace Ω] in
/-- Every discovered square lies among the squares of the rectangle. -/
theorem reachSq_subset {a b : Fin 2 → ℝ} {lev : ℝ} {bf : Space 2 → Ω → ℝ}
    {D : Finset (Sandpile.Site 2)} {ω : Ω} : reachSq a b lev bf D ω ⊆ rectSq a b :=
  fun _ hz => (mem_reachSq.mp hz).1

omit [MeasurableSpace Ω] in
/-- `reachSq` is monotone in the set of processed squares `D`, since `reachedPt` is
(`reachedPt_mono`). -/
theorem reachSq_mono {a b : Fin 2 → ℝ} {lev : ℝ} {bf : Space 2 → Ω → ℝ}
    {D D' : Finset (Sandpile.Site 2)} (hD : D ⊆ D') {ω : Ω} :
    reachSq a b lev bf D ω ⊆ reachSq a b lev bf D' ω := by
  intro z hz
  rw [mem_reachSq] at hz ⊢
  refine ⟨hz.1, ?_⟩
  rcases hz.2 with h | ⟨p, hp, hadj⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, reachedPt_mono hD hp, hadj⟩


/-! ### The cells the exploration reveals, and the rule itself -/

/-- The cells of the unit mesh of `ℤ^d` that the exploration of the rectangle can reveal. -/
abbrev cellIdx (d : ℕ) (a b : Fin 2 → ℝ) : Type := {x : Sandpile.Site d // x ∈ allSites d a b}

/-- The cells a square carries, as indices. -/
noncomputable def blockIdx (d : ℕ) (a b : Fin 2 → ℝ) (z : Sandpile.Site 2) :
    Finset (cellIdx d a b) :=
  Finset.univ.filter (fun i => (i : Sandpile.Site d) ∈ blockSites d z)

/-- Membership in `blockIdx d a b z`, unfolded: `i` indexes a cell of `blockSites d z`,
the cells the square `z` carries. -/
theorem mem_blockIdx {d : ℕ} {a b : Fin 2 → ℝ} {z : Sandpile.Site 2} {i : cellIdx d a b} :
    i ∈ blockIdx d a b z ↔ (i : Sandpile.Site d) ∈ blockSites d z := by
  rw [blockIdx, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- Every cell `x` that a square `z` of the rectangle carries has an index in
`blockIdx d a b z`, via `blockSites_subset_allSites`. -/
theorem exists_mem_blockIdx {d : ℕ} {a b : Fin 2 → ℝ} {z : Sandpile.Site 2}
    (hz : z ∈ rectSq a b) {x : Sandpile.Site d} (hx : x ∈ blockSites d z) :
    ∃ i ∈ blockIdx d a b z, (i : Sandpile.Site d) = x :=
  ⟨⟨x, blockSites_subset_allSites hz hx⟩, mem_blockIdx.mpr hx, rfl⟩

/-- The squares the exploration has finished processing. -/
noncomputable def doneSq (d : ℕ) (a b : Fin 2 → ℝ) (A : Finset (cellIdx d a b)) :
    Finset (Sandpile.Site 2) :=
  (rectSq a b).filter (fun z => blockIdx d a b z ⊆ A)

/-- Membership in `doneSq d a b A`, unfolded: `z` is processed iff it is a square of the
rectangle whose cell indices all lie in `A`. -/
theorem mem_doneSq {d : ℕ} {a b : Fin 2 → ℝ} {A : Finset (cellIdx d a b)}
    {z : Sandpile.Site 2} :
    z ∈ doneSq d a b A ↔ z ∈ rectSq a b ∧ blockIdx d a b z ⊆ A := by
  rw [doneSq, Finset.mem_filter]

/-- `doneSq` is monotone in the set of revealed cells `A`. -/
theorem doneSq_mono {d : ℕ} {a b : Fin 2 → ℝ} {A A' : Finset (cellIdx d a b)} (h : A ⊆ A') :
    doneSq d a b A ⊆ doneSq d a b A' := by
  intro z hz
  rw [mem_doneSq] at hz ⊢
  exact ⟨hz.1, hz.2.trans h⟩

/-- The next cell to reveal, from the squares already discovered and those already processed. -/
noncomputable def pickIdx (d : ℕ) (a b : Fin 2 → ℝ) (A : Finset (cellIdx d a b))
    (T : Finset (Sandpile.Site 2)) : Option (cellIdx d a b) :=
  if h : (T \ doneSq d a b A).Nonempty then
    (if h2 : (blockIdx d a b h.choose \ A).Nonempty then some h2.choose else none)
  else none

/-- The cell `pickIdx` names next has not already been revealed, since it is drawn from
`blockIdx d a b z \ A` for some `z`. -/
theorem pickIdx_fresh {d : ℕ} {a b : Fin 2 → ℝ} {A : Finset (cellIdx d a b)}
    {T : Finset (Sandpile.Site 2)} {i : cellIdx d a b} (h : pickIdx d a b A T = some i) :
    i ∉ A := by
  rw [pickIdx] at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      have : i = h2.choose := by
        simpa using h.symm
      rw [this]
      exact (Finset.mem_sdiff.mp h2.choose_spec).2
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- If `pickIdx` finds nothing left to reveal among the squares of `T`, then every square
of `T` (that lies in the rectangle) is already processed. -/
theorem subset_doneSq_of_pickIdx_none {d : ℕ} {a b : Fin 2 → ℝ} {A : Finset (cellIdx d a b)}
    {T : Finset (Sandpile.Site 2)} (hT : T ⊆ rectSq a b) (h : pickIdx d a b A T = none) :
    T ⊆ doneSq d a b A := by
  by_contra hc
  obtain ⟨z, hzT, hz⟩ := Finset.not_subset.mp hc
  have hne : (T \ doneSq d a b A).Nonempty := ⟨z, Finset.mem_sdiff.mpr ⟨hzT, hz⟩⟩
  rw [pickIdx, dif_pos hne] at h
  set z₀ := hne.choose with hz₀
  have hz₀mem : z₀ ∈ T \ doneSq d a b A := hne.choose_spec
  have hz₀T : z₀ ∈ rectSq a b := hT (Finset.mem_sdiff.mp hz₀mem).1
  have hz₀nd : ¬ (blockIdx d a b z₀ ⊆ A) := by
    intro hsub
    exact (Finset.mem_sdiff.mp hz₀mem).2 (mem_doneSq.mpr ⟨hz₀T, hsub⟩)
  obtain ⟨i, hi, hiA⟩ := Finset.not_subset.mp hz₀nd
  have hne2 : (blockIdx d a b z₀ \ A).Nonempty := ⟨i, Finset.mem_sdiff.mpr ⟨hi, hiA⟩⟩
  rw [dif_pos hne2] at h
  exact absurd h (by simp)

/-- The exploration rule: reveal the next cell of the first discovered square that is not yet
processed. -/
noncomputable def exploreNext (d : ℕ) (a b : Fin 2 → ℝ) (lev : ℝ) (bf : Space 2 → Ω → ℝ)
    (A : Finset (cellIdx d a b)) (ω : Ω) : Option (cellIdx d a b) :=
  pickIdx d a b A (reachSq a b lev bf (doneSq d a b A) ω)

omit [MeasurableSpace Ω] in
/-- The cell `exploreNext` names next has not already been revealed, from
`pickIdx_fresh`. -/
theorem exploreNext_fresh {d : ℕ} {a b : Fin 2 → ℝ} {lev : ℝ} {bf : Space 2 → Ω → ℝ}
    (A : Finset (cellIdx d a b)) (ω : Ω) (i : cellIdx d a b)
    (h : exploreNext d a b lev bf A ω = some i) : i ∉ A :=
  pickIdx_fresh h

omit [MeasurableSpace Ω] in
/-- When the rule stops, every discovered square has been processed. -/
theorem reachSq_subset_doneSq_of_none {d : ℕ} {a b : Fin 2 → ℝ} {lev : ℝ}
    {bf : Space 2 → Ω → ℝ} {A : Finset (cellIdx d a b)} {ω : Ω}
    (h : exploreNext d a b lev bf A ω = none) :
    reachSq a b lev bf (doneSq d a b A) ω ⊆ doneSq d a b A :=
  subset_doneSq_of_pickIdx_none reachSq_subset h


/-! ### The rule is admissible -/

/-- The field the exploration reads is decided, on each square, by the cells that square
carries. -/
def BlockMeasurable (d : ℕ) (a b : Fin 2 → ℝ) (G : cellIdx d a b → MeasurableSpace Ω)
    (bf : Space 2 → Ω → ℝ) : Prop :=
  ∀ z : Sandpile.Site 2, z ∈ rectSq a b → ∀ u : Space 2, sqAdj (sqOf u) z →
    Measurable[indepAlg G (↑(blockIdx d a b z))] (bf u)

variable {d : ℕ} {a b : Fin 2 → ℝ} {lev : ℝ} {bf : Space 2 → Ω → ℝ}
  {G : cellIdx d a b → MeasurableSpace Ω}

omit [MeasurableSpace Ω] in
/-- The superlevel event `{ω | lev ≤ bf u ω}` at a point `u` of an already-processed
square `z` is decided by the revealed cells `A`, via `BlockMeasurable` and monotonicity
of `indepAlg`. -/
theorem measurableSet_le_bf (hm : BlockMeasurable d a b G bf) {A : Finset (cellIdx d a b)}
    {z : Sandpile.Site 2} (hz : z ∈ doneSq d a b A) {u : Space 2} (hu : sqAdj (sqOf u) z) :
    MeasurableSet[indepAlg G (↑A : Set (cellIdx d a b))] {ω | lev ≤ bf u ω} := by
  rw [mem_doneSq] at hz
  have hsub : (↑(blockIdx d a b z) : Set (cellIdx d a b)) ⊆ (↑A : Set (cellIdx d a b)) := by
    intro i hi
    exact Finset.mem_coe.mpr (hz.2 (Finset.mem_coe.mp hi))
  have hmeas : Measurable[indepAlg G (↑A : Set (cellIdx d a b))] (bf u) :=
    (hm z hz.1 u hu).mono (indepAlg_mono G hsub) le_rfl
  exact measurableSet_le measurable_const hmeas

omit [MeasurableSpace Ω] in
/-- The event that `p` and `p'` form one admissible step (`stepOK`) is decided by the
revealed cells `A`: it splits on the geometric side conditions, and the level condition
becomes a countable intersection over rationals, each decided by `measurableSet_le_bf`. -/
theorem measurableSet_stepOK (hm : BlockMeasurable d a b G bf) {A : Finset (cellIdx d a b)}
    {p p' : Space 2} (hp : sqOf p ∈ doneSq d a b A) :
    MeasurableSet[indepAlg G (↑A : Set (cellIdx d a b))] {ω | stepOK a b lev bf ω p p'} := by
  by_cases hgeom : sqAdj (sqOf p) (sqOf p') ∧ segSet p p' ⊆ rectSet a b
  · have hrw : {ω | stepOK a b lev bf ω p p'}
        = ⋂ q : ℚ, {ω | 0 ≤ q → q ≤ 1 → lev ≤ bf (segPt p p' (q : ℝ)) ω} := by
      ext ω
      simp only [stepOK, Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h q => h.2.2 q, fun h => ⟨hgeom.1, hgeom.2, fun q => h q⟩⟩
    rw [hrw]
    refine MeasurableSet.iInter fun q => ?_
    by_cases hq : 0 ≤ q ∧ q ≤ 1
    · have hset : {ω | 0 ≤ q → q ≤ 1 → lev ≤ bf (segPt p p' (q : ℝ)) ω}
          = {ω | lev ≤ bf (segPt p p' (q : ℝ)) ω} := by
        ext ω; simp [hq.1, hq.2]
      rw [hset]
      refine measurableSet_le_bf hm hp ?_
      refine sqAdj_segPt hgeom.1 (q : ℝ) ?_ ?_
      · exact_mod_cast hq.1
      · exact_mod_cast hq.2
    · have hset : {ω | 0 ≤ q → q ≤ 1 → lev ≤ bf (segPt p p' (q : ℝ)) ω}
          = (Set.univ : Set Ω) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h1 h2
        exact absurd ⟨h1, h2⟩ hq
      rw [hset]
      exact @MeasurableSet.univ Ω (indepAlg G _)
  · have hrw : {ω | stepOK a b lev bf ω p p'} = (∅ : Set Ω) := by
      ext ω
      simp only [stepOK, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hgeom ⟨h.1, h.2.1⟩
    rw [hrw]
    exact @MeasurableSet.empty Ω (indepAlg G _)

omit [MeasurableSpace Ω] in
/-- The event that `p` is reached using the processed squares of `doneSq d a b A` is
decided by the revealed cells `A`: it is a countable union over chain lengths and vertex
choices of a finite intersection of `stepOK` events, each decided by
`measurableSet_stepOK`. -/
theorem measurableSet_reachedPt (hm : BlockMeasurable d a b G bf) {A : Finset (cellIdx d a b)}
    (p : Space 2) :
    MeasurableSet[indepAlg G (↑A : Set (cellIdx d a b))]
      {ω | reachedPt a b lev bf (doneSq d a b A) ω p} := by
  classical
  have hrw : {ω | reachedPt a b lev bf (doneSq d a b A) ω p}
      = ⋃ (k : ℕ), ⋃ (v : Fin (k + 1) → ↥(sampPts a b)),
          {ω | (((v 0 : Space 2) 0 = a 0) ∧ ((v 0 : Space 2) ∈ rectSet a b) ∧
              (∀ j : Fin (k + 1), sqOf (v j : Space 2) ∈ doneSq d a b A) ∧
              (v (Fin.last k) : Space 2) = p) ∧
            (∀ j : Fin k, stepOK a b lev bf ω (v j.castSucc : Space 2) (v j.succ : Space 2))} := by
    ext ω
    simp only [reachedPt, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨k, v, h0, hr, hD, hs, hlast⟩
      exact ⟨k, v, ⟨h0, hr, hD, hlast⟩, hs⟩
    · rintro ⟨k, v, ⟨h0, hr, hD, hlast⟩, hs⟩
      exact ⟨k, v, h0, hr, hD, hs, hlast⟩
  rw [hrw]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun v => ?_
  by_cases hcond : ((v 0 : Space 2) 0 = a 0) ∧ ((v 0 : Space 2) ∈ rectSet a b) ∧
      (∀ j : Fin (k + 1), sqOf (v j : Space 2) ∈ doneSq d a b A) ∧
      (v (Fin.last k) : Space 2) = p
  · have hset : {ω | (((v 0 : Space 2) 0 = a 0) ∧ ((v 0 : Space 2) ∈ rectSet a b) ∧
          (∀ j : Fin (k + 1), sqOf (v j : Space 2) ∈ doneSq d a b A) ∧
          (v (Fin.last k) : Space 2) = p) ∧
        (∀ j : Fin k, stepOK a b lev bf ω (v j.castSucc : Space 2) (v j.succ : Space 2))}
        = ⋂ j : Fin k, {ω | stepOK a b lev bf ω (v j.castSucc : Space 2) (v j.succ : Space 2)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h j => h.2 j, fun h => ⟨hcond, fun j => h j⟩⟩
    rw [hset]
    exact MeasurableSet.iInter fun j => measurableSet_stepOK hm (hcond.2.2.1 j.castSucc)
  · have hset : {ω | (((v 0 : Space 2) 0 = a 0) ∧ ((v 0 : Space 2) ∈ rectSet a b) ∧
          (∀ j : Fin (k + 1), sqOf (v j : Space 2) ∈ doneSq d a b A) ∧
          (v (Fin.last k) : Space 2) = p) ∧
        (∀ j : Fin k, stepOK a b lev bf ω (v j.castSucc : Space 2) (v j.succ : Space 2))}
        = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hcond h.1
    rw [hset]
    exact @MeasurableSet.empty Ω (indepAlg G _)

omit [MeasurableSpace Ω] in
/-- Membership of a square `z` in the discovered set `reachSq a b lev bf (doneSq d a b A)`
is decided by the revealed cells `A`: it is trivial if `z` sits on the starting side, and
otherwise a countable union over sample points of `measurableSet_reachedPt` events. -/
theorem measurableSet_mem_reachSq (hm : BlockMeasurable d a b G bf)
    {A : Finset (cellIdx d a b)} (z : Sandpile.Site 2) :
    MeasurableSet[indepAlg G (↑A : Set (cellIdx d a b))]
      {ω | z ∈ reachSq a b lev bf (doneSq d a b A) ω} := by
  classical
  by_cases hz : z ∈ rectSq a b
  · by_cases hside : z 0 = ⌊a 0⌋
    · have hset : {ω | z ∈ reachSq a b lev bf (doneSq d a b A) ω} = (Set.univ : Set Ω) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, mem_reachSq]
        exact ⟨hz, Or.inl hside⟩
      rw [hset]
      exact @MeasurableSet.univ Ω (indepAlg G _)
    · have hset : {ω | z ∈ reachSq a b lev bf (doneSq d a b A) ω}
          = ⋃ p : ↥(sampPts a b), {ω | reachedPt a b lev bf (doneSq d a b A) ω (p : Space 2) ∧
              sqAdj (sqOf (p : Space 2)) z} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, mem_reachSq]
        constructor
        · rintro ⟨-, h | ⟨p, hp⟩⟩
          · exact absurd h hside
          · exact ⟨p, hp⟩
        · rintro ⟨p, hp⟩
          exact ⟨hz, Or.inr ⟨p, hp⟩⟩
      rw [hset]
      refine MeasurableSet.iUnion fun p => ?_
      by_cases hadj : sqAdj (sqOf (p : Space 2)) z
      · have h2 : {ω | reachedPt a b lev bf (doneSq d a b A) ω (p : Space 2) ∧
            sqAdj (sqOf (p : Space 2)) z}
            = {ω | reachedPt a b lev bf (doneSq d a b A) ω (p : Space 2)} := by
          ext ω; simp [hadj]
        rw [h2]
        exact measurableSet_reachedPt hm _
      · have h2 : {ω | reachedPt a b lev bf (doneSq d a b A) ω (p : Space 2) ∧
            sqAdj (sqOf (p : Space 2)) z} = (∅ : Set Ω) := by
          ext ω; simp [hadj]
        rw [h2]
        exact @MeasurableSet.empty Ω (indepAlg G _)
  · have hset : {ω | z ∈ reachSq a b lev bf (doneSq d a b A) ω} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, mem_reachSq]
      exact fun h => hz h.1
    rw [hset]
    exact @MeasurableSet.empty Ω (indepAlg G _)

omit [MeasurableSpace Ω] in
/-- The event that the discovered set equals a fixed finite set `T` is decided by the
revealed cells `A`, as a finite intersection of the membership and non-membership events
of `measurableSet_mem_reachSq`. -/
theorem measurableSet_reachSq_eq (hm : BlockMeasurable d a b G bf)
    {A : Finset (cellIdx d a b)} (T : Finset (Sandpile.Site 2)) :
    MeasurableSet[indepAlg G (↑A : Set (cellIdx d a b))]
      {ω | reachSq a b lev bf (doneSq d a b A) ω = T} := by
  classical
  by_cases hT : T ⊆ rectSq a b
  · have hset : {ω | reachSq a b lev bf (doneSq d a b A) ω = T}
        = (⋂ z ∈ T, {ω | z ∈ reachSq a b lev bf (doneSq d a b A) ω}) ∩
          (⋂ z ∈ rectSq a b, ⋂ _ : z ∉ T, {ω | z ∈ reachSq a b lev bf (doneSq d a b A) ω}ᶜ) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_compl_iff]
      constructor
      · rintro rfl
        exact ⟨fun z hz => hz, fun z _ hz => hz⟩
      · rintro ⟨h1, h2⟩
        refine Finset.ext fun z => ⟨fun hz => ?_, fun hz => h1 z hz⟩
        by_contra hzT
        exact h2 z (reachSq_subset hz) hzT hz
    rw [hset]
    refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSet.biInter (Finset.countable_toSet T)
        fun z _ => measurableSet_mem_reachSq hm z
    · refine MeasurableSet.biInter (Finset.countable_toSet (rectSq a b)) fun z _ => ?_
      refine MeasurableSet.iInter fun _ => ?_
      exact (measurableSet_mem_reachSq hm z).compl
  · have hset : {ω | reachSq a b lev bf (doneSq d a b A) ω = T} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro rfl
      exact hT reachSq_subset
    rw [hset]
    exact @MeasurableSet.empty Ω (indepAlg G _)

omit [MeasurableSpace Ω] in
/-- **The rule of Step 2 is an admissible exploration rule**: it names a fresh cell, and its
decision is read off the cells it has already revealed. -/
theorem isExplorationRule_exploreNext (hm : BlockMeasurable d a b G bf) :
    IsExplorationRule G (exploreNext d a b lev bf) := by
  classical
  refine ⟨?_, fun A ω i h => exploreNext_fresh A ω i h⟩
  intro A i
  have hset : {ω | exploreNext d a b lev bf A ω = some i}
      = ⋃ T ∈ ((rectSq a b).powerset.filter (fun T => pickIdx d a b A T = some i)),
          {ω | reachSq a b lev bf (doneSq d a b A) ω = T} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter,
      Finset.mem_powerset, exists_prop]
    constructor
    · intro h
      exact ⟨reachSq a b lev bf (doneSq d a b A) ω, ⟨reachSq_subset, h⟩, rfl⟩
    · rintro ⟨T, ⟨-, hp⟩, hrw⟩
      rw [exploreNext, hrw]
      exact hp
  rw [hset]
  exact MeasurableSet.biUnion (Finset.countable_toSet _)
    fun T _ => measurableSet_reachSq_eq hm T

omit [MeasurableSpace Ω] in
/-- The field the exploration computes from the cells it has revealed satisfies the
measurability the rule needs. -/
theorem blockMeasurable_blockField {W : (Space d → ℝ) → Ω → ℝ} (hd : d = 2 ∨ d = 3)
    (a b : Fin 2 → ℝ) :
    BlockMeasurable d a b
      (fun i : cellIdx d a b => noiseBlockAlg W (cell d 1 (i : Sandpile.Site d)))
      (blockField d W) := by
  intro z hz u hu
  refine measurable_blockField hd (fun i : cellIdx d a b => (i : Sandpile.Site d))
    (blockIdx d a b z) u ?_
  intro x hx
  exact exists_mem_blockIdx hz (nearSites_subset_blockSites hu hx)

end Sandpile.Support
