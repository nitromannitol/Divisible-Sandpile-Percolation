import Sandpile.Support.CrossVertex

/-!
# The chain-event union and the two-sided crossing estimate

The countable union of the chain events, and the two-sided estimate it gives for
the crossing probability of an almost surely continuous planar field.

The chains with admissible vertices of `Sandpile/Support/CrossVertex.lean` form
a countable type `VertexChain`, a number of segments together with that many
admissible vertices; `crossApprox` is the union, over the chains that lie in the
rectangle and join its two opposite sides, of the events `pathEvent` of
`Sandpile/Support/CrossPath.lean`.  It is a countable union of measurable sets,
hence measurable, and it is an event about countably many values of the field.

The two estimates are

  `P (crossApprox … l) ≤ P {crossing at level l}`      (`measure_crossApprox_le_crossing`)
  `P {crossing at level l} ≤ P (crossApprox … (l - ε))` (`measure_crossing_le_crossApprox`)

for every `ε > 0`, the crossing probability being the outer measure of the
crossing event, which need not be measurable.  They bracket that outer measure
between the measures of two genuine events, at two levels a distance `ε` apart.
The bracket is not a squeeze at one level: an approximating chain at level
`l - ε` need not survive as `ε → 0`, so what this gives is the continuity of the
crossing probability in the level wherever the level is a continuity point, and
in every case a lower bound at the level the paper needs, which is what
`prop:fixed-scale-crossings` asks for.

This is the vocabulary a restatement of the continuum crossing comparison has to
be given in; `Sandpile/Support/CrossVacuity.lean` records why the statement on
the space of all planar functions cannot be.
-/

open MeasureTheory Set

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A point of the plane is the point built from its two coordinates. -/
theorem eq_hSeg_self (p : Sandpile.Continuum.Space 2) : p = hSeg (p 1) (p 0) := by
  ext k
  fin_cases k
  · exact (hSeg_apply_zero (p 1) (p 0)).symm
  · exact (hSeg_apply_one (p 1) (p 0)).symm

/-- There are countably many admissible vertices. -/
theorem countable_vertexOK (a b : Fin 2 → ℝ) :
    {p : Sandpile.Continuum.Space 2 | VertexOK a b p}.Countable := by
  have hQ : ∀ k : Fin 2, ((Set.range ((↑) : ℚ → ℝ)) ∪ {a k, b k}).Countable :=
    fun k => (Set.countable_range _).union ((Set.countable_singleton (b k)).insert (a k))
  have hsub : {p : Sandpile.Continuum.Space 2 | VertexOK a b p} ⊆
      (fun xy : ℝ × ℝ => hSeg xy.2 xy.1) ''
        (((Set.range ((↑) : ℚ → ℝ)) ∪ {a 0, b 0}) ×ˢ
          ((Set.range ((↑) : ℚ → ℝ)) ∪ {a 1, b 1})) := by
    intro p hp
    refine ⟨(p 0, p 1), ⟨?_, ?_⟩, (eq_hSeg_self p).symm⟩
    · rcases hp 0 with ⟨q, hq⟩ | h | h
      · exact Or.inl ⟨q, hq.symm⟩
      · exact Or.inr (by simp [h])
      · exact Or.inr (by simp [h])
    · rcases hp 1 with ⟨q, hq⟩ | h | h
      · exact Or.inl ⟨q, hq.symm⟩
      · exact Or.inr (by simp [h])
      · exact Or.inr (by simp [h])
  exact Set.Countable.mono hsub (((hQ 0).prod (hQ 1)).image _)

/-- A chain of admissible vertices: a number of segments and the vertices. -/
abbrev VertexChain (a b : Fin 2 → ℝ) : Type :=
  Σ m : ℕ, Fin (m + 2) → {p : Sandpile.Continuum.Space 2 // VertexOK a b p}

/-- `VertexChain a b` is countable: it is a sigma type over `ℕ` of functions into the
countable set of admissible vertices (`countable_vertexOK`). -/
instance countable_vertexChain (a b : Fin 2 → ℝ) : Countable (VertexChain a b) :=
  have : Countable {p : Sandpile.Continuum.Space 2 // VertexOK a b p} :=
    (countable_vertexOK a b).to_subtype
  inferInstance

/-- The chain read as a sequence of plane points. -/
noncomputable def chainFun {a b : Fin 2 → ℝ} (ch : VertexChain a b) :
    ℕ → Sandpile.Continuum.Space 2 :=
  fun j => if h : j < ch.1 + 2 then (ch.2 ⟨j, h⟩ : Sandpile.Continuum.Space 2) else 0

/-- Unfolds `chainFun` on an explicit chain `⟨m, f⟩` at an index within range. -/
theorem chainFun_apply {a b : Fin 2 → ℝ} (m : ℕ)
    (f : Fin (m + 2) → {p : Sandpile.Continuum.Space 2 // VertexOK a b p})
    (j : ℕ) (hj : j < m + 2) :
    chainFun (⟨m, f⟩ : VertexChain a b) j = (f ⟨j, hj⟩ : Sandpile.Continuum.Space 2) := by
  simp [chainFun, hj]

/-- The chain set depends only on the vertices actually used. -/
theorem pathSet_congr (n : ℕ) (v w : ℕ → Sandpile.Continuum.Space 2)
    (h : ∀ j ≤ n, v j = w j) : pathSet n v = pathSet n w := by
  unfold pathSet
  refine Set.iUnion₂_congr fun j hj => ?_
  have hjn : j < n := Finset.mem_range.mp hj
  rw [h j (le_of_lt hjn), h (j + 1) hjn]

/-- A chain that lies in the rectangle and joins its two opposite sides. -/
def GoodChain (a b : Fin 2 → ℝ) (i : Fin 2) (ch : VertexChain a b) : Prop :=
  pathSet (ch.1 + 1) (chainFun ch) ⊆ rectSet a b ∧
    chainFun ch 0 i = a i ∧ chainFun ch (ch.1 + 1) i = b i

/-- The union of the chain events over the chains that cross the rectangle. -/
noncomputable def crossApprox {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) : Set Ω :=
  ⋃ ch : {ch : VertexChain a b // GoodChain a b i ch},
    pathEvent X l (ch.1.1 + 1) (chainFun ch.1)

/-- A countable union of measurable events. -/
theorem measurableSet_crossApprox {Ω : Type*} [MeasurableSpace Ω]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) : MeasurableSet (crossApprox X a b i l) :=
  MeasurableSet.iUnion fun _ => measurableSet_pathEvent hX _ _ _

/-- Every chain event forces a crossing, on the continuity event. -/
theorem crossApprox_inter_subset_crossing {Ω : Type*} [MeasurableSpace Ω]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {l : ℝ} :
    crossApprox X a b i l ∩ {ω | Continuous fun u => X u ω}
      ⊆ {ω | Crosses a b i {u | l ≤ X u ω}} := by
  rintro ω ⟨hω, hc⟩
  obtain ⟨ch, hch⟩ := Set.mem_iUnion.mp hω
  exact pathEvent_inter_subset_crossing ch.1.1 (chainFun ch.1) ch.2.1 ch.2.2.1 ch.2.2.2 ⟨hch, hc⟩

/-- Every crossing is carried by an admissible chain at a level lower by `ε`. -/
theorem crossing_inter_subset_crossApprox {Ω : Type*} [MeasurableSpace Ω]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {l ε : ℝ}
    (ha0 : a 0 < b 0) (ha1 : a 1 < b 1) (hε : 0 < ε) :
    {ω | Crosses a b i {u | l ≤ X u ω}} ∩ {ω | Continuous fun u => X u ω}
      ⊆ crossApprox X a b i (l - ε) := by
  rintro ω ⟨hcross, hc⟩
  obtain ⟨m, v, hrect, hlev, hs, he, hOK⟩ :=
    exists_vertex_path_of_crosses hc ha0 ha1 hε hcross
  set f : Fin (m + 2) → {p : Sandpile.Continuum.Space 2 // VertexOK a b p} :=
    fun j => ⟨v j, hOK j (by omega)⟩ with hf
  have hcf : ∀ j ≤ m + 1, chainFun (⟨m, f⟩ : VertexChain a b) j = v j := by
    intro j hj
    rw [chainFun_apply m f j (by omega)]
  have hps : pathSet (m + 1) (chainFun (⟨m, f⟩ : VertexChain a b)) = pathSet (m + 1) v :=
    pathSet_congr _ _ _ hcf
  have hgood : GoodChain a b i (⟨m, f⟩ : VertexChain a b) := by
    refine ⟨by rw [hps]; exact hrect, ?_, ?_⟩
    · rw [hcf 0 (by omega)]; exact hs
    · rw [hcf (m + 1) (by omega)]; exact he
  refine Set.mem_iUnion.mpr ⟨⟨⟨m, f⟩, hgood⟩, ?_⟩
  intro j q hj hq0 hq1
  have hj' : j < m + 1 := hj
  have hq0' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  have hq1' : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
  have hmem : segPt (v j) (v (j + 1)) (q : ℝ) ∈ pathSet (m + 1) v :=
    Set.mem_biUnion (Finset.mem_range.mpr hj') ⟨(q : ℝ), ⟨hq0', hq1'⟩, rfl⟩
  rw [hcf j (by omega), hcf (j + 1) (by omega)]
  exact hlev _ hmem

/-- The inner bound for the crossing probability. -/
theorem measure_crossApprox_le_crossing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {l : ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω) :
    P (crossApprox X a b i l) ≤ P {ω | Crosses a b i {u | l ≤ X u ω}} := by
  have hnull : P {ω | Continuous fun u => X u ω}ᶜ = 0 := by
    rw [← MeasureTheory.ae_iff.mp hcont]
    rfl
  calc P (crossApprox X a b i l)
      ≤ P (crossApprox X a b i l ∩ {ω | Continuous fun u => X u ω})
          + P {ω | Continuous fun u => X u ω}ᶜ := measure_le_inter_add_compl P _ _
    _ = P (crossApprox X a b i l ∩ {ω | Continuous fun u => X u ω}) := by rw [hnull, add_zero]
    _ ≤ P {ω | Crosses a b i {u | l ≤ X u ω}} :=
        measure_mono crossApprox_inter_subset_crossing

/-- The outer bound, at a level lower by `ε`. -/
theorem measure_crossing_le_crossApprox {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {l ε : ℝ}
    (ha0 : a 0 < b 0) (ha1 : a 1 < b 1) (hε : 0 < ε)
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω) :
    P {ω | Crosses a b i {u | l ≤ X u ω}} ≤ P (crossApprox X a b i (l - ε)) := by
  have hnull : P {ω | Continuous fun u => X u ω}ᶜ = 0 := by
    rw [← MeasureTheory.ae_iff.mp hcont]
    rfl
  calc P {ω | Crosses a b i {u | l ≤ X u ω}}
      ≤ P ({ω | Crosses a b i {u | l ≤ X u ω}} ∩ {ω | Continuous fun u => X u ω})
          + P {ω | Continuous fun u => X u ω}ᶜ := measure_le_inter_add_compl P _ _
    _ = P ({ω | Crosses a b i {u | l ≤ X u ω}} ∩ {ω | Continuous fun u => X u ω}) := by
        rw [hnull, add_zero]
    _ ≤ P (crossApprox X a b i (l - ε)) :=
        measure_mono (crossing_inter_subset_crossApprox ha0 ha1 hε)

/-- The chain event only weakens when the level falls. -/
theorem pathEvent_mono_level {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) {l l' : ℝ} (hl : l' ≤ l) (n : ℕ)
    (v : ℕ → Sandpile.Continuum.Space 2) :
    pathEvent X l n v ⊆ pathEvent X l' n v := by
  intro ω hω j q hj hq0 hq1
  exact le_trans hl (hω j q hj hq0 hq1)

/-- So does the union over the chains. -/
theorem crossApprox_mono_level {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2) {l l' : ℝ}
    (hl : l' ≤ l) : crossApprox X a b i l ⊆ crossApprox X a b i l' := by
  intro ω hω
  obtain ⟨ch, hch⟩ := Set.mem_iUnion.mp hω
  exact Set.mem_iUnion.mpr ⟨ch, pathEvent_mono_level X hl _ _ hch⟩

/-- And so does the crossing probability itself. -/
theorem measure_crossing_mono_level {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2) {l l' : ℝ}
    (hl : l' ≤ l) :
    P {ω | Crosses a b i {u | l ≤ X u ω}} ≤ P {ω | Crosses a b i {u | l' ≤ X u ω}} :=
  measure_mono fun _ hω => crosses_level_mono hl hω

/-- A chain whose vertices lie in the rectangle lies in the rectangle. -/
theorem pathSet_subset_rectSet {a b : Fin 2 → ℝ} (n : ℕ) (v : ℕ → Sandpile.Continuum.Space 2)
    (hv : ∀ j ≤ n, v j ∈ rectSet a b) : pathSet n v ⊆ rectSet a b := by
  intro u hu
  obtain ⟨j, hj, hu⟩ := Set.mem_iUnion₂.mp hu
  have hjn : j < n := Finset.mem_range.mp hj
  exact segSet_subset_rectSet (hv j (le_of_lt hjn)) (hv (j + 1) hjn) hu

/-- The bracket, in the two forms the crossing estimates use: the crossing
probability at a level is below the chain measure at any strictly lower level,
and above the chain measure at any higher level. -/
theorem measure_crossing_le_of_lt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {l l' : ℝ}
    (ha0 : a 0 < b 0) (ha1 : a 1 < b 1) (hl : l' < l)
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω) :
    P {ω | Crosses a b i {u | l ≤ X u ω}} ≤ P (crossApprox X a b i l') := by
  have hε : (0 : ℝ) < l - l' := by linarith
  have h := measure_crossing_le_crossApprox (i := i) P ha0 ha1 hε hcont (l := l)
  have hrw : l - (l - l') = l' := by ring
  rwa [hrw] at h

/-- The reverse bracket: the chain measure at a level is at most the crossing probability
at any lower or equal level. -/
theorem measure_crossApprox_le_of_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {l l' : ℝ}
    (hl : l ≤ l') (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω) :
    P (crossApprox X a b i l') ≤ P {ω | Crosses a b i {u | l ≤ X u ω}} := by
  refine le_trans (measure_crossApprox_le_crossing (i := i) (a := a) (b := b) P hcont) ?_
  exact measure_mono fun ω hω => crosses_level_mono hl hω

end Sandpile.Support
