import Mathlib.Analysis.Real.Cardinality
import Sandpile.Support.CrossBasic

/-!
# Crossing events read along a countable set of points

The crossing events of `sandpile.tex:2112-2118` read along a countable set of
points, which is what makes them events.

`Sandpile/Support/CrossVacuity.lean` shows that on the space of ALL planar
functions the crossing event of a nondegenerate rectangle has outer measure one,
so that no comparison of such outer measures says anything.  What survives is
the observation that the paper's fields have continuous sample paths
(`sandpile.tex:2103-2104`: "The fields `𝒳_s` have continuous
modifications"), and that for a CONTINUOUS field a crossing can be exhibited by data
indexed by a countable set.

This module builds that inner approximation.  A polygonal chain `v 0, …, v (m+1)`
of points of the plane spans the compact connected set `pathSet`, the union of
its closed segments; if the chain lies in the rectangle, starts on one side and
ends on the opposite side, and the field is at least the level on the chain,
then the superlevel set crosses (`crosses_of_pathSet`).  Along one segment the
level need only be checked at the RATIONAL parameters: a continuous function
that is at least the level at every rational parameter is at least the level on
the whole segment (`le_on_segSet`, from the density of `ℚ` in `ℝ`).  The
resulting event `pathEvent` on the probability space carrying the field is a
countable intersection of events about single field values, hence measurable
(`measurableSet_pathEvent`), and `measure_pathEvent_le_crossing` bounds the
outer measure of the crossing event below by its measure.

That inequality is the law bridge in the direction the fixed-scale crossing
estimate of `prop:fixed-scale-crossings` needs: a lower bound for the
probability of a crossing, obtained from a quantity that depends on the field
only through countably many of its values, and therefore only through its
finite-dimensional distributions.

The approximation is exact in the limit: `exists_path_of_crosses` is the
converse, that a crossing of a continuous field at level `l` is carried by such
a chain at level `l - ε` for every `ε > 0`.  Its ingredients are the thickening
of a compact set inside an open set, the `δ`-chains that connect any two points
of a preconnected set (`reflTransGen_of_isPreconnected`, which is where
connectedness of the crossing is used), and the convexity of the rectangle,
which is what keeps the chain inside it.
-/

open MeasureTheory Set

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A finite chain of connected sets `K 0, …, K n`, each meeting the next, has connected
union, proved by induction on `n`: the union up to `m` is connected by the induction
hypothesis, and it meets `K (m + 1)` at the point supplied by `hmeet m`, so
`IsPreconnected.union` joins them. -/
theorem isConnected_biUnion_chain {X : Type*} [TopologicalSpace X] (n : ℕ) (K : ℕ → Set X)
    (hKc : ∀ j ≤ n, IsConnected (K j))
    (hmeet : ∀ j < n, (K j ∩ K (j + 1)).Nonempty) :
    IsConnected (⋃ j ∈ Finset.range (n + 1), K j) := by
  induction n with
  | zero => simpa using hKc 0 le_rfl
  | succ m ih =>
      have hprev : IsConnected (⋃ j ∈ Finset.range (m + 1), K j) :=
        ih (fun j hj => hKc j (hj.trans (Nat.le_succ m)))
          (fun j hj => hmeet j (hj.trans (Nat.lt_succ_self m)))
      have hlast : IsConnected (K (m + 1)) := hKc (m + 1) le_rfl
      obtain ⟨x, hx1, hx2⟩ := hmeet m (Nat.lt_succ_self m)
      have hxU : x ∈ ⋃ j ∈ Finset.range (m + 1), K j :=
        Set.mem_biUnion (Finset.self_mem_range_succ m) hx1
      have hrw : (⋃ j ∈ Finset.range (m + 1 + 1), K j)
          = (⋃ j ∈ Finset.range (m + 1), K j) ∪ K (m + 1) := by
        rw [Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]
      rw [hrw]
      exact ⟨⟨x, Or.inl hxU⟩,
        IsPreconnected.union x hxU hx2 hprev.isPreconnected hlast.isPreconnected⟩

/-- The point at parameter `t` on the line through `v` and `w`: `v` at `t = 0`, `w` at
`t = 1`, and an affine combination in between. -/
noncomputable def segPt (v w : Sandpile.Continuum.Space 2) (t : ℝ) : Sandpile.Continuum.Space 2 :=
  v + t • (w - v)

/-- The closed segment from `v` to `w`, the image of `[0, 1]` under `segPt v w`. -/
noncomputable def segSet (v w : Sandpile.Continuum.Space 2) : Set (Sandpile.Continuum.Space 2) :=
  segPt v w '' Set.Icc (0 : ℝ) 1

/-- `segPt v w` is continuous in the parameter `t`. -/
theorem continuous_segPt (v w : Sandpile.Continuum.Space 2) : Continuous (segPt v w) := by
  unfold segPt
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- The segment starts at `v`. -/
theorem segPt_zero (v w : Sandpile.Continuum.Space 2) : segPt v w 0 = v := by
  simp [segPt]

/-- The segment ends at `w`. -/
theorem segPt_one (v w : Sandpile.Continuum.Space 2) : segPt v w 1 = w := by
  simp [segPt]

/-- `segSet v w` is compact, the continuous image of the compact interval `[0, 1]`. -/
theorem isCompact_segSet (v w : Sandpile.Continuum.Space 2) : IsCompact (segSet v w) :=
  isCompact_Icc.image (continuous_segPt v w)

/-- `segSet v w` is connected, the continuous image of the connected interval `[0, 1]`. -/
theorem isConnected_segSet (v w : Sandpile.Continuum.Space 2) : IsConnected (segSet v w) :=
  (isConnected_Icc (by norm_num : (0:ℝ) ≤ 1)).image _ (continuous_segPt v w).continuousOn

/-- The left endpoint `v` lies in `segSet v w`. -/
theorem left_mem_segSet (v w : Sandpile.Continuum.Space 2) : v ∈ segSet v w :=
  ⟨0, ⟨le_refl _, by norm_num⟩, segPt_zero v w⟩

/-- The right endpoint `w` lies in `segSet v w`. -/
theorem right_mem_segSet (v w : Sandpile.Continuum.Space 2) : w ∈ segSet v w :=
  ⟨1, ⟨by norm_num, le_refl _⟩, segPt_one v w⟩

/-- A continuous function that is at least `l` at every rational is at least `l`
everywhere, since `{f ≥ l}` is closed and `ℚ` is dense in `ℝ`. -/
theorem le_of_le_on_rat {f : ℝ → ℝ} (hf : Continuous f) {l : ℝ}
    (h : ∀ q : ℚ, l ≤ f (q : ℝ)) (t : ℝ) : l ≤ f t := by
  have hclosed : IsClosed {x : ℝ | l ≤ f x} := isClosed_le continuous_const hf
  have hrange : Set.range ((↑) : ℚ → ℝ) ⊆ {x : ℝ | l ≤ f x} := by
    rintro x ⟨q, rfl⟩
    exact h q
  have huniv : (Set.univ : Set ℝ) ⊆ {x : ℝ | l ≤ f x} := by
    rw [← Rat.denseRange_cast.closure_range]
    exact hclosed.closure_subset_iff.mpr hrange
  exact huniv (Set.mem_univ t)

/-- If `X` is continuous and at least `l` at every rational parameter of the segment
`segSet v w`, it is at least `l` on the whole segment: clamp the parameter to `[0, 1]`
and apply `le_of_le_on_rat`. -/
theorem le_on_segSet {X : Sandpile.Continuum.Space 2 → ℝ} (hX : Continuous X)
    (v w : Sandpile.Continuum.Space 2) (l : ℝ)
    (h : ∀ q : ℚ, 0 ≤ q → q ≤ 1 → l ≤ X (segPt v w (q : ℝ))) :
    ∀ u ∈ segSet v w, l ≤ X u := by
  have hclamp : Continuous (fun t : ℝ => max 0 (min 1 t)) :=
    continuous_const.max (continuous_const.min continuous_id)
  have hg : Continuous (fun t : ℝ => X (segPt v w (max 0 (min 1 t)))) :=
    hX.comp ((continuous_segPt v w).comp hclamp)
  have hq : ∀ q : ℚ, l ≤ X (segPt v w (max 0 (min 1 (q : ℝ)))) := by
    intro q
    have hcast : (max 0 (min 1 (q : ℝ))) = ((max 0 (min 1 q) : ℚ) : ℝ) := by push_cast; rfl
    rw [hcast]
    exact h _ (le_max_left _ _) (max_le (by norm_num) (min_le_left _ _))
  rintro u ⟨t, ⟨ht0, ht1⟩, rfl⟩
  have hval := le_of_le_on_rat hg hq t
  rwa [min_eq_right ht1, max_eq_right ht0] at hval

/-- The polygonal chain through `v 0, …, v n`: the union of the `n` closed segments
`segSet (v j) (v (j + 1))` for `j < n`. -/
noncomputable def pathSet (n : ℕ) (v : ℕ → Sandpile.Continuum.Space 2) :
    Set (Sandpile.Continuum.Space 2) :=
  ⋃ j ∈ Finset.range n, segSet (v j) (v (j + 1))

/-- `pathSet n v` is compact, a finite union of compact segments. -/
theorem isCompact_pathSet (n : ℕ) (v : ℕ → Sandpile.Continuum.Space 2) :
    IsCompact (pathSet n v) :=
  (Finset.range n).finite_toSet.isCompact_biUnion fun _ _ => isCompact_segSet _ _

/-- `pathSet (m + 1) v` is connected: consecutive segments share the vertex `v (j + 1)`,
so `isConnected_biUnion_chain` applies. -/
theorem isConnected_pathSet (m : ℕ) (v : ℕ → Sandpile.Continuum.Space 2) :
    IsConnected (pathSet (m + 1) v) :=
  isConnected_biUnion_chain m (fun j => segSet (v j) (v (j + 1)))
    (fun _ _ => isConnected_segSet _ _)
    (fun j _ => ⟨v (j + 1), right_mem_segSet _ _, left_mem_segSet _ _⟩)

/-- The first vertex of the chain lies on its path set. -/
theorem start_mem_pathSet (m : ℕ) (v : ℕ → Sandpile.Continuum.Space 2) :
    v 0 ∈ pathSet (m + 1) v :=
  Set.mem_biUnion (Finset.mem_range.mpr (Nat.succ_pos m)) (left_mem_segSet _ _)

/-- The last vertex of the chain lies on its path set. -/
theorem end_mem_pathSet (m : ℕ) (v : ℕ → Sandpile.Continuum.Space 2) :
    v (m + 1) ∈ pathSet (m + 1) v :=
  Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_self m)) (right_mem_segSet _ _)

/-- A chain whose path set lies in `S ∩ rectSet a b` and that runs from the side `a i`
to the side `b i` witnesses that `S` crosses the rectangle: `pathSet (m + 1) v` itself is
the compact connected set of the `Crosses` definition. -/
theorem crosses_of_pathSet {a b : Fin 2 → ℝ} {i : Fin 2}
    {S : Set (Sandpile.Continuum.Space 2)} (m : ℕ) (v : ℕ → Sandpile.Continuum.Space 2)
    (hsub : pathSet (m + 1) v ⊆ S ∩ rectSet a b)
    (hstart : v 0 i = a i) (hend : v (m + 1) i = b i) :
    Crosses a b i S :=
  ⟨pathSet (m + 1) v, hsub, isCompact_pathSet _ _, isConnected_pathSet m v,
    ⟨v 0, start_mem_pathSet m v, hstart⟩, ⟨v (m + 1), end_mem_pathSet m v, hend⟩⟩

/-- The event, on the probability space carrying the field, that the field is at
least the level at every rational parameter of every segment of the chain.  It is
an intersection of countably many events about single field values. -/
def pathEvent {Ω : Type*} [MeasurableSpace Ω] (X : Sandpile.Continuum.Space 2 → Ω → ℝ)
    (l : ℝ) (n : ℕ) (v : ℕ → Sandpile.Continuum.Space 2) : Set Ω :=
  {ω | ∀ (j : ℕ) (q : ℚ), j < n → 0 ≤ q → q ≤ 1 →
    l ≤ X (segPt (v j) (v (j + 1)) (q : ℝ)) ω}

/-- `pathEvent X l n v` is measurable: it is a countable intersection, over `j : ℕ` and
`q : ℚ`, of sets that are either the measurable `{ω | l ≤ X (segPt ...) ω}` (when the
side conditions `j < n`, `0 ≤ q ≤ 1` hold) or all of `Ω` (when they fail). -/
theorem measurableSet_pathEvent {Ω : Type*} [MeasurableSpace Ω]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    (l : ℝ) (n : ℕ) (v : ℕ → Sandpile.Continuum.Space 2) :
    MeasurableSet (pathEvent X l n v) := by
  classical
  have hrw : pathEvent X l n v =
      ⋂ (j : ℕ), ⋂ (q : ℚ), {ω | j < n → 0 ≤ q → q ≤ 1 →
        l ≤ X (segPt (v j) (v (j + 1)) (q : ℝ)) ω} := by
    ext ω
    simp only [pathEvent, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hrw]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun q => ?_
  by_cases h : j < n ∧ 0 ≤ q ∧ q ≤ 1
  · have hset : {ω | j < n → 0 ≤ q → q ≤ 1 → l ≤ X (segPt (v j) (v (j + 1)) (q : ℝ)) ω}
        = {ω | l ≤ X (segPt (v j) (v (j + 1)) (q : ℝ)) ω} := by
      ext ω
      simp [h.1, h.2.1, h.2.2]
    rw [hset]
    exact measurableSet_le measurable_const (hX _)
  · have hset : {ω | j < n → 0 ≤ q → q ≤ 1 → l ≤ X (segPt (v j) (v (j + 1)) (q : ℝ)) ω}
        = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1 h2 h3
      exact absurd ⟨h1, h2, h3⟩ h
    rw [hset]
    exact MeasurableSet.univ

/-- On the event that the sample path is continuous, the countably determined
event `pathEvent` forces the superlevel set to cross the rectangle. -/
theorem pathEvent_inter_subset_crossing {Ω : Type*} [MeasurableSpace Ω]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {l : ℝ}
    (m : ℕ) (v : ℕ → Sandpile.Continuum.Space 2)
    (hrect : pathSet (m + 1) v ⊆ rectSet a b)
    (hstart : v 0 i = a i) (hend : v (m + 1) i = b i) :
    pathEvent X l (m + 1) v ∩ {ω | Continuous fun u => X u ω}
      ⊆ {ω | Crosses a b i {u | l ≤ X u ω}} := by
  rintro ω ⟨hp, hc⟩
  refine crosses_of_pathSet m v (fun u hu => ⟨?_, hrect hu⟩) hstart hend
  obtain ⟨j, hj, hu⟩ := Set.mem_iUnion₂.mp hu
  exact le_on_segSet hc _ _ l
    (fun q hq0 hq1 => hp j q (Finset.mem_range.mp hj) hq0 hq1) u hu

/-- The law bridge in the direction the fixed-scale crossing estimate needs: the
outer measure of the crossing event of an almost surely continuous field is at
least the measure of the countably determined chain event, which is an event
about finitely many field values at a time. -/
theorem measure_pathEvent_le_crossing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {l : ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω)
    (m : ℕ) (v : ℕ → Sandpile.Continuum.Space 2)
    (hrect : pathSet (m + 1) v ⊆ rectSet a b)
    (hstart : v 0 i = a i) (hend : v (m + 1) i = b i) :
    P (pathEvent X l (m + 1) v) ≤ P {ω | Crosses a b i {u | l ≤ X u ω}} := by
  have hnull : P {ω | Continuous fun u => X u ω}ᶜ = 0 := by
    rw [← MeasureTheory.ae_iff.mp hcont]
    rfl
  calc P (pathEvent X l (m + 1) v)
      ≤ P (pathEvent X l (m + 1) v ∩ {ω | Continuous fun u => X u ω})
          + P {ω | Continuous fun u => X u ω}ᶜ :=
        measure_le_inter_add_compl P _ _
    _ = P (pathEvent X l (m + 1) v ∩ {ω | Continuous fun u => X u ω}) := by
        rw [hnull, add_zero]
    _ ≤ P {ω | Crosses a b i {u | l ≤ X u ω}} :=
        measure_mono (pathEvent_inter_subset_crossing m v hrect hstart hend)

/-- The horizontal line at height `c`, parametrized by the first coordinate. -/
noncomputable def hSeg (c t : ℝ) : Sandpile.Continuum.Space 2 :=
  t • (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) + c • (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

/-- The first coordinate of `hSeg c t` is the parameter `t`. -/
theorem hSeg_apply_zero (c t : ℝ) : hSeg c t 0 = t := by
  simp [hSeg]

/-- The second coordinate of `hSeg c t` is the fixed height `c`. -/
theorem hSeg_apply_one (c t : ℝ) : hSeg c t 1 = c := by
  simp [hSeg]

/-- `hSeg c` is continuous in the parameter `t`. -/
theorem continuous_hSeg (c : ℝ) : Continuous (hSeg c) := by
  unfold hSeg
  exact (continuous_id.smul continuous_const).add continuous_const

/-- A horizontal segment across the rectangle on which the field is at least
the level is a left-right crossing: it is compact, connected, and meets the two
vertical sides. -/
theorem crosses_hSeg {a b : Fin 2 → ℝ} {level c : ℝ} {X : Sandpile.Continuum.Space 2 → ℝ}
    (hab : a 0 ≤ b 0) (hc0 : a 1 ≤ c) (hc1 : c ≤ b 1)
    (hX : ∀ t, a 0 ≤ t → t ≤ b 0 → level ≤ X (hSeg c t)) :
    Crosses a b 0 {u | level ≤ X u} := by
  refine ⟨hSeg c '' (Set.Icc (a 0) (b 0)), ?_, isCompact_Icc.image (continuous_hSeg c),
    (isConnected_Icc hab).image _ (continuous_hSeg c).continuousOn,
    ⟨hSeg c (a 0), ⟨a 0, ⟨le_refl _, hab⟩, rfl⟩, hSeg_apply_zero c (a 0)⟩,
    ⟨hSeg c (b 0), ⟨b 0, ⟨hab, le_refl _⟩, rfl⟩, hSeg_apply_zero c (b 0)⟩⟩
  rintro w ⟨t, ⟨ht1, ht2⟩, rfl⟩
  refine ⟨hX t ht1 ht2, ?_⟩
  intro i
  fin_cases i
  · show a 0 ≤ hSeg c t 0 ∧ hSeg c t 0 ≤ b 0
    rw [hSeg_apply_zero]
    exact ⟨ht1, ht2⟩
  · show a 1 ≤ hSeg c t 1 ∧ hSeg c t 1 ≤ b 1
    rw [hSeg_apply_one]
    exact ⟨hc0, hc1⟩

/-- The `k`-th coordinate of a point of the segment. -/
theorem segPt_apply (v w : Sandpile.Continuum.Space 2) (t : ℝ) (k : Fin 2) :
    segPt v w t k = v k + t * (w k - v k) := by
  simp [segPt]

/-- A rectangle is convex, so it contains the segment between any two of its
points. -/
theorem segSet_subset_rectSet {a b : Fin 2 → ℝ} {v w : Sandpile.Continuum.Space 2}
    (hv : v ∈ rectSet a b) (hw : w ∈ rectSet a b) : segSet v w ⊆ rectSet a b := by
  rintro u ⟨t, ⟨ht0, ht1⟩, rfl⟩
  intro k
  obtain ⟨hv1, hv2⟩ := hv k
  obtain ⟨hw1, hw2⟩ := hw k
  rw [segPt_apply]
  constructor
  · nlinarith
  · nlinarith

/-- A segment whose endpoints are within `δ` of each other lies in the
`δ`-thickening of any set containing its first endpoint. -/
theorem segSet_subset_thickening {δ : ℝ} {Γ : Set (Sandpile.Continuum.Space 2)}
    {v w : Sandpile.Continuum.Space 2} (hv : v ∈ Γ) (hd : dist v w < δ) :
    segSet v w ⊆ Metric.thickening δ Γ := by
  rintro u ⟨t, ⟨ht0, ht1⟩, rfl⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨v, hv, ?_⟩
  have hnorm : dist (segPt v w t) v = |t| * dist v w := by
    rw [dist_eq_norm, segPt, dist_eq_norm]
    simp [norm_smul, norm_sub_rev]
  rw [hnorm, abs_of_nonneg ht0]
  have hdd : (0 : ℝ) ≤ dist v w := dist_nonneg
  nlinarith

/-- In a preconnected set `Γ`, every point `y ∈ Γ` is reachable from a fixed `x ∈ Γ` by a
`ReflTransGen` chain of steps that stay in `Γ` with consecutive distance less than `δ`.
Proved by splitting `Γ` into the `δ`-neighborhood `U` of the reachable points and the
`δ`-neighborhood `V` of the rest, showing `U`, `V` cannot both meet `Γ` (else a point of
`U ∩ V ∩ Γ` would extend reachability into `V`), and using preconnectedness to rule out
`Γ ∩ V` being nonempty while `Γ ∩ U` is. -/
theorem reflTransGen_of_isPreconnected {X : Type*} [MetricSpace X] {Γ : Set X}
    (hconn : IsPreconnected Γ) {δ : ℝ} (hδ : 0 < δ) {x : X} (hx : x ∈ Γ) :
    ∀ y ∈ Γ, Relation.ReflTransGen (fun p q => q ∈ Γ ∧ dist p q < δ) x y := by
  classical
  set r : X → X → Prop := fun p q => q ∈ Γ ∧ dist p q < δ with hr
  set A : Set X := {z | z ∈ Γ ∧ Relation.ReflTransGen r x z} with hA
  set U : Set X := ⋃ z ∈ A, Metric.ball z δ with hU
  set V : Set X := ⋃ z ∈ Γ \ A, Metric.ball z δ with hV
  have hUopen : IsOpen U := isOpen_biUnion fun z _ => Metric.isOpen_ball
  have hVopen : IsOpen V := isOpen_biUnion fun z _ => Metric.isOpen_ball
  have hcover : Γ ⊆ U ∪ V := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact Or.inl (Set.mem_biUnion hzA (Metric.mem_ball_self hδ))
    · exact Or.inr (Set.mem_biUnion ⟨hz, hzA⟩ (Metric.mem_ball_self hδ))
  have hxA : x ∈ A := ⟨hx, Relation.ReflTransGen.refl⟩
  have hUne : (Γ ∩ U).Nonempty := ⟨x, hx, Set.mem_biUnion hxA (Metric.mem_ball_self hδ)⟩
  have hempty : ¬ (Γ ∩ (U ∩ V)).Nonempty := by
    rintro ⟨w, hwΓ, hwU, hwV⟩
    obtain ⟨z, hzA, hwz⟩ := Set.mem_iUnion₂.mp hwU
    obtain ⟨z', hz'A, hwz'⟩ := Set.mem_iUnion₂.mp hwV
    have hwA : Relation.ReflTransGen r x w :=
      hzA.2.tail ⟨hwΓ, by simpa [dist_comm] using hwz⟩
    have hz'reach : Relation.ReflTransGen r x z' :=
      hwA.tail ⟨hz'A.1, by simpa [dist_comm] using hwz'⟩
    exact hz'A.2 ⟨hz'A.1, hz'reach⟩
  have hVempty : ¬ (Γ ∩ V).Nonempty := fun hVne => hempty (hconn U V hUopen hVopen hcover hUne hVne)
  intro y hy
  by_cases hyA : y ∈ A
  · exact hyA.2
  · exact absurd ⟨y, hy, Set.mem_biUnion ⟨hy, hyA⟩ (Metric.mem_ball_self hδ)⟩ hVempty

/-- Unwinds a `ReflTransGen` chain of `δ`-close steps from `x` to `y` into an explicit
finite vertex sequence `v 0 = x, …, v (m + 1) = y`, all lying in `Γ`, with consecutive
vertices at distance less than `δ`, by induction on the `ReflTransGen` derivation. -/
theorem exists_vertices_of_reflTransGen {X : Type*} [MetricSpace X] {Γ : Set X} {δ : ℝ}
    (hδ : 0 < δ) {x y : X} (hx : x ∈ Γ)
    (h : Relation.ReflTransGen (fun p q => q ∈ Γ ∧ dist p q < δ) x y) :
    ∃ (m : ℕ) (v : ℕ → X), v 0 = x ∧ v (m + 1) = y ∧ (∀ j ≤ m + 1, v j ∈ Γ) ∧
      ∀ j ≤ m, dist (v j) (v (j + 1)) < δ := by
  classical
  induction h with
  | refl => exact ⟨0, fun _ => x, rfl, rfl, fun _ _ => hx, fun _ _ => by simpa using hδ⟩
  | @tail b c hab hbc ih =>
      obtain ⟨m, v, hv0, hvm, hvΓ, hvd⟩ := ih
      refine ⟨m + 1, fun j => if j ≤ m + 1 then v j else c, ?_, ?_, ?_, ?_⟩
      · simp only [if_pos (Nat.zero_le _)]
        exact hv0
      · simp only [if_neg (by omega : ¬ (m + 1 + 1 ≤ m + 1))]
      · intro j hj
        by_cases hjm : j ≤ m + 1
        · simpa [hjm] using hvΓ j hjm
        · simpa [hjm] using hbc.1
      · intro j hj
        rcases Nat.lt_or_ge j (m + 1) with hjm | hjm
        · have h1 : j ≤ m + 1 := le_of_lt hjm
          have h2 : j + 1 ≤ m + 1 := by omega
          simpa [h1, h2] using hvd j (by omega)
        · have hjeq : j = m + 1 := by omega
          subst hjeq
          simp only [if_pos (le_refl (m + 1)), if_neg (by omega : ¬ (m + 1 + 1 ≤ m + 1))]
          rw [hvm]
          exact hbc.2

/-- The converse approximation: a crossing of a continuous field at level `l` is
carried by a polygonal chain inside the rectangle on which the field is at least
`l - ε`.  The crossing is compact and sits in the open set `{X > l - ε}`, so a
whole thickening of it does; the chain is a `δ`-chain inside the crossing, which
exists because the crossing is connected, and its segments stay in the rectangle
because a rectangle is convex. -/
theorem exists_path_of_crosses {X : Sandpile.Continuum.Space 2 → ℝ} (hX : Continuous X)
    {a b : Fin 2 → ℝ} {i : Fin 2} {l ε : ℝ} (hε : 0 < ε)
    (h : Crosses a b i {u | l ≤ X u}) :
    ∃ (m : ℕ) (v : ℕ → Sandpile.Continuum.Space 2),
      pathSet (m + 1) v ⊆ rectSet a b ∧
      (∀ u ∈ pathSet (m + 1) v, l - ε ≤ X u) ∧
      v 0 i = a i ∧ v (m + 1) i = b i := by
  obtain ⟨Γ, hsub, hcomp, hconn, ⟨p, hpΓ, hpa⟩, ⟨q, hqΓ, hqb⟩⟩ := h
  have hGopen : IsOpen {u : Sandpile.Continuum.Space 2 | l - ε < X u} :=
    isOpen_lt continuous_const hX
  have hΓG : Γ ⊆ {u : Sandpile.Continuum.Space 2 | l - ε < X u} := by
    intro u hu
    have hlu : l ≤ X u := (hsub hu).1
    show l - ε < X u
    linarith
  obtain ⟨δ, hδ, hδsub⟩ := hcomp.exists_thickening_subset_open hGopen hΓG
  have hchain := reflTransGen_of_isPreconnected hconn.isPreconnected hδ hpΓ q hqΓ
  obtain ⟨m, v, hv0, hvm, hvΓ, hvd⟩ := exists_vertices_of_reflTransGen hδ hpΓ hchain
  refine ⟨m, v, ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨j, hj, hu⟩ := Set.mem_iUnion₂.mp hu
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact segSet_subset_rectSet (hsub (hvΓ j (by omega))).2 (hsub (hvΓ (j + 1) (by omega))).2 hu
  · intro u hu
    obtain ⟨j, hj, hu⟩ := Set.mem_iUnion₂.mp hu
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hthick : u ∈ Metric.thickening δ Γ :=
      segSet_subset_thickening (hvΓ j (by omega)) (hvd j hjm) hu
    exact le_of_lt (hδsub hthick)
  · rw [hv0]; exact hpa
  · rw [hvm]; exact hqb

end Sandpile.Support
