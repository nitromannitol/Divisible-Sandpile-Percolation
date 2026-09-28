import LatticeProb.Analysis.SoftComposition

/-!
# Balanced bottleneck recursions

Balanced bottleneck recursions on a finite graph. Bounded walks split at their midpoint, their
minima attain the exact recursion, and smooth extrema give a uniform approximation with
derivative bounds proportional to the depth.
-/

open LatticeProb

namespace Sandpile

variable {V : Type*} (G : SimpleGraph V)

/-- `a` reaches `b` within `2^n` steps of `G`: there is a walk of length at most `2^n`. -/
def BoundedReach (n : ℕ) (a b : V) : Prop := ∃ p : G.Walk a b, p.length ≤ 2 ^ n

/-- At the base layer `n = 0`, `BoundedReach G 0 a b` holds iff `a = b` or `G.Adj a b`, since a
walk of length at most `1` is either trivial or a single edge. -/
lemma boundedReach_zero (a b : V) : BoundedReach G 0 a b ↔ a = b ∨ G.Adj a b := by
  constructor
  · rintro ⟨p, hp⟩
    simp only [pow_zero] at hp
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with h | h
    · exact Or.inl (SimpleGraph.Walk.eq_of_length_eq_zero h)
    · exact Or.inr (SimpleGraph.Walk.adj_of_length_eq_one h)
  · rintro (rfl | h)
    · exact ⟨.nil, by simp⟩
    · exact ⟨h.toWalk, by simp⟩

/-- The bottleneck-recursion step for reachability: `BoundedReach G (n+1) a b` holds iff some
midpoint `c` is within `BoundedReach G n` of both `a` and `b`, obtained by splitting a
length-`2^(n+1)` walk at its midpoint (`Walk.take`/`Walk.drop`) or by concatenating two
length-`2^n` witnesses (`Walk.append`). -/
lemma boundedReach_succ (n : ℕ) (a b : V) :
    BoundedReach G (n + 1) a b ↔ ∃ c, BoundedReach G n a c ∧ BoundedReach G n c b := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.getVert (2 ^ n), ⟨p.take (2 ^ n), ?_⟩, ⟨p.drop (2 ^ n), ?_⟩⟩
    · simp only [SimpleGraph.Walk.take_length]
      exact min_le_left _ _
    · simp only [SimpleGraph.Walk.drop_length]
      rw [pow_succ] at hp
      omega
  · rintro ⟨c, ⟨p, hp⟩, ⟨q, hq⟩⟩
    refine ⟨p.append q, ?_⟩
    rw [SimpleGraph.Walk.length_append, pow_succ]
    omega

section Bottleneck
variable {G} [DecidableEq V]

/-- The minimum value of `F` along the support of the walk `p`, computed as a `Finset.inf'` over
the (finite) list of visited vertices. -/
noncomputable def walkBottleneck {a b : V} (p : G.Walk a b) (F : V → ℝ) : ℝ :=
  p.support.toFinset.inf' ⟨a, List.mem_toFinset.mpr p.start_mem_support⟩ F

/-- `c` is a lower bound for the bottleneck of `p` iff `F` is at least `c` at every site visited
by `p`. -/
lemma le_walkBottleneck_iff {a b : V} (p : G.Walk a b) (F : V → ℝ) (c : ℝ) :
    c ≤ walkBottleneck p F ↔ ∀ z ∈ p.support, c ≤ F z := by
  simp [walkBottleneck, Finset.le_inf'_iff]

/-- The bottleneck value never exceeds `F` at any site the walk visits. -/
lemma walkBottleneck_le {a b z : V} (p : G.Walk a b) (F : V → ℝ) (hz : z ∈ p.support) :
    walkBottleneck p F ≤ F z :=
  (le_walkBottleneck_iff p F _).mp le_rfl z hz

/-- The bottleneck value is attained: some site on the walk realizes it exactly. -/
lemma walkBottleneck_mem {a b : V} (p : G.Walk a b) (F : V → ℝ) :
    ∃ z ∈ p.support, walkBottleneck p F = F z := by
  obtain ⟨z, hz, he⟩ := Finset.exists_mem_eq_inf'
    (s := p.support.toFinset) ⟨a, List.mem_toFinset.mpr p.start_mem_support⟩ F
  exact ⟨z, List.mem_toFinset.mp hz, he⟩

/-- The bottleneck of the trivial walk at `a` is just `F a`. -/
lemma walkBottleneck_nil (a : V) (F : V → ℝ) : walkBottleneck (.nil (G := G) (u := a)) F = F a := by
  simp [walkBottleneck]

/-- The bottleneck of a concatenated walk `p.append q` is the smaller of the two pieces'
bottlenecks, since the support of the concatenation is the union of the two supports. -/
lemma walkBottleneck_append {a b c : V} (p : G.Walk a b) (q : G.Walk b c) (F : V → ℝ) :
    walkBottleneck (p.append q) F = min (walkBottleneck p F) (walkBottleneck q F) := by
  apply le_antisymm
  · apply le_min
    · apply (le_walkBottleneck_iff p F _).mpr
      intro z hz
      exact walkBottleneck_le (p.append q) F (p.support_subset_support_append_left q hz)
    · apply (le_walkBottleneck_iff q F _).mpr
      intro z hz
      exact walkBottleneck_le (p.append q) F (p.support_subset_support_append_right q hz)
  · apply (le_walkBottleneck_iff (p.append q) F _).mpr
    intro z hz
    rcases (SimpleGraph.Walk.mem_support_append_iff p q).mp hz with hz | hz
    · exact (min_le_left _ _).trans (walkBottleneck_le p F hz)
    · exact (min_le_right _ _).trans (walkBottleneck_le q F hz)

/-- Splitting a walk at the vertex reached after `n` steps via `Walk.take`/`Walk.drop`, and
combining with `walkBottleneck_append`, recovers the bottleneck of the whole walk as the minimum
of the two halves. -/
lemma walkBottleneck_take_drop {a b : V} (p : G.Walk a b) (F : V → ℝ) (n : ℕ) :
    walkBottleneck p F = min (walkBottleneck (p.take n) F) (walkBottleneck (p.drop n) F) := by
  rw [← walkBottleneck_append, SimpleGraph.Walk.append_take_drop_eq]

/-- The bottleneck value can only increase when a walk is shortcut to its `bypass` (the simple
path with the same endpoints), since `bypass` visits a subset of the original support. -/
lemma walkBottleneck_le_bypass {a b : V} (p : G.Walk a b) (F : V → ℝ) :
    walkBottleneck p F ≤ walkBottleneck p.bypass F := by
  apply (le_walkBottleneck_iff p.bypass F _).mpr
  intro z hz
  exact walkBottleneck_le p F (p.support_bypass_subset_support hz)

/-- The bottleneck value equals the infimum of `F` over the (finite, nonempty) image of the
walk's support, unwinding `Finset.inf'` as an `sInf` over the corresponding set. -/
lemma walkBottleneck_eq_csInf {a b : V} (p : G.Walk a b) (F : V → ℝ) :
    walkBottleneck p F = sInf (F '' {z : V | z ∈ p.support}) := by
  unfold walkBottleneck
  rw [Finset.inf'_eq_csInf_image]
  congr 2
  ext z
  simp

/-- A walk of length at most `1` is either trivial or a single edge, so its bottleneck value is
exactly `min (F a) (F b)`, checked by case analysis on the walk's constructors. -/
lemma walkBottleneck_of_length_le_one {a b : V} (p : G.Walk a b) (F : V → ℝ)
    (hp : p.length ≤ 1) : walkBottleneck p F = min (F a) (F b) := by
  cases p with
  | nil => simp [walkBottleneck]
  | cons h p =>
    cases p with
    | nil => simp [walkBottleneck, Finset.inf'_insert]
    | cons h' p => simp at hp

end Bottleneck

variable [Fintype V]

/-- The (finite) set of candidate midpoints for splitting a `BoundedReach G (n+1)` witness
between `a` and `b`: sites `c` within `BoundedReach G n` of both `a` and `b`. -/
noncomputable def walkMidpoints (n : ℕ) (a b : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun c => BoundedReach G n a c ∧ BoundedReach G n c b)

/-- Membership characterization: `c ∈ walkMidpoints G n a b` iff `BoundedReach G n a c` and
`BoundedReach G n c b`. -/
lemma mem_walkMidpoints (n : ℕ) (a b c : V) :
    c ∈ walkMidpoints G n a b ↔ BoundedReach G n a c ∧ BoundedReach G n c b := by
  classical
  simp [walkMidpoints]

/-- If `a` and `b` satisfy `BoundedReach G (n+1)`, the midpoint set `walkMidpoints G n a b` is
nonempty, extracting the witness midpoint of `boundedReach_succ`. -/
lemma walkMidpoints_nonempty {n : ℕ} {a b : V} (h : BoundedReach G (n + 1) a b) :
    (walkMidpoints G n a b).Nonempty := by
  obtain ⟨c, hc⟩ := (boundedReach_succ G n a b).mp h
  exact ⟨c, (mem_walkMidpoints G n a b c).mpr hc⟩

section Maximum
variable {I : Type*} [Fintype I] [Nonempty I]

/-- The maximum value of `f` over a finite nonempty index type `I`, via `Finset.sup'`. -/
noncomputable def finiteMaximum (f : I → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty f

/-- Every value `f i` is at most the finite maximum `finiteMaximum f`. -/
lemma le_finiteMaximum (f : I → ℝ) (i : I) : f i ≤ finiteMaximum f :=
  Finset.le_sup' f (Finset.mem_univ i)

/-- `finiteMaximum f ≤ c` iff `f i ≤ c` for every index `i`. -/
lemma finiteMaximum_le_iff (f : I → ℝ) (c : ℝ) : finiteMaximum f ≤ c ↔ ∀ i, f i ≤ c := by
  simp [finiteMaximum, Finset.sup'_le_iff]

/-- The finite maximum is attained: some index `i` realizes it exactly. -/
lemma finiteMaximum_mem (f : I → ℝ) : ∃ i, finiteMaximum f = f i := by
  obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty f
  exact ⟨i, h⟩

/-- If a smooth approximant `f` and exact values `g` agree pointwise up to `a`, the smooth
maximum `softMaximum β f` and the finite maximum `finiteMaximum g` agree up to `a` plus a
logarithmic correction `log(card I)/β` coming from the Gibbs bias of `softMaximum`. -/
lemma abs_softMaximum_sub_finiteMaximum {β : ℝ} (hβ : 0 < β)
    (f g : I → ℝ) {a : ℝ} (ha : ∀ i, |f i - g i| ≤ a) :
    |softMaximum β f - finiteMaximum g| ≤ a + Real.log (Fintype.card I) / β := by
  have hlog : 0 ≤ Real.log (Fintype.card I) / β := by
    apply div_nonneg _ hβ.le
    apply Real.log_nonneg
    exact_mod_cast Fintype.card_pos
  have hu := softMaximum_le hβ f (finiteMaximum g + a) (fun i => by
    have h := (abs_le.mp (ha i)).2
    linarith [le_finiteMaximum g i])
  obtain ⟨i, hi⟩ := finiteMaximum_mem g
  have hl := le_softMaximum hβ f i
  have he := (abs_le.mp (ha i)).1
  rw [abs_le]
  constructor <;> linarith

end Maximum

/-- The exact recursive bottleneck value at layer `n`: at `n = 0` it is `min (F a) (F b)`, and at
`n + 1` it is the finite maximum, over midpoints `c ∈ walkMidpoints G n a b`, of the minimum of
the two half-recursions on `[a, c]` and `[c, b]`. -/
noncomputable def boundedBottleneckValue :
    (n : ℕ) → (a b : V) → BoundedReach G n a b → (V → ℝ) → ℝ
  | 0, a, b, _, F => min (F a) (F b)
  | n + 1, a, b, h, F => by
    classical
    letI : Nonempty (walkMidpoints G n a b) := by
      obtain ⟨c, hc⟩ := walkMidpoints_nonempty G h
      exact ⟨⟨c, hc⟩⟩
    exact finiteMaximum (fun c : walkMidpoints G n a b =>
      min (boundedBottleneckValue n a c ((mem_walkMidpoints G n a b c).mp c.property).1 F)
        (boundedBottleneckValue n c b ((mem_walkMidpoints G n a b c).mp c.property).2 F))

/-- The smooth (`C^∞`) approximation to `boundedBottleneckValue` at inverse temperature `β`:
`softMinimum`/`softMaximum` at each recursive layer replace `min`/`finiteMaximum`, so `n` is
exactly the number of smooth composition layers used. -/
noncomputable def smoothBoundedBottleneck (β : ℝ) :
    (n : ℕ) → (a b : V) → BoundedReach G n a b → (V → ℝ) → ℝ
  | 0, a, b, _, F => LatticeProb.softMinimum β ![F a, F b]
  | n + 1, a, b, _, F => by
    classical
    exact softMaximum β (fun c : walkMidpoints G n a b =>
      LatticeProb.softMinimum β ![
        smoothBoundedBottleneck β n a c ((mem_walkMidpoints G n a b c).mp c.property).1 F,
        smoothBoundedBottleneck β n c b ((mem_walkMidpoints G n a b c).mp c.property).2 F])

/-- The smooth minimum of two functions each satisfying `SmoothBottleneckBound β n` satisfies the
bound at layer `n + 1`, by rewriting the pairwise `softMinimum β ![f F, g F]` as the two-index
composition `LatticeProb.softMinimum β ![f, g]` and applying `SmoothBottleneckBound.softMinimum`.
-/
lemma SmoothBottleneckBound.softMinimum_pair [DecidableEq V]
    {β : ℝ} (hβ : β ≠ 0) {n : ℕ} {f g : (V → ℝ) → ℝ}
    (hf : SmoothBottleneckBound β n f) (hg : SmoothBottleneckBound β n g) :
    SmoothBottleneckBound β (n + 1) (fun F => LatticeProb.softMinimum β ![f F, g F]) := by
  have hh : ∀ i : Fin 2, SmoothBottleneckBound β n (![f, g] i) := by
    intro i
    fin_cases i
    · exact hf
    · exact hg
  have he : (fun F => LatticeProb.softMinimum β (fun i => ![f, g] i F)) =
      (fun F => LatticeProb.softMinimum β ![f F, g F]) := by
    funext F
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [← he]
  exact SmoothBottleneckBound.softMinimum hβ hh

/-- `smoothBoundedBottleneck G β n a b h` satisfies `SmoothBottleneckBound β (2n + 1)` for every
`n`, by induction: the base case composes two coordinate projections via
`SmoothBottleneckBound.softMinimum_pair`, and the successor case composes the `n`-th-layer bounds
of the two halves via `softMinimum_pair` and then adds one more `SmoothBottleneckBound.softMaximum`
layer over the midpoints. -/
lemma smoothBoundedBottleneck_bound [DecidableEq V] {β : ℝ} (hβ : β ≠ 0) :
    ∀ (n : ℕ) (a b : V) (h : BoundedReach G n a b),
      SmoothBottleneckBound β (2 * n + 1) (smoothBoundedBottleneck G β n a b h) := by
  intro n
  induction n with
  | zero =>
    intro a b h
    exact SmoothBottleneckBound.softMinimum_pair hβ
      (smoothBottleneckBound_coordinate β a) (smoothBottleneckBound_coordinate β b)
  | succ n ih =>
    intro a b h
    letI : Nonempty (walkMidpoints G n a b) := by
      obtain ⟨c, hc⟩ := walkMidpoints_nonempty G h
      exact ⟨⟨c, hc⟩⟩
    have hm (c : walkMidpoints G n a b) := SmoothBottleneckBound.softMinimum_pair hβ
      (ih a c ((mem_walkMidpoints G n a b c).mp c.property).1)
      (ih c b ((mem_walkMidpoints G n a b c).mp c.property).2)
    have hh := SmoothBottleneckBound.softMaximum hβ hm
    convert hh using 1 <;> congr 1

/-- `boundedBottleneckValue` is exactly the bottleneck-value optimum among walks of length at
most `2^n`: every such walk's `walkBottleneck` is bounded above by it, and some such walk attains
it, proved by induction using `walkBottleneck_take_drop` at the recursive midpoint split. -/
lemma boundedBottleneckValue_spec [DecidableEq V] :
    ∀ (n : ℕ) (a b : V) (h : BoundedReach G n a b) (F : V → ℝ),
      (∀ p : G.Walk a b, p.length ≤ 2 ^ n →
        walkBottleneck p F ≤ boundedBottleneckValue G n a b h F) ∧
      (∃ p : G.Walk a b, p.length ≤ 2 ^ n ∧
        walkBottleneck p F = boundedBottleneckValue G n a b h F) := by
  intro n
  induction n with
  | zero =>
    intro a b h F
    constructor
    · intro p hp
      exact (walkBottleneck_of_length_le_one p F (by simpa using hp)).le
    · obtain ⟨p, hp⟩ := h
      exact ⟨p, hp, walkBottleneck_of_length_le_one p F (by simpa using hp)⟩
  | succ n ih =>
    intro a b h F
    letI : Nonempty (walkMidpoints G n a b) := by
      obtain ⟨c, hc⟩ := walkMidpoints_nonempty G h
      exact ⟨⟨c, hc⟩⟩
    let fmid (c : walkMidpoints G n a b) :=
      min (boundedBottleneckValue G n a c ((mem_walkMidpoints G n a b c).mp c.property).1 F)
        (boundedBottleneckValue G n c b ((mem_walkMidpoints G n a b c).mp c.property).2 F)
    have he : boundedBottleneckValue G (n + 1) a b h F = finiteMaximum fmid := rfl
    rw [he]
    constructor
    · intro p hp
      have hp1 : (p.take (2 ^ n)).length ≤ 2 ^ n := by
        rw [SimpleGraph.Walk.take_length]
        exact min_le_left _ _
      have hp2 : (p.drop (2 ^ n)).length ≤ 2 ^ n := by
        rw [SimpleGraph.Walk.drop_length]
        rw [pow_succ] at hp
        omega
      have hc : p.getVert (2 ^ n) ∈ walkMidpoints G n a b :=
        (mem_walkMidpoints G n a b _).mpr ⟨⟨_, hp1⟩, ⟨_, hp2⟩⟩
      let c : walkMidpoints G n a b := ⟨p.getVert (2 ^ n), hc⟩
      have hleft := (ih a c ((mem_walkMidpoints G n a b c).mp c.property).1 F).1 _ hp1
      have hright := (ih c b ((mem_walkMidpoints G n a b c).mp c.property).2 F).1 _ hp2
      rw [walkBottleneck_take_drop p F (2 ^ n)]
      exact (min_le_min hleft hright).trans (le_finiteMaximum fmid c)
    · obtain ⟨c, hc⟩ := finiteMaximum_mem fmid
      obtain ⟨p, hp, hep⟩ := (ih a c ((mem_walkMidpoints G n a b c).mp c.property).1 F).2
      obtain ⟨q, hq, heq⟩ := (ih c b ((mem_walkMidpoints G n a b c).mp c.property).2 F).2
      refine ⟨p.append q, ?_, ?_⟩
      · rw [SimpleGraph.Walk.length_append, pow_succ]
        omega
      · rw [walkBottleneck_append, hep, heq, hc]

/-- Two-term smooth-minimum error bound: if `a', b'` approximate `a, b` to within `e`, then
`LatticeProb.softMinimum β ![a', b']` approximates `min a b` to within `e` plus the fixed
two-term Gibbs bias `log 2 / β`. -/
lemma abs_softMinimum_pair_sub_min {β : ℝ} (hβ : 0 < β)
    (a b a' b' : ℝ) {e : ℝ} (ha : |a' - a| ≤ e) (hb : |b' - b| ≤ e) :
    |LatticeProb.softMinimum β ![a', b'] - min a b| ≤ e + Real.log 2 / β := by
  have hhi : LatticeProb.softMinimum β ![a, b] ≤ min a b := by
    exact le_min (by simpa using softMinimum_le hβ ![a, b] 0)
      (by simpa using softMinimum_le hβ ![a, b] 1)
  have hlo : min a b - Real.log 2 / β ≤ LatticeProb.softMinimum β ![a, b] := by
    have hh : ∀ i : Fin 2, min a b ≤ ![a, b] i := by
      intro i
      fin_cases i
      · exact min_le_left _ _
      · exact min_le_right _ _
    simpa using le_softMinimum hβ ![a, b] (min a b) hh
  have hold : |LatticeProb.softMinimum β ![a, b] - min a b| ≤ Real.log 2 / β := by
    rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
    linarith
  have he : |LatticeProb.softMinimum β ![a', b'] - LatticeProb.softMinimum β ![a, b]| ≤ e := by
    apply abs_softMinimum_sub_le hβ
    intro i
    fin_cases i
    · exact ha
    · exact hb
  exact (abs_sub_le _ (LatticeProb.softMinimum β ![a, b]) _).trans (add_le_add he hold)

/-- The main approximation theorem: `smoothBoundedBottleneck` differs from the exact
`boundedBottleneckValue` by at most `(n+1) · (log(card V) + log 2) / β`, proved by induction,
combining `abs_softMinimum_pair_sub_min` at the base layer and `abs_softMaximum_sub_finiteMaximum`
for the recursive max-over-midpoints step, bounding each layer's logarithmic term via
`Fintype.card (walkMidpoints ...) ≤ Fintype.card V`. -/
lemma smoothBoundedBottleneck_error {β : ℝ} (hβ : 0 < β) :
    ∀ (n : ℕ) (a b : V) (h : BoundedReach G n a b) (F : V → ℝ),
      |smoothBoundedBottleneck G β n a b h F - boundedBottleneckValue G n a b h F| ≤
        (n + 1 : ℝ) * (Real.log (Fintype.card V) + Real.log 2) / β := by
  intro n
  induction n with
  | zero =>
    intro a b h F
    letI : Nonempty V := ⟨a⟩
    have hN : 0 ≤ Real.log (Fintype.card V) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
    have hh := abs_softMinimum_pair_sub_min hβ (F a) (F b) (F a) (F b)
      (e := 0) (by simp) (by simp)
    change |LatticeProb.softMinimum β ![F a, F b] - min (F a) (F b)| ≤ _
    simpa only [Nat.cast_zero, zero_add, one_mul] using hh.trans
      (by rw [zero_add]; apply div_le_div_of_nonneg_right _ hβ.le; linarith)
  | succ n ih =>
    intro a b h F
    classical
    letI : Nonempty (walkMidpoints G n a b) := by
      obtain ⟨c, hc⟩ := walkMidpoints_nonempty G h
      exact ⟨⟨c, hc⟩⟩
    let fmid (c : walkMidpoints G n a b) :=
      min (boundedBottleneckValue G n a c ((mem_walkMidpoints G n a b c).mp c.property).1 F)
        (boundedBottleneckValue G n c b ((mem_walkMidpoints G n a b c).mp c.property).2 F)
    let smid (c : walkMidpoints G n a b) := LatticeProb.softMinimum β ![
      smoothBoundedBottleneck G β n a c ((mem_walkMidpoints G n a b c).mp c.property).1 F,
      smoothBoundedBottleneck G β n c b ((mem_walkMidpoints G n a b c).mp c.property).2 F]
    let E : ℝ := (n + 1 : ℝ) * (Real.log (Fintype.card V) + Real.log 2) / β
    have herr (c : walkMidpoints G n a b) : |smid c - fmid c| ≤ E + Real.log 2 / β :=
      abs_softMinimum_pair_sub_min hβ _ _ _ _
        (ih a c ((mem_walkMidpoints G n a b c).mp c.property).1 F)
        (ih c b ((mem_walkMidpoints G n a b c).mp c.property).2 F)
    have hcard : Fintype.card (walkMidpoints G n a b) ≤ Fintype.card V := by
      simpa only [Fintype.card_coe] using (walkMidpoints G n a b).card_le_univ
    have hlog : Real.log (Fintype.card (walkMidpoints G n a b)) ≤ Real.log (Fintype.card V) :=
      Real.log_le_log (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast hcard)
    change |softMaximum β smid - finiteMaximum fmid| ≤ _
    apply (abs_softMaximum_sub_finiteMaximum hβ smid fmid herr).trans
    calc
      _ ≤ E + Real.log 2 / β + Real.log (Fintype.card V) / β :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hlog hβ.le)
      _ = _ := by dsimp only [E]; push_cast; ring

end Sandpile
