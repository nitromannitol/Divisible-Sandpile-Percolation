import Sandpile.Support.CrossingDefinitions
import Sandpile.Support.BoundedBottleneck

/-!
# Smooth crossing values for finite lattice rectangles

Smooth crossing values for finite lattice rectangles. Coordinate paths give connectivity
(`rectangleGraph_preconnected`, built by moving one coordinate at a time with
`rectangle_update_reachable`), loop removal identifies the bounded-walk maximum
`boundedBottleneckValue` with the simple-path crossing value `crossingValue`
(`crossingValue_eq_bounded_max`), and a logarithmic recursion depth
(`exists_logarithmic_walk_depth`) gives a smooth approximation `L` to `crossingValue` with the
three coordinate-derivative bounds `SmoothBottleneckBound` at an error and a depth both
logarithmic in the rectangle's cardinality (`rectangle_smooth_bottleneck_at_depth`,
`exists_smooth_rectangle_bottleneck`).
-/

open LatticeProb

namespace Sandpile

/-- The subgraph of `lattice 2` induced on a finite rectangle `Q`: adjacency of sites of `Q` in
the ambient lattice. -/
noncomputable def rectangleGraph (Q : Finset (Site 2)) : SimpleGraph Q :=
  (lattice 2).induce (Q : Set (Site 2))

/-- Updating a single coordinate `i` of a point `x ∈ Q` to any value `t` between the rectangle's
bounds in that coordinate keeps the result in `Q`, since the other coordinates are unaffected and
already satisfy the rectangle's bounds. -/
lemma rectangle_update_mem {Q : Finset (Site 2)} {lo hi : Site 2}
    (hQ : ∀ z : Site 2, z ∈ Q ↔ ∀ i : Fin 2, lo i ≤ z i ∧ z i ≤ hi i)
    {x : Site 2} (hx : x ∈ Q) (i : Fin 2) {t : ℤ} (htlo : lo i ≤ t) (hthi : t ≤ hi i) :
    Function.update x i t ∈ Q := by
  rw [hQ]
  intro j
  by_cases hj : j = i
  · subst j; simpa using And.intro htlo hthi
  · simpa only [Function.update_of_ne hj] using (hQ x).mp hx j

/-- Increasing coordinate `i` of `x ∈ Q` from its current value up to any target `t ≤ hi i` stays
inside `Q` and is reachable in `rectangleGraph Q`: induct on `t` with `Int.leInduction`, each
step being a single unit move along axis `i`. -/
lemma rectangle_update_reachable_ge {Q : Finset (Site 2)} {lo hi : Site 2}
    (hQ : ∀ z : Site 2, z ∈ Q ↔ ∀ i : Fin 2, lo i ≤ z i ∧ z i ≤ hi i)
    {x : Site 2} (hx : x ∈ Q) (i : Fin 2) {t : ℤ} (hxt : x i ≤ t) (hthi : t ≤ hi i) :
    (rectangleGraph Q).Reachable ⟨x, hx⟩
      ⟨Function.update x i t,
        rectangle_update_mem hQ hx i ((hQ x).mp hx i |>.1.trans hxt) hthi⟩ := by
  have H : ∀ (t : ℤ) (hxt : x i ≤ t) (hthi : t ≤ hi i),
      (rectangleGraph Q).Reachable ⟨x, hx⟩
        ⟨Function.update x i t,
          rectangle_update_mem hQ hx i ((hQ x).mp hx i |>.1.trans hxt) hthi⟩ := by
    apply Int.leInduction
    · intro ht
      simpa only [Function.update_eq_self] using
        (SimpleGraph.Reachable.refl (G := rectangleGraph Q) ⟨x, hx⟩)
    · intro s hxs ih hs
      have hs' : s ≤ hi i := by omega
      apply (ih hs').trans
      apply SimpleGraph.Adj.reachable
      change (lattice 2).Adj (Function.update x i s) (Function.update x i (s + 1))
      refine ⟨i, Or.inl ?_⟩
      ext j
      by_cases hj : j = i
      · subst j
        simp [LatticeProb.unit]
      · simp [LatticeProb.unit, hj]
  exact H t hxt hthi

/-- Updating a single coordinate `i` of `x ∈ Q` to any target value `t` within the rectangle's
bounds is reachable in `rectangleGraph Q`, whether `t` is above or below the current value: the
increasing case is `rectangle_update_reachable_ge` directly, and the decreasing case follows from
it applied in reverse. -/
lemma rectangle_update_reachable {Q : Finset (Site 2)} {lo hi : Site 2}
    (hQ : ∀ z : Site 2, z ∈ Q ↔ ∀ i : Fin 2, lo i ≤ z i ∧ z i ≤ hi i)
    {x : Site 2} (hx : x ∈ Q) (i : Fin 2) {t : ℤ} (htlo : lo i ≤ t) (hthi : t ≤ hi i) :
    (rectangleGraph Q).Reachable ⟨x, hx⟩
      ⟨Function.update x i t, rectangle_update_mem hQ hx i htlo hthi⟩ := by
  by_cases hxt : x i ≤ t
  · exact rectangle_update_reachable_ge hQ hx i hxt hthi
  · have hy := rectangle_update_mem hQ hx i htlo hthi
    have hh := rectangle_update_reachable_ge hQ hy i
      (t := x i) (by simp only [Function.update_self]; omega) ((hQ x).mp hx i).2
    have hh' : (rectangleGraph Q).Reachable ⟨Function.update x i t, hy⟩ ⟨x, hx⟩ := by
      simpa only [Function.update_idem, Function.update_eq_self] using hh
    exact hh'.symm

/-- `rectangleGraph Q` is preconnected for a lattice rectangle `Q`: any two points can be joined
by first moving coordinate `0` and then coordinate `1` to match, using
`rectangle_update_reachable` twice. -/
lemma rectangleGraph_preconnected {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q) :
    (rectangleGraph Q).Preconnected := by
  obtain ⟨lo, hi, hQ⟩ := hQ
  intro x y
  have hy0 := (hQ y).mp y.property 0
  have hy1 := (hQ y).mp y.property 1
  have hx' := rectangle_update_mem hQ x.property 0 hy0.1 hy0.2
  have h0 := rectangle_update_reachable hQ x.property 0 hy0.1 hy0.2
  have h1 := rectangle_update_reachable hQ hx' 1 hy1.1 hy1.2
  have he : Function.update (Function.update (x : Site 2) 0 ((y : Site 2) 0)) 1 ((y : Site 2) 1)
      = y := by
    ext i
    fin_cases i <;> simp
  simpa only [he] using h0.trans h1

/-- The left side of a rectangle `Q`: the points of `Q` whose first coordinate is minimal among
all points of `Q`. -/
noncomputable def rectangleLeft (Q : Finset (Site 2)) : Finset Q := by
  classical
  exact Finset.univ.filter (fun z : Q => ∀ w ∈ Q, (z : Site 2) 0 ≤ w 0)

/-- The right side of a rectangle `Q`: the points of `Q` whose first coordinate is maximal among
all points of `Q`. -/
noncomputable def rectangleRight (Q : Finset (Site 2)) : Finset Q := by
  classical
  exact Finset.univ.filter (fun z : Q => ∀ w ∈ Q, w 0 ≤ (z : Site 2) 0)

/-- Both `rectangleLeft Q` and `rectangleRight Q` are nonempty for a nonempty lattice rectangle:
the rectangle's own left and right corners `lo` and `hi` witness them. -/
lemma rectangle_boundaries_nonempty {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    (hN : Q.Nonempty) : (rectangleLeft Q).Nonempty ∧ (rectangleRight Q).Nonempty := by
  classical
  obtain ⟨lo, hi, hQ⟩ := hQ
  obtain ⟨z, hz⟩ := hN
  have hlohi (i : Fin 2) : lo i ≤ hi i := ((hQ z).mp hz i).1.trans ((hQ z).mp hz i).2
  have hlo : lo ∈ Q := (hQ lo).mpr fun i => ⟨le_rfl, hlohi i⟩
  have hhi : hi ∈ Q := (hQ hi).mpr fun i => ⟨hlohi i, le_rfl⟩
  constructor
  · refine ⟨⟨lo, hlo⟩, ?_⟩
    simp only [rectangleLeft, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun w hw => ((hQ w).mp hw 0).1
  · refine ⟨⟨hi, hhi⟩, ?_⟩
    simp only [rectangleRight, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun w hw => ((hQ w).mp hw 0).2

/-- The support of a simple graph path from a left-boundary point to a right-boundary point of
`Q` is a crossing path, in the sense of `IsCrossingPath`. -/
lemma isCrossingPath_of_walk {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b) (hp : p.IsPath)
    (ha : a ∈ rectangleLeft Q) (hb : b ∈ rectangleRight Q) : IsCrossingPath Q p.support := by
  classical
  have ha' : ∀ w ∈ Q, (a : Site 2) 0 ≤ w 0 := (Finset.mem_filter.mp ha).2
  have hb' : ∀ w ∈ Q, w 0 ≤ (b : Site 2) 0 := (Finset.mem_filter.mp hb).2
  refine ⟨p.support_ne_nil, hp.support_nodup, p.isChain_adj_support, ?_, ?_⟩
  · intro z hz
    have he : a = z := by
      simpa only [List.head?_eq_some_head p.support_ne_nil, p.head_support,
        Option.mem_some_iff] using hz
    subst z
    exact ha'
  · intro z hz
    have he : b = z := by
      simpa only [List.getLast?_eq_some_getLast p.support_ne_nil, p.getLast_support,
        Option.mem_some_iff] using hz
    subst z
    exact hb'

/-- The converse of `isCrossingPath_of_walk`: a crossing path `Γ` arises as the support of a
simple graph walk (via `SimpleGraph.Walk.ofSupport`) between a left-boundary and a right-boundary
point of `Q`. -/
lemma crossingPath_walk {Q : Finset (Site 2)} {Γ : List Q} (hΓ : IsCrossingPath Q Γ) :
    ∃ (a b : Q) (p : (rectangleGraph Q).Walk a b),
      p.IsPath ∧ p.support = Γ ∧ a ∈ rectangleLeft Q ∧ b ∈ rectangleRight Q := by
  classical
  let p := SimpleGraph.Walk.ofSupport (G := rectangleGraph Q) Γ hΓ.1 hΓ.2.2.1
  refine ⟨Γ.head hΓ.1, Γ.getLast hΓ.1, p, ?_, ?_, ?_, ?_⟩
  · exact (SimpleGraph.Walk.isPath_def _).mpr (by
      simpa only [p, SimpleGraph.Walk.support_ofSupport] using hΓ.2.1)
  · exact SimpleGraph.Walk.support_ofSupport _ _
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hΓ.2.2.2.1 _ (List.head_mem_head? _)⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hΓ.2.2.2.2 _ (List.getLast_mem_getLast? _)⟩

/-- Any two points of a lattice rectangle `Q` are within `BoundedReach (rectangleGraph Q) n` of
each other once `Q.card ≤ 2 ^ n`: `rectangleGraph_preconnected` gives a walk, and its bypass has
length below `Q.card` since it is a simple path in a graph on `Q.card` vertices. -/
lemma rectangle_boundedReach {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    {n : ℕ} (hn : Q.card ≤ 2 ^ n) (a b : Q) : BoundedReach (rectangleGraph Q) n a b := by
  obtain ⟨p⟩ := rectangleGraph_preconnected hQ a b
  refine ⟨p.bypass, ?_⟩
  have hh : p.bypass.length < Q.card := by simpa using p.bypass_isPath.length_lt
  exact hh.le.trans hn

/-- **The crossing value equals the bounded-walk maximum.** For a lattice rectangle `Q` with
`Q.card ≤ 2 ^ n`, `crossingValue Q F` (the supremum over crossing paths of their minimum field
value) equals the finite maximum, over all left/right boundary pairs, of the exact recursive
bottleneck `boundedBottleneckValue (rectangleGraph Q) n`: crossing paths give simple paths of
length below `Q.card ≤ 2 ^ n` by `crossingPath_walk`, and conversely a bypassed maximizing walk of
that bounded length gives a crossing path by `isCrossingPath_of_walk`, so `walkBottleneck` and
`boundedBottleneckValue` agree on the extremizers on both sides. -/
lemma crossingValue_eq_bounded_max {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    {n : ℕ} (hn : Q.card ≤ 2 ^ n)
    [Nonempty (rectangleLeft Q)] [Nonempty (rectangleRight Q)] (F : Q → ℝ) :
    crossingValue Q F = finiteMaximum (fun p : rectangleLeft Q × rectangleRight Q =>
      boundedBottleneckValue (rectangleGraph Q) n p.1 p.2
        (rectangle_boundedReach hQ hn p.1 p.2) F) := by
  classical
  let G := rectangleGraph Q
  let f (p : rectangleLeft Q × rectangleRight Q) :=
    boundedBottleneckValue G n p.1 p.2 (rectangle_boundedReach hQ hn p.1 p.2) F
  let S : Set ℝ := {v | ∃ Γ : List Q, IsCrossingPath Q Γ ∧ v = sInf (F '' {z : Q | z ∈ Γ})}
  have hu (v : ℝ) (hv : v ∈ S) : v ≤ finiteMaximum f := by
    obtain ⟨Γ, hΓ, rfl⟩ := hv
    obtain ⟨a, b, p, hp, he, ha, hb⟩ := crossingPath_walk hΓ
    have hlen : p.length ≤ 2 ^ n := (by simpa using hp.length_lt.le : p.length ≤ Q.card).trans hn
    have hh := (boundedBottleneckValue_spec G n a b (rectangle_boundedReach hQ hn a b) F).1 p hlen
    rw [← he, ← walkBottleneck_eq_csInf]
    exact hh.trans (le_finiteMaximum f (⟨a, ha⟩, ⟨b, hb⟩))
  obtain ⟨c, hc⟩ := finiteMaximum_mem f
  obtain ⟨p, _, hp⟩ := (boundedBottleneckValue_spec G n c.1 c.2
    (rectangle_boundedReach hQ hn c.1 c.2) F).2
  have hcross := isCrossingPath_of_walk p.bypass p.bypass_isPath c.1.property c.2.property
  have hm : walkBottleneck p.bypass F ∈ S :=
    ⟨p.bypass.support, hcross, walkBottleneck_eq_csInf p.bypass F⟩
  change sSup S = finiteMaximum f
  apply le_antisymm
  · exact csSup_le ⟨_, hm⟩ hu
  · apply le_trans _ (le_csSup ⟨finiteMaximum f, hu⟩ hm)
    rw [hc]
    dsimp only [f]
    rw [← hp]
    exact walkBottleneck_le_bypass p F

/-- **A smooth approximation to a rectangle's crossing value at walk depth `n`.** For a lattice
rectangle `Q` with `Q.card ≤ 2 ^ n`, the softmax `L` of `smoothBoundedBottleneck` over every
left/right boundary pair satisfies `SmoothBottleneckBound β (2n+2) L` and approximates
`crossingValue Q` to within an error `((n+1)(log Q.card + log 2) + 2 log Q.card) / β`: the bound
comes from `smoothBoundedBottleneck_bound` composed with `SmoothBottleneckBound.softMaximum`, and
the error from `crossingValue_eq_bounded_max`, `smoothBoundedBottleneck_error` and
`abs_softMaximum_sub_finiteMaximum`, the last contributing the extra `2 log Q.card / β` from the
number of boundary pairs. -/
lemma rectangle_smooth_bottleneck_at_depth {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    (hN : Q.Nonempty) {n : ℕ} (hn : Q.card ≤ 2 ^ n) {β : ℝ} (hβ : 0 < β) :
    ∃ L : (Q → ℝ) → ℝ, SmoothBottleneckBound β (2 * n + 2) L ∧
      ∀ F, |L F - crossingValue Q F| ≤
        ((n + 1 : ℝ) * (Real.log Q.card + Real.log 2) + 2 * Real.log Q.card) / β := by
  classical
  obtain ⟨hleft, hright⟩ := rectangle_boundaries_nonempty hQ hN
  letI : Nonempty (rectangleLeft Q) := ⟨⟨hleft.choose, hleft.choose_spec⟩⟩
  letI : Nonempty (rectangleRight Q) := ⟨⟨hright.choose, hright.choose_spec⟩⟩
  let P := rectangleLeft Q × rectangleRight Q
  let f (p : P) := smoothBoundedBottleneck (rectangleGraph Q) β n p.1 p.2
    (rectangle_boundedReach hQ hn p.1 p.2)
  let L (F : Q → ℝ) := softMaximum β (fun p : P => f p F)
  have hf (p : P) : SmoothBottleneckBound β (2 * n + 1) (f p) :=
    smoothBoundedBottleneck_bound (rectangleGraph Q) hβ.ne' n p.1 p.2 _
  refine ⟨L, ?_, ?_⟩
  · convert SmoothBottleneckBound.softMaximum hβ.ne' hf using 1
  · intro F
    let g (p : P) := boundedBottleneckValue (rectangleGraph Q) n p.1 p.2
      (rectangle_boundedReach hQ hn p.1 p.2) F
    have he : crossingValue Q F = finiteMaximum g := crossingValue_eq_bounded_max hQ hn F
    have herr (p : P) : |f p F - g p| ≤
        (n + 1 : ℝ) * (Real.log Q.card + Real.log 2) / β := by
      simpa only [Fintype.card_coe] using
        smoothBoundedBottleneck_error (rectangleGraph Q) hβ n p.1 p.2
          (rectangle_boundedReach hQ hn p.1 p.2) F
    have hcL : Fintype.card (rectangleLeft Q) ≤ Q.card := by
      simpa only [Fintype.card_coe] using (rectangleLeft Q).card_le_univ
    have hcR : Fintype.card (rectangleRight Q) ≤ Q.card := by
      simpa only [Fintype.card_coe] using (rectangleRight Q).card_le_univ
    have hcP : Fintype.card P ≤ Q.card ^ 2 := by
      simpa only [P, Fintype.card_prod, pow_two] using Nat.mul_le_mul hcL hcR
    have hlog : Real.log (Fintype.card P) ≤ 2 * Real.log Q.card := by
      have hh := Real.log_le_log (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card P)
        (by exact_mod_cast hcP : (Fintype.card P : ℝ) ≤ (Q.card : ℝ) ^ 2)
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
    rw [he]
    apply (abs_softMaximum_sub_finiteMaximum hβ (fun p => f p F) g herr).trans
    calc
      _ ≤ (n + 1 : ℝ) * (Real.log Q.card + Real.log 2) / β + 2 * Real.log Q.card / β :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hlog hβ.le)
      _ = _ := by ring

/-- **A logarithmic recursion depth suffices.** For every `N ≥ 2` there is `n` with `N ≤ 2 ^ n`
and `n + 1 ≤ (3 / log 2) log N`: take `n = ⌈(log N) / (log 2)⌉`, whose ceiling gives `N ≤ 2 ^ n`
after exponentiating, and whose defining bound `⌈x⌉ < x + 1` gives the linear estimate. -/
lemma exists_logarithmic_walk_depth {N : ℕ} (hN : 2 ≤ N) :
    ∃ n : ℕ, N ≤ 2 ^ n ∧ (n + 1 : ℝ) ≤ (3 / Real.log 2) * Real.log N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  let x : ℝ := Real.log N / Real.log 2
  have hx : 1 ≤ x := (le_div_iff₀ hlog2).mpr (by simpa using hlogN)
  refine ⟨Nat.ceil x, ?_, ?_⟩
  · have hn : Real.log N / Real.log 2 ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
    have he := Real.exp_le_exp.mpr ((div_le_iff₀ hlog2).mp hn)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
    rw [Real.exp_log hNpos] at he
    have hpow : Real.exp ((Nat.ceil x : ℝ) * Real.log 2) = (2 : ℝ) ^ Nat.ceil x := by
      rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
    rw [hpow] at he
    exact_mod_cast he
  · have hn := (Nat.ceil_lt_add_one (show 0 ≤ x by linarith)).le
    calc
      _ ≤ 3 * x := by linarith
      _ = _ := by dsimp only [x]; ring

/-- **A universal smooth approximation to any rectangle's crossing value.** There is a single
constant `C` such that for every lattice rectangle `Q` with at least two sites and every `β ≥ 1`,
some smooth `L` approximates `crossingValue Q` to within `C (log Q.card)² / β`, with its `k`-th
coordinate derivatives (`k = 1, 2, 3`) summing to at most `C β^{k-1} (log Q.card)^{k-1}`: obtained
from `rectangle_smooth_bottleneck_at_depth` at the logarithmic depth furnished by
`exists_logarithmic_walk_depth`, unfolding `SmoothBottleneckBound.iteratedFDeriv` for the
derivative bounds. -/
lemma exists_smooth_rectangle_bottleneck :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : Finset (Site 2), IsLatticeRectangle Q → 2 ≤ Q.card →
        ∀ β : ℝ, 1 ≤ β → ∃ L : (Q → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) L ∧
          (∀ F : Q → ℝ,
            |L F - crossingValue Q F| ≤ C * (Real.log Q.card) ^ 2 / β) ∧
          (∀ k : ℕ, 1 ≤ k → k ≤ 3 → ∀ F : Q → ℝ,
            ∑ z : Fin k → Q,
                |iteratedFDeriv ℝ k L F (fun j => Pi.single (z j) 1)| ≤
              C * β ^ (k - 1) * (Real.log Q.card) ^ (k - 1)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D : ℝ := 6 / Real.log 2
  let C : ℝ := 6 * (1 + D) ^ 2 + 8 / Real.log 2 + 1
  have hD : 0 < D := div_pos (by norm_num) hlog2
  have hc0 : 6 ≤ C := by
    dsimp only [C]; nlinarith [sq_nonneg D, div_pos (by norm_num : (0 : ℝ) < 8) hlog2]
  have hc1 : 6 * D ≤ C := by
    dsimp only [C]; nlinarith [sq_nonneg D, div_pos (by norm_num : (0 : ℝ) < 8) hlog2]
  have hc2 : 6 * D ^ 2 ≤ C := by
    dsimp only [C]; nlinarith [div_pos (by norm_num : (0 : ℝ) < 8) hlog2]
  have hcE : 8 / Real.log 2 ≤ C := by dsimp only [C]; nlinarith [sq_nonneg (1 + D)]
  refine ⟨C, by linarith, ?_⟩
  intro Q hQ hN β hβ
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hlogN : Real.log 2 ≤ Real.log Q.card :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hq : 0 < Real.log Q.card := hlog2.trans_le hlogN
  obtain ⟨n, hn, hnlog⟩ := exists_logarithmic_walk_depth hN
  obtain ⟨L, hL, he⟩ := rectangle_smooth_bottleneck_at_depth hQ
    (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hN)) hn hβpos
  refine ⟨L, hL.1, ?_, ?_⟩
  · intro F
    apply (he F).trans
    apply div_le_div_of_nonneg_right _ hβpos.le
    have hp : (n + 1 : ℝ) * (Real.log Q.card + Real.log 2) ≤
        (3 / Real.log 2) * Real.log Q.card * (2 * Real.log Q.card) :=
      mul_le_mul hnlog (by linarith) (by positivity) (by positivity)
    have hlin : 2 * Real.log Q.card ≤ (2 / Real.log 2) * (Real.log Q.card) ^ 2 := by
      apply (mul_le_mul_iff_right₀ hlog2).mp
      field_simp
      nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hlogN)]
    calc
      _ ≤ (3 / Real.log 2) * Real.log Q.card * (2 * Real.log Q.card) +
          (2 / Real.log 2) * (Real.log Q.card) ^ 2 := add_le_add hp hlin
      _ = (8 / Real.log 2) * (Real.log Q.card) ^ 2 := by ring
      _ ≤ C * (Real.log Q.card) ^ 2 := mul_le_mul_of_nonneg_right hcE (sq_nonneg _)
  · intro k hk hk' F
    have hd' : ((2 * n + 2 : ℕ) : ℝ) ≤ D * Real.log Q.card := by
      dsimp only [D]
      push_cast
      calc
        _ ≤ 2 * ((3 / Real.log 2) * Real.log Q.card) := by nlinarith [hnlog]
        _ = _ := by ring
    have hh := hL.iteratedFDeriv k hk hk' F
    rw [abs_of_pos hβpos] at hh
    interval_cases k
    · simpa only [Nat.reduceSub, pow_zero, mul_one] using hh.trans (by simpa using hc0)
    · simp only [Nat.reduceSub, pow_one] at hh ⊢
      calc
        _ ≤ 6 * β * ((2 * n + 2 : ℕ) : ℝ) := hh
        _ ≤ 6 * β * (D * Real.log Q.card) := mul_le_mul_of_nonneg_left hd' (by positivity)
        _ = (6 * D) * β * Real.log Q.card := by ring
        _ ≤ C * β * Real.log Q.card := by gcongr
    · simp only [Nat.reduceSub] at hh ⊢
      calc
        _ ≤ 6 * β ^ 2 * ((2 * n + 2 : ℕ) : ℝ) ^ 2 := hh
        _ ≤ 6 * β ^ 2 * (D * Real.log Q.card) ^ 2 := by gcongr
        _ = (6 * D ^ 2) * β ^ 2 * (Real.log Q.card) ^ 2 := by ring
        _ ≤ C * β ^ 2 * (Real.log Q.card) ^ 2 := by gcongr

end Sandpile
