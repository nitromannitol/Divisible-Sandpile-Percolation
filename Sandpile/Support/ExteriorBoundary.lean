import Sandpile.Support.CascadeGeometry

/-!
# Exterior Boundary and Axis-Ray Annular Crossings

Exterior rays, finite lattice components and annular boundary witnesses.

This module builds the machinery for finding a star-lattice annular crossing
near the origin from two far-apart points of a finite, connected set `Γ`: it
develops basic closure properties of `LatticeProb.componentIn`, the exterior
vertex boundary `exteriorVertexBoundary` (points outside `D` reachable from `D`
by a single step and escaping to infinity along a simple path avoiding `D`),
and integer points `axisSite i n` running out along a single coordinate axis,
then combines these with `exists_star_subcrossing` to locate a crossing at a
dyadic-in-base-64 scale bounded in terms of the diameter of `Γ`.
-/

namespace Sandpile

/-- Exterior nearest-neighbor boundary, with accessibility expressed by a simple infinite path. -/
def exteriorVertexBoundary {d : ℕ} (D : Set (Site d)) : Set (Site d) :=
  {z | z ∉ D ∧ (∃ y ∈ D, (lattice d).Adj y z) ∧
    ∃ p : ℕ → Site d, Function.Injective p ∧ p 0 = z ∧
      ∀ n, p n ∉ D ∧ (lattice d).Adj (p n) (p (n + 1))}

/-- The connected component `LatticeProb.componentIn O x` is a subset of `O`, immediate from
unpacking its defining witness of `O`-membership. -/
lemma componentIn_subset {d : ℕ} (O : Set (Site d)) (x : Site d) :
    LatticeProb.componentIn O x ⊆ O := by
  rintro y ⟨_, hy, _⟩
  exact hy

/-- A point `x ∈ O` lies in its own component `LatticeProb.componentIn O x`, via reflexivity of
reachability in the induced graph. -/
lemma mem_componentIn_self {d : ℕ} {O : Set (Site d)} {x : Site d} (hx : x ∈ O) :
    x ∈ LatticeProb.componentIn O x := ⟨hx, hx, SimpleGraph.Reachable.refl _⟩

/-- `LatticeProb.componentIn O x` is closed under stepping to an `O`-adjacent neighbor: if `y` is
in the component and `z ∈ O` is `(lattice d)`-adjacent to `y`, then `z` is in the component too. -/
lemma mem_componentIn_of_adj {d : ℕ} {O : Set (Site d)} {x y z : Site d}
    (hy : y ∈ LatticeProb.componentIn O x) (hz : z ∈ O) (hyz : (lattice d).Adj y z) :
    z ∈ LatticeProb.componentIn O x := by
  obtain ⟨hx, hyO, hxy⟩ := hy
  exact ⟨hx, hz, hxy.trans (show ((lattice d).induce O).Adj ⟨y, hyO⟩ ⟨z, hz⟩ from hyz).reachable⟩

/-- The induced subgraph on `LatticeProb.componentIn O x` is connected, proved by mapping the
connected component of `⟨x, hx⟩` in `(lattice d).induce O` onto it via a graph homomorphism. -/
lemma componentIn_connected {d : ℕ} (O : Set (Site d)) (x : Site d) (hx : x ∈ O) :
    ((lattice d).induce (LatticeProb.componentIn O x)).Connected := by
  let C := ((lattice d).induce O).connectedComponentMk ⟨x, hx⟩
  let f : C.toSimpleGraph →g (lattice d).induce (LatticeProb.componentIn O x) :=
    { toFun := fun y => ⟨y.val.val, hx, y.val.property,
        SimpleGraph.ConnectedComponent.exact y.property.symm⟩
      map_rel' := fun h => h }
  apply C.connected_toSimpleGraph.map f
  rintro ⟨y, hy⟩
  obtain ⟨_, hyO, hxy⟩ := hy
  exact ⟨⟨⟨y, hyO⟩, SimpleGraph.ConnectedComponent.sound hxy.symm⟩, rfl⟩

/-- The exterior vertex boundary of `LatticeProb.componentIn O x` is disjoint from `O`: a point of
the boundary adjacent to a point of `O ∩ LatticeProb.componentIn O x` would itself lie in the
component by `mem_componentIn_of_adj`, contradicting that it is outside the component. -/
lemma exteriorVertexBoundary_componentIn_subset {d : ℕ} (O : Set (Site d)) (x : Site d) :
    exteriorVertexBoundary (LatticeProb.componentIn O x) ⊆ Oᶜ := by
  rintro z ⟨hz, ⟨y, hy, hyz⟩, _⟩ hzO
  exact hz (mem_componentIn_of_adj hy hzO hyz)

/-- The exterior vertex boundary of a finite set `D` is finite: every boundary point is a
neighbor of some point of `D`, so the boundary is covered by the finite union, over `D`, of
each point's finite neighbor set. -/
lemma exteriorVertexBoundary_finite {d : ℕ} {D : Set (Site d)} (hD : D.Finite) :
    (exteriorVertexBoundary D).Finite := by
  classical
  apply (hD.biUnion (fun y _ => (LatticeProb.nbrFinset y).finite_toSet)).subset
  rintro z ⟨_, ⟨y, hy, ⟨i, hi | hi⟩⟩, _⟩
  · exact Set.mem_biUnion hy (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [hi]⟩)
  · exact Set.mem_biUnion hy (by
      have hz : z = y - unit i := by rw [hi]; abel
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [hz]⟩)

/-- The point on coordinate axis `i` at integer position `n`: all coordinates zero except the
`i`-th, which is `n`. -/
def axisSite {d : ℕ} (i : Fin d) (n : ℤ) : Site d := Pi.single i n

/-- `axisSite i` is injective in `n`: two axis points agree only if their `i`-th coordinates,
which equal `n` itself, agree. -/
lemma axisSite_injective {d : ℕ} (i : Fin d) : Function.Injective (axisSite i) := by
  intro m n h
  have := congrFun h i
  simpa [axisSite] using this

/-- The box distance between two points on the same coordinate axis `i` is exactly the absolute
difference of their positions on that axis. -/
lemma boxDist_axisSite {d : ℕ} (i : Fin d) (m n : ℤ) :
    boxDist (axisSite i m) (axisSite i n) = (m - n).natAbs := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    by_cases h : j = i
    · subst j; simp [axisSite]
    · simp [axisSite, Pi.single_eq_of_ne h]
  · have h := Finset.le_sup (f := fun j =>
        (axisSite i m j - axisSite i n j).natAbs) (Finset.mem_univ i)
    simpa [axisSite, boxDist] using h

/-- Consecutive points on the same coordinate axis are lattice-adjacent: `axisSite i n` and
`axisSite i (n + 1)` differ by the unit vector `unit i`. -/
lemma axisSite_adj {d : ℕ} (i : Fin d) (n : ℤ) :
    (lattice d).Adj (axisSite i n) (axisSite i (n + 1)) := by
  refine ⟨i, Or.inl ?_⟩
  ext j
  by_cases h : j = i
  · subst j; simp [axisSite, unit]
  · simp [axisSite, unit, Pi.single_eq_of_ne h]

/-- If a finite set `D` contains the axis points at positions `1` and `-1` along axis `i`, then
just beyond `D`'s extent on that axis, in each direction, lies a point of the exterior vertex
boundary of `D`: the extremal `D`-points on the axis (found by `Set.exists_max_image` and
`Set.exists_min_image`) have an adjacent point outside `D`, which escapes to infinity along the
rest of the axis, itself avoiding `D` by extremality. -/
lemma exists_exterior_axis_points {d : ℕ} (i : Fin d) (D : Set (Site d))
    (hD : D.Finite) (hp : axisSite i 1 ∈ D) (hm : axisSite i (-1) ∈ D) :
    ∃ a b : ℤ, 2 ≤ a ∧ b ≤ -2 ∧
      axisSite i a ∈ exteriorVertexBoundary D ∧ axisSite i b ∈ exteriorVertexBoundary D := by
  classical
  let A : Set ℤ := axisSite i ⁻¹' D
  have hA : A.Finite := hD.preimage (axisSite_injective i).injOn
  obtain ⟨a, ha, hamax⟩ := Set.exists_max_image A id hA ⟨1, hp⟩
  obtain ⟨b, hb, hbmin⟩ := Set.exists_min_image A id hA ⟨-1, hm⟩
  have ha1 : 1 ≤ a := hamax 1 hp
  have hb1 : b ≤ -1 := hbmin (-1) hm
  refine ⟨a + 1, b - 1, by omega, by omega, ?_, ?_⟩
  · have hout : ∀ n : ℕ, axisSite i (a + 1 + n) ∉ D := by
      intro n hn
      have := hamax (a + 1 + n) hn
      change a + 1 + (n : ℤ) ≤ a at this
      omega
    refine ⟨by simpa using hout 0, ⟨axisSite i a, ha, axisSite_adj i a⟩,
      (fun n => axisSite i (a + 1 + n)), ?_, by simp, fun n => ⟨hout n, ?_⟩⟩
    · intro m n h
      have := axisSite_injective i h
      omega
    · simpa [add_assoc] using axisSite_adj i (a + 1 + (n : ℤ))
  · have hout : ∀ n : ℕ, axisSite i (b - 1 - n) ∉ D := by
      intro n hn
      have := hbmin (b - 1 - n) hn
      change b ≤ b - 1 - (n : ℤ) at this
      omega
    refine ⟨by simpa using hout 0, ⟨axisSite i b, hb, ?_⟩,
      (fun n => axisSite i (b - 1 - n)), ?_, by simp, fun n => ⟨hout n, ?_⟩⟩
    · simpa using (axisSite_adj i (b - 1)).symm
    · intro m n h
      have := axisSite_injective i h
      omega
    · have he : b - 1 - ((n + 1 : ℕ) : ℤ) + 1 = b - 1 - (n : ℤ) := by
        push_cast
        ring
      simpa only [he] using (axisSite_adj i (b - 1 - ((n + 1 : ℕ) : ℤ))).symm

/-- The axis point at position `0` is the origin, since `Pi.single i 0 = 0`. -/
lemma axisSite_zero {d : ℕ} (i : Fin d) : axisSite i 0 = 0 := by
  simp [axisSite]

/-- Every `D ≥ 3` lies strictly between two consecutive powers-of-`64`-scaled brackets
`2 · 64ⁿ < D ≤ 2 · 64^(n+1)`, found as the least `n` making the upper bound hold. -/
lemma exists_annulus_scale (D : ℕ) (hD : 3 ≤ D) :
    ∃ n : ℕ, 2 * 64 ^ n < D ∧ D ≤ 2 * 64 ^ (n + 1) := by
  have hex : ∃ n : ℕ, D ≤ 2 * 64 ^ (n + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt D (show 1 < (64 : ℕ) by norm_num)
    refine ⟨n, ?_⟩
    rw [pow_succ]
    omega
  let n := Nat.find hex
  refine ⟨n, ?_, Nat.find_spec hex⟩
  cases hn : n with
  | zero => simp only [pow_zero, mul_one]; omega
  | succ k =>
    have h := Nat.find_min hex (show k < Nat.find hex by change k < n; omega)
    exact lt_of_not_ge h

/-- A finite, connected set `Γ` containing two axis points at least `2` and at most `-2` from the
origin along the same axis contains a star-lattice annular crossing `HasStarAnnularCrossing Γ x
(64ⁿ)` centred at some `x` within `4 · 64^(n+1)` of the origin: the diameter `D` of `Γ` is pinned
between two axis points via `boxDist_axisSite`, `exists_annulus_scale` selects a scale `n` from
`D`, and `exists_star_subcrossing` supplies the crossing at that scale. -/
lemma exists_crossing_of_finite_boundary {d : ℕ} (Γ : Set (Site d))
    (hΓ : Γ.Finite) (hconn : ((starLatticeGraph d).induce Γ).Connected)
    (i : Fin d) (a b : ℤ) (ha : 2 ≤ a) (hb : b ≤ -2)
    (hpa : axisSite i a ∈ Γ) (hpb : axisSite i b ∈ Γ) :
    ∃ n : ℕ, ∃ x : Site d, boxDist x 0 ≤ 4 * 64 ^ (n + 1) ∧
      HasStarAnnularCrossing Γ x (64 ^ n) := by
  classical
  obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, hmax⟩ := Set.exists_max_image (Γ ×ˢ Γ)
    (fun p => boxDist p.1 p.2) (hΓ.prod hΓ) ⟨(axisSite i a, axisSite i b), hpa, hpb⟩
  let D := boxDist u v
  have hdiam : ∀ x ∈ Γ, ∀ y ∈ Γ, boxDist x y ≤ D :=
    fun x hx y hy => hmax (x, y) ⟨hx, hy⟩
  have hab : (a - b).natAbs ≤ D := by
    simpa only [boxDist_axisSite] using hdiam _ hpa _ hpb
  have hD : 3 ≤ D := by omega
  have ha0 : boxDist (axisSite i a) 0 ≤ D := by
    rw [← axisSite_zero i, boxDist_axisSite]
    omega
  have hu0 : boxDist u 0 ≤ 2 * D := by
    have htri := boxDist_trans u (axisSite i a) 0
    have hud := hdiam u hu _ hpa
    omega
  obtain ⟨n, hlow, hhigh⟩ := exists_annulus_scale D hD
  refine ⟨n, u, by omega, ?_⟩
  obtain ⟨U, hUΓ, hUbox, hUc, hUi, hUo⟩ :=
    exists_star_subcrossing Γ hconn hu hv u (64 ^ n)
      (by simp [boxDist_self]) (by rwa [boxDist_comm v u])
  exact ⟨U, hUΓ, hUbox, hUc, hUi, hUo⟩

end Sandpile
