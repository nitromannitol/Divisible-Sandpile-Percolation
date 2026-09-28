import Sandpile.Support.PlanarLaw
import Sandpile.Support.RectangleIncrement

/-!
# Rectangle crossing-value monotonicity

Rectangle monotonicity: wider and taller rectangles have larger crossing events,
and the measurability of planar crossing events.
-/

noncomputable section
namespace Sandpile

/-- Along a walk `p` from `a` to `b` where each step changes an integer function `f` by at
most `1`, if `f a ≤ k ≤ f b` then some prefix of `p` reaches a vertex `c` with `f c = k`
exactly, using only vertices of `p` and keeping `f ≤ k` throughout the prefix. -/
lemma walk_prefix_hit_integer {V : Type*} {G : SimpleGraph V} (f : V → ℤ)
    (hstep : ∀ x y, G.Adj x y → |f y - f x| ≤ 1) {a b : V} (p : G.Walk a b) (k : ℤ) :
    f a ≤ k → k ≤ f b → ∃ (c : V) (q : G.Walk a c), f c = k ∧ q.support ⊆ p.support ∧
      ∀ z ∈ q.support, f z ≤ k := by
  induction p with
  | @nil a =>
    intro ha hb
    refine ⟨_, .nil, le_antisymm ha hb, fun _ hz => hz, ?_⟩
    intro z hz
    have he : z = a := by simpa using hz
    simpa only [he] using ha
  | @cons a b c hab p ih =>
    intro ha hc
    by_cases he : f a = k
    · refine ⟨a, .nil, he, ?_, ?_⟩
      · intro z hz
        have hz' : z = a := by simpa using hz
        subst z
        exact (SimpleGraph.Walk.cons hab p).start_mem_support
      · intro z hz
        have hz' : z = a := by simpa using hz
        simpa only [hz'] using ha
    · have hb : f b ≤ k := by
        have hh := (abs_le.mp (hstep a b hab)).2
        omega
      obtain ⟨z, q, hz, hsub, hbound⟩ := ih hb hc
      refine ⟨z, .cons hab q, hz, ?_, ?_⟩
      · intro t ht
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ht ⊢
        exact ht.imp_right (fun ht => hsub ht)
      · intro t ht
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ha
        · exact hbound t ht

/-- A vertex `z` of the induced walk `p.induce S hp` corresponds to a vertex of the original
walk `p`: `(z : V) ∈ p.support`, obtained by mapping the induced walk back through
`SimpleGraph.Embedding.induce S` and using `SimpleGraph.Walk.map_induce`. -/
lemma walk_mem_support_of_induce {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (S : Set V) (hp : ∀ z ∈ p.support, z ∈ S) {z : S}
    (hz : z ∈ (p.induce S hp).support) : (z : V) ∈ p.support := by
  have hm : (z : V) ∈ ((p.induce S hp).map (SimpleGraph.Embedding.induce S).toHom).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  rw [SimpleGraph.Walk.map_induce] at hm
  exact hm

/-- The horizontal `crossingValue` combines monotonicity in width with antitonicity in height:
for `w ≤ W` and `h ≤ H`, `crossingValue (planeRectangle W h) F ≤
crossingValue (planeRectangle w H) F`, since a bottleneck-optimal crossing of the `W × h`
rectangle restricts, after being cut off at column `w` via `walk_prefix_hit_integer`, to an
admissible crossing of the taller `w × H` rectangle. -/
lemma crossingValue_width_height_mono {w W h H : ℕ} (hw : w ≤ W) (hh : h ≤ H)
    (F : Site 2 → ℝ) :
    crossingValue (planeRectangle W h) (fun z => F z) ≤
      crossingValue (planeRectangle w H) (fun z => F z) := by
  classical
  obtain ⟨a, b, p, _, ha, hb, he⟩ := (crossingValue_spec
    (isLatticeRectangle_planeRectangle W h) (planeRectangle_nonempty W h) (fun z => F z)).2
  have ha0 := (mem_rectangleLeft_planeRectangle a).mp ha
  have hb0 := (mem_rectangleRight_planeRectangle b).mp hb
  have hstep (z t : planeRectangle W h) (hzt : (rectangleGraph (planeRectangle W h)).Adj z t) :
      |(t : Site 2) 0 - (z : Site 2) 0| ≤ 1 := lattice_adj_coord_abs_le hzt 0
  obtain ⟨c, q, hc, hsub, hbound⟩ := walk_prefix_hit_integer
    (fun z : planeRectangle W h => (z : Site 2) 0) hstep p (w : ℤ)
    (by rw [ha0]; exact Nat.cast_nonneg w) (by rw [hb0]; exact_mod_cast hw)
  let f : rectangleGraph (planeRectangle W h) →g lattice 2 := ⟨Subtype.val, fun h => h⟩
  let q₀ := q.map f
  have hq₀ : ∀ z ∈ q₀.support, z ∈ (planeRectangle w H : Set (Site 2)) := by
    intro z hz
    change z ∈ (q.map f).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
    have htb := (mem_planeRectangle W h (t : Site 2)).mp t.property
    apply (mem_planeRectangle w H (t : Site 2)).mpr
    exact ⟨htb.1, hbound t ht, htb.2.2.1, htb.2.2.2.trans (by exact_mod_cast hh)⟩
  apply le_crossingValue_of_walk (isLatticeRectangle_planeRectangle w H)
    (q₀.induce (planeRectangle w H : Set (Site 2)) hq₀)
  · apply (mem_rectangleLeft_planeRectangle _).mpr
    exact ha0
  · apply (mem_rectangleRight_planeRectangle _).mpr
    exact hc
  · intro z hz
    have hz' := walk_mem_support_of_induce q₀ (planeRectangle w H : Set (Site 2)) hq₀ hz
    change (z : Site 2) ∈ (q.map f).support at hz'
    rw [SimpleGraph.Walk.support_map] at hz'
    obtain ⟨t, ht, htz⟩ := List.mem_map.mp hz'
    have hlow : crossingValue (planeRectangle W h) (fun z => F z) ≤ F (t : Site 2) := by
      rw [← he]
      exact walkBottleneck_le p (fun z => F z) (hsub ht)
    change (t : Site 2) = (z : Site 2) at htz
    simpa only [htz] using hlow

/-- `planarCrossingEvent w h level` is measurable, since it is the preimage of `[level, ∞)`
under the measurable map `F ↦ crossingValue (planeRectangle w h) F`. -/
lemma measurableSet_planarCrossingEvent (w h : ℕ) (level : ℝ) :
    MeasurableSet (planarCrossingEvent w h level) := by
  apply measurableSet_le measurable_const
  exact (measurable_crossingValue (isLatticeRectangle_planeRectangle w h)
    (planeRectangle_nonempty w h)).comp
    (measurable_pi_lambda _ (fun z : planeRectangle w h => measurable_pi_apply (z : Site 2)))

/-- `planarCrossingEvent W h level ⊆ planarCrossingEvent w H level` for `w ≤ W`, `h ≤ H`: a
field crossing the wide short rectangle at `level` also crosses the narrow tall one, by
`crossingValue_width_height_mono`. -/
lemma planarCrossingEvent_width_height_mono {w W h H : ℕ} (hw : w ≤ W) (hh : h ≤ H) (level : ℝ) :
    planarCrossingEvent W h level ⊆ planarCrossingEvent w H level := by
  intro F hF
  exact hF.trans (crossingValue_width_height_mono hw hh F)

end Sandpile
