import Mathlib
import Sandpile.Support.BallCrossingDefinitions

/-!
# Replacing a crossing through small low components by a nearby field level

Given a crossing whose path may dip into a set `S` of low field values, this file replaces the
crossing by one lying in a nearby sublevel set of the field, provided every connected component
of `S` reached along the path has bounded diameter and the field oscillates little over that
diameter plus one edge. The key lemma `walk_field_le_of_small_components` bounds the field along
the whole walk by the bound on the complementary set `T` plus the oscillation allowance.
`star_crossing_of_small_components` and `star_crossing_field_split` specialize this to
star-graph crossings and to a field split as `H + N`, respectively.
-/

open Set

namespace Sandpile

/-- Any two vertices `z` and `w` on the support of a walk `p : G.Walk u v` are joined by a walk
`q : G.Walk z w` whose support stays inside `p.support`, built from the reversal of the initial
segment to `z` appended to the segment to `w`. -/
lemma walk_between_support {V : Type*} {G : SimpleGraph V} {u v z w : V}
    (p : G.Walk u v) (hz : z ∈ p.support) (hw : w ∈ p.support) :
    ∃ q : G.Walk z w, q.support ⊆ p.support := by
  classical
  refine ⟨(p.takeUntil z hz).reverse.append (p.takeUntil w hw), ?_⟩
  intro y hy
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hy with hleft | hright
  · have hh : y ∈ (p.takeUntil z hz).support := by simpa using hleft
    exact (p.support_takeUntil_subset_support hz) hh
  · exact (p.support_takeUntil_subset_support hw) hright

/-- If a walk `p` lies in `S ∪ T` and leaves `S` somewhere along its support, the `S`-component of
a chosen point `z ∈ S ∩ p.support` has a boundary dart: some `a` reachable from `z` inside
`G.induce S` is adjacent to some `b ∈ T ∩ p.support`, extracted via
`SimpleGraph.Walk.exists_boundary_dart` on the sub-walk between `z` and the first point outside
`S`. -/
lemma walk_exists_adjacent_to_component {V : Type*} {G : SimpleGraph V} {u v z : V}
    (p : G.Walk u v) {S T : Set V} (hST : ∀ y ∈ p.support, y ∈ S ∪ T)
    (hzp : z ∈ p.support) (hz : z ∈ S) (hout : ∃ w ∈ p.support, w ∉ S) :
    ∃ a : S, ∃ b ∈ p.support, b ∈ T ∧ G.Adj a b ∧
      (G.induce S).Reachable ⟨z, hz⟩ a := by
  classical
  let C : Set V := {y | ∃ hy : y ∈ S, (G.induce S).Reachable ⟨z, hz⟩ ⟨y, hy⟩}
  have hzC : z ∈ C := ⟨hz, SimpleGraph.Reachable.refl _⟩
  obtain ⟨w, hwp, hwS⟩ := hout
  have hwC : w ∉ C := fun hw => hwS hw.choose
  obtain ⟨q, hq⟩ := walk_between_support p hzp hwp
  obtain ⟨d, hd, hdC, hdout⟩ := q.exists_boundary_dart C hzC hwC
  obtain ⟨haS, hreach⟩ := hdC
  have hbS : d.snd ∉ S := by
    intro hb
    apply hdout
    exact ⟨hb, hreach.trans (SimpleGraph.Adj.reachable
      (show (G.induce S).Adj ⟨d.fst, haS⟩ ⟨d.snd, hb⟩ from d.adj))⟩
  have hbp : d.snd ∈ p.support := hq (q.dart_snd_mem_support_of_mem_darts hd)
  exact ⟨⟨d.fst, haS⟩, d.snd, hbp, (hST d.snd hbp).resolve_left hbS, d.adj, hreach⟩

/-- If every pair reachable within the induced graph on `S` is within distance `D` of each other
but the endpoints `u` and `v` of `p` are farther apart than `D`, then `p`'s support cannot stay
inside `S`. -/
lemma walk_not_subset_of_component_diameter {V : Type*} [PseudoMetricSpace V]
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (S : Set V) {D : ℝ}
    (hdiam : ∀ a b : S, (G.induce S).Reachable a b → dist (a : V) (b : V) ≤ D)
    (hgap : D < dist u v) : ∃ w ∈ p.support, w ∉ S := by
  by_contra hh
  push Not at hh
  have hreach := (p.induce S hh).reachable
  exact hgap.not_ge (hdiam _ _ hreach)

/-- Given a bound `level` on `H` over `T`, an oscillation bound `η` for `H` over pairs on the walk
within distance `D + step`, and a diameter bound `D` on `S`-components that is smaller than
`dist u v`, every point of the walk's support satisfies `H z ≤ level + η`: a point in `S` is within
`D + step` of an adjacent point that must lie in `T`, by `walk_exists_adjacent_to_component` and
`walk_not_subset_of_component_diameter`. -/
lemma walk_field_le_of_small_components {V : Type*} [PseudoMetricSpace V]
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) {S T : Set V}
    (hST : ∀ y ∈ p.support, y ∈ S ∪ T) {D step η level : ℝ} (hη : 0 ≤ η)
    (hdiam : ∀ a b : S, (G.induce S).Reachable a b → dist (a : V) (b : V) ≤ D)
    (hstep : ∀ a b, G.Adj a b → dist a b ≤ step) (hgap : D < dist u v)
    (H : V → ℝ) (hT : ∀ y ∈ T, H y ≤ level)
    (hosc : ∀ a ∈ p.support, ∀ b ∈ p.support, dist a b ≤ D + step → |H a - H b| ≤ η) :
    ∀ z ∈ p.support, H z ≤ level + η := by
  intro z hzp
  by_cases hzT : z ∈ T
  · exact (hT z hzT).trans (le_add_of_nonneg_right hη)
  · have hzS : z ∈ S := (hST z hzp).resolve_right hzT
    obtain ⟨a, b, hbp, hbT, hadj, hreach⟩ := walk_exists_adjacent_to_component p hST hzp hzS
      (walk_not_subset_of_component_diameter p S hdiam hgap)
    have hd : dist z b ≤ D + step := (dist_triangle z a b).trans
      (add_le_add (hdiam ⟨z, hzS⟩ a hreach) (hstep a b hadj))
    have hh := (abs_le.mp (hosc z hzp b hbp hd)).2
    linarith [hT b hbT]

/-- Adjacent sites in `starGraph` on `Site 4` are at `dist`-distance at most `1`, since adjacency
bounds each coordinate's integer difference by `1`. -/
lemma dist_le_one_of_starGraph_adj {z w : Site 4} (h : starGraph.Adj z w) : dist z w ≤ 1 := by
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  rw [Int.dist_eq']
  exact_mod_cast h.2.1 i

/-- A top-bottom star crossing of `S ∪ T` for the star graph on `Site 4` gives a top-bottom star
crossing of the sublevel set `{z | H z ≤ level + η}`, by applying
`walk_field_le_of_small_components` to the crossing's chain, using that star-graph edges have
`dist`-length at most `1` (`dist_le_one_of_starGraph_adj`) and that the chain's vertical span
`r` exceeds the `S`-component diameter `D`. -/
lemma star_crossing_of_small_components {ϑ : ℝ} {r : ℕ} {x : Site 4}
    {S T : Set (Site 4)} {D η level : ℝ} (hη : 0 ≤ η) (hD : D < (r : ℝ))
    (hdiam : ∀ a b : S, (starGraph.induce S).Reachable a b → dist (a : Site 4) (b : Site 4) ≤ D)
    (H : Site 4 → ℝ) (hT : ∀ z ∈ T, H z ≤ level)
    (hosc : ∀ z ∈ ballRect ϑ r x, ∀ w ∈ ballRect ϑ r x,
      dist z w ≤ D + 1 → |H z - H w| ≤ η)
    (hcross : HasStarTopBottomCrossing ϑ r x (S ∪ T)) :
    HasStarTopBottomCrossing ϑ r x {z | H z ≤ level + η} := by
  obtain ⟨Γ, hΓ, hmem, hchain, hhead, hlast⟩ := hcross
  let p := SimpleGraph.Walk.ofSupport Γ hΓ hchain
  have hp : p.support = Γ := SimpleGraph.Walk.support_ofSupport hΓ hchain
  have htop : (Γ.head hΓ) 1 = x 1 + (r : ℤ) :=
    hhead _ (by simp [List.head?_eq_some_head hΓ])
  have hbot : (Γ.getLast hΓ) 1 = x 1 :=
    hlast _ (by simp [List.getLast?_eq_getLast_of_ne_nil hΓ])
  have hgap : D < dist (Γ.head hΓ) (Γ.getLast hΓ) := by
    apply hD.trans_le
    calc
      (r : ℝ) = dist ((Γ.head hΓ) 1) ((Γ.getLast hΓ) 1) := by
        rw [htop, hbot, Int.dist_eq]
        push_cast
        simp only [add_sub_cancel_left]
        exact (abs_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) from Nat.cast_nonneg r)).symm
      _ ≤ _ := dist_le_pi_dist _ _ 1
  have hh := walk_field_le_of_small_components p (fun z hz => (hmem z (hp ▸ hz)).1)
    hη hdiam (fun _ _ h => dist_le_one_of_starGraph_adj h) hgap H hT
    (fun z hz w hw hd => hosc z (hmem z (hp ▸ hz)).2 w (hmem w (hp ▸ hw)).2 hd)
  refine ⟨Γ, hΓ, ?_, hchain, hhead, hlast⟩
  intro z hz
  exact ⟨hh z (hp.symm ▸ hz), (hmem z hz).2⟩

/-- Splitting `F = H + N`, a top-bottom star crossing of `{z | F z ≤ level - δ}` gives a top-bottom
star crossing of `{z | H z ≤ level + η}`, by applying `star_crossing_of_small_components` with
`S = {z | N z ≤ -δ}` and `T = {z | H z ≤ level}`: off `S`, the bounds `F z ≤ level - δ` and
`N z > -δ` force `H z ≤ level`. -/
lemma star_crossing_field_split {ϑ : ℝ} {r : ℕ} {x : Site 4}
    (F H N : Site 4 → ℝ) (hF : ∀ z, F z = H z + N z)
    {D δ η level : ℝ} (hη : 0 ≤ η) (hD : D < (r : ℝ))
    (hdiam : ∀ a b : {z | z ∈ ballRect ϑ r x ∧ N z ≤ -δ},
      (starGraph.induce {z | z ∈ ballRect ϑ r x ∧ N z ≤ -δ}).Reachable a b →
        dist (a : Site 4) (b : Site 4) ≤ D)
    (hosc : ∀ z ∈ ballRect ϑ r x, ∀ w ∈ ballRect ϑ r x,
      dist z w ≤ D + 1 → |H z - H w| ≤ η)
    (hcross : HasStarTopBottomCrossing ϑ r x {z | F z ≤ level - δ}) :
    HasStarTopBottomCrossing ϑ r x {z | H z ≤ level + η} := by
  apply star_crossing_of_small_components (S := {z | z ∈ ballRect ϑ r x ∧ N z ≤ -δ})
    (T := {z | H z ≤ level}) hη hD hdiam H (fun _ h => h) hosc
  obtain ⟨Γ, hΓ, hmem, hchain, hhead, hlast⟩ := hcross
  refine ⟨Γ, hΓ, ?_, hchain, hhead, hlast⟩
  intro z hz
  obtain ⟨hlow, hrect⟩ := hmem z hz
  refine ⟨?_, hrect⟩
  by_cases hn : N z ≤ -δ
  · exact Or.inl ⟨hrect, hn⟩
  · apply Or.inr
    change H z ≤ level
    change F z ≤ level - δ at hlow
    rw [hF z] at hlow
    linarith

end Sandpile
