import Sandpile.Support.CrossGrid
import Sandpile.Support.RectangleIntersection

/-!
# The deterministic blocking of Step 1

The blocking half of Step 1 of `prop:fixed-scale-crossings` (`sandpile.tex:2233-2235`): a
`{𝒳₁ < 0}` arm from `B(x,r₁)` to `∂B(x,r₂)` must avoid the `{𝒳₁ ≥ 0}` circuit of every annulus
it crosses, which implies the arm bound by choosing a logarithmic number of such annuli that
the arm must avoid all of them. The two ingredients are here. `exists_star_walk_of_adj_seq`
turns a sequence of consecutive adjacencies into a walk through all of them, which is what a
chain of grid points gives. `no_lattice_walk_of_levels` is the deterministic blocking:
`rectangle_nn_star_intersect` of `Sandpile/Support/RectangleIntersection.lean` says a
nearest-neighbour lattice walk of a rectangle and a star bottom-top walk of the same rectangle
must meet at a common grid point, where the two level bounds contradict each other. No Jordan
curve theorem is used.
-/

open MeasureTheory Set

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A sequence of vertices with consecutive adjacencies carries a walk through
all of them. -/
theorem exists_star_walk_of_adj_seq {V : Type*} {G : SimpleGraph V} (z : ℕ → V) (n : ℕ)
    (h : ∀ j < n, G.Adj (z j) (z (j + 1))) :
    ∃ p : G.Walk (z 0) (z n), ∀ j ≤ n, z j ∈ p.support := by
  induction n with
  | zero => exact ⟨SimpleGraph.Walk.nil, fun j hj => by
      have : j = 0 := Nat.le_zero.mp hj
      subst this; exact SimpleGraph.Walk.start_mem_support _⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    refine ⟨p.concat (h n (Nat.lt_succ_self n)), ?_⟩
    intro j hj
    rw [SimpleGraph.Walk.support_concat]
    rcases Nat.lt_or_eq_of_le hj with hjn | hjn
    · exact List.mem_append.mpr (Or.inl (hp j (Nat.le_of_lt_succ hjn)))
    · subst hjn
      simp

/-- A nearest-neighbour lattice walk of a lattice rectangle whose grid points
carry the field at least `l` cannot coexist with a star bottom-top walk of the
same rectangle whose grid points carry the field at most `l'`, when `l' < l`. -/
theorem no_lattice_walk_of_levels {X : Sandpile.Continuum.Space 2 → ℝ}
    {t l l' : ℝ} (hlt : l' < l) {w h : ℕ}
    {a b : Sandpile.planeRectangle w h}
    (p : (Sandpile.rectangleGraph (Sandpile.planeRectangle w h)).Walk a b)
    (ha : a ∈ Sandpile.rectangleLeft (Sandpile.planeRectangle w h))
    (hb : b ∈ Sandpile.rectangleRight (Sandpile.planeRectangle w h))
    (hp : ∀ z ∈ p.support, l ≤ X (gridPt t (z : Site 2)))
    {c d : {x : Site 2 // x ∈ ((Sandpile.planeRectangle w h : Finset (Site 2)) : Set (Site 2))}}
    (q : ((Sandpile.starLatticeGraph 2).induce
      ((Sandpile.planeRectangle w h : Finset (Site 2)) : Set (Site 2))).Walk c d)
    (hc : (c : Site 2) 1 = 0) (hd : (d : Site 2) 1 = (h : ℤ))
    (hq : ∀ z ∈ q.support, X (gridPt t (z : Site 2)) ≤ l') :
    False := by
  obtain ⟨z, u, hu, hzu, hzq⟩ := Sandpile.rectangle_nn_star_intersect p q ha hb hc hd
  have h1 : l ≤ X (gridPt t (z : Site 2)) := by
    rw [hzu]; exact hp u hu
  have h2 : X (gridPt t (z : Site 2)) ≤ l' := hq z hzq
  linarith


/-- Two lattice sites `z` and `w` that agree off a coordinate `i` and differ by exactly `1`
in coordinate `i` are adjacent in `lattice 2`. -/
theorem adj_of_coord {z w : Site 2} (i : Fin 2) (hother : ∀ j ≠ i, z j = w j)
    (h : (z i - w i).natAbs = 1) :
    (lattice 2).Adj z w := by
  have h1 : z i - w i = 1 ∨ z i - w i = -1 := by omega
  rcases h1 with h1 | h1
  · refine ⟨i, Or.inr ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
      omega
    · rw [hother j hj]
      simp [LatticeProb.unit, hj]
  · refine ⟨i, Or.inl ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
      omega
    · rw [← hother j hj]
      simp [LatticeProb.unit, hj]

/-- Two sites at Chebyshev distance at most `1` in each coordinate are joined by a walk in
`lattice 2` of at most two steps that visits both endpoints, going through the common corner
`m` when `z` and `w` differ in both coordinates. -/
theorem exists_lattice_walk_pair {z w : Site 2}
    (h : ∀ i : Fin 2, (z i - w i).natAbs ≤ 1) :
    ∃ p : (lattice 2).Walk z w, z ∈ p.support ∧ w ∈ p.support := by
  by_cases hzw : z = w
  · subst hzw
    exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.start_mem_support _,
        SimpleGraph.Walk.end_mem_support _⟩
  · have h0 := h 0
    have h1 := h 1
    by_cases hz0 : z 0 = w 0
    · have hw1 : (z 1 - w 1).natAbs = 1 := by
        rcases Nat.eq_zero_or_pos (z 1 - w 1).natAbs with hh | hh
        · exfalso; apply hzw; ext j; fin_cases j
          · exact hz0
          · exact sub_eq_zero.mp (by simpa using hh)
        · omega
      exact ⟨SimpleGraph.Walk.cons
          (adj_of_coord 1 (fun j hj => by fin_cases j <;> simp_all) hw1) SimpleGraph.Walk.nil,
        SimpleGraph.Walk.start_mem_support _, SimpleGraph.Walk.end_mem_support _⟩
    · have hz0' : (z 0 - w 0).natAbs = 1 := by
        rcases Nat.eq_zero_or_pos (z 0 - w 0).natAbs with hh | hh
        · exfalso; apply hz0; omega
        · omega
      by_cases hz1 : z 1 = w 1
      · exact ⟨SimpleGraph.Walk.cons
            (adj_of_coord 0 (fun j hj => by fin_cases j <;> simp_all) hz0') SimpleGraph.Walk.nil,
          SimpleGraph.Walk.start_mem_support _, SimpleGraph.Walk.end_mem_support _⟩
      · have hw1' : (z 1 - w 1).natAbs = 1 := by
          rcases Nat.eq_zero_or_pos (z 1 - w 1).natAbs with hh | hh
          · exfalso; apply hz1; omega
          · omega
        let m : Site 2 := Function.update z 0 (w 0)
        have hzm : (lattice 2).Adj z m := by
          refine adj_of_coord 0 ?_ ?_
          · intro j hj
            simp only [m, Function.update_of_ne hj]
          · simp only [m, Function.update_self]
            exact hz0'
        have hmw : (lattice 2).Adj m w := by
          refine adj_of_coord 1 ?_ ?_
          · intro j hj
            have hj0 : j = 0 := by fin_cases j <;> simp_all
            subst hj0
            simp [m]
          · have hm1 : m 1 = z 1 := by simp [m]
            rw [hm1]
            exact hw1'
        exact ⟨SimpleGraph.Walk.cons hzm (SimpleGraph.Walk.cons hmw SimpleGraph.Walk.nil),
          SimpleGraph.Walk.start_mem_support _, SimpleGraph.Walk.end_mem_support _⟩


/-- A sequence of sites that are pairwise within Chebyshev distance `1` of their successor is
carried by a `lattice 2` walk from `v 0` to `v n` that visits every `v j`, obtained by
concatenating the two-step walks of `exists_lattice_walk_pair` along the sequence. -/
theorem exists_lattice_walk_seq {v : ℕ → Site 2} {n : ℕ}
    (h : ∀ j < n, ∀ i : Fin 2, (v j i - v (j + 1) i).natAbs ≤ 1) :
    ∃ p : (lattice 2).Walk (v 0) (v n), ∀ j ≤ n, v j ∈ p.support := by
  induction n with
  | zero => exact ⟨SimpleGraph.Walk.nil, fun j hj => by
      have : j = 0 := by omega
      subst this
      exact SimpleGraph.Walk.start_mem_support _⟩
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih (fun j hj i => h j (Nat.lt_succ_of_lt hj) i)
      have hlast : ∀ i : Fin 2, (v n i - v (n + 1) i).natAbs ≤ 1 := h n (Nat.lt_succ_self n)
      obtain ⟨q, _, hq2⟩ := exists_lattice_walk_pair hlast
      refine ⟨p.append q, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
      · exact (SimpleGraph.Walk.mem_support_append_iff p q).mpr (Or.inl (hp j (by omega)))
      · have hje : j = n + 1 := by omega
        subst hje
        exact (SimpleGraph.Walk.mem_support_append_iff p q).mpr (Or.inr hq2)



/-- The blocking of Step 1 (`sandpile.tex:2233-2235`) in the form the arm bound
consumes: a nearest-neighbour left-right walk of a lattice rectangle at level
`l'` and a star bottom-top walk of the same rectangle at level `l > l'` cannot
coexist.  This is `Sandpile.Support.no_lattice_walk_of_levels` with the two
walks of the annulus in its place. -/
theorem blocking_of_star_walk {X : Sandpile.Continuum.Space 2 → ℝ}
    {t l l' : ℝ} (hlt : l' < l) {w h : ℕ}
    {a b : Sandpile.planeRectangle w h}
    (p : (Sandpile.rectangleGraph (Sandpile.planeRectangle w h)).Walk a b)
    (ha : a ∈ Sandpile.rectangleLeft (Sandpile.planeRectangle w h))
    (hb : b ∈ Sandpile.rectangleRight (Sandpile.planeRectangle w h))
    (hp : ∀ z ∈ p.support, l ≤ X (gridPt t (z : Site 2)))
    {c d : {x : Site 2 // x ∈ ((Sandpile.planeRectangle w h : Finset (Site 2)) : Set (Site 2))}}
    (q : ((Sandpile.starLatticeGraph 2).induce
      ((Sandpile.planeRectangle w h : Finset (Site 2)) : Set (Site 2))).Walk c d)
    (hc : (c : Site 2) 1 = 0) (hd : (d : Site 2) 1 = (h : ℤ))
    (hq : ∀ z ∈ q.support, X (gridPt t (z : Site 2)) ≤ l') :
    False :=
  Sandpile.Support.no_lattice_walk_of_levels hlt p ha hb hp q hc hd hq

end Sandpile.Support
