import Sandpile.Support.BallRectangleDuality
import Sandpile.Support.RectangleDuality

/-!
# The converse planar duality for the dimension-four percolation argument

This file proves the converse direction of the planar duality used by the dimension-four
percolation argument: a crossing value at most a level produces a `∗`-connected top-bottom
crossing of the low set, in the translated coordinate rectangle of `sandpile.tex:3436-3440`.
The translation `planeTranslate x` embeds the coordinate-plane rectangle into the ambient
four-dimensional lattice as a graph homomorphism into the star-adjacency graph, and the
top-bottom crossing produced by `rectangle_low_star_walk` is pushed forward along it.
-/

noncomputable section
namespace Sandpile

/-- `planeTranslate x z` agrees with `x` on coordinate `0` after adding `z 0`. -/
lemma planeTranslate_apply_zero (x : Site 4) (z : Site 2) :
    planeTranslate x z 0 = x 0 + z 0 := rfl

/-- `planeTranslate x z` agrees with `x` on coordinate `1` after adding `z 1`. -/
lemma planeTranslate_apply_one (x : Site 4) (z : Site 2) :
    planeTranslate x z 1 = x 1 + z 1 := rfl

/-- `planeTranslate x z` leaves coordinate `2` of `x` unchanged. -/
lemma planeTranslate_apply_two (x : Site 4) (z : Site 2) :
    planeTranslate x z 2 = x 2 := rfl

/-- `planeTranslate x z` leaves coordinate `3` of `x` unchanged. -/
lemma planeTranslate_apply_three (x : Site 4) (z : Site 2) :
    planeTranslate x z 3 = x 3 := rfl

/-- `planeTranslate x` sends `starLatticeGraph 2`-adjacent sites of the coordinate plane to
`starGraph`-adjacent sites of the ambient lattice: it changes only the first two coordinates,
each by at most `1`, and never both to the point of equality. -/
lemma starGraph_adj_planeTranslate {z w : Site 2}
    (h : (starLatticeGraph 2).Adj z w) (x : Site 4) :
    starGraph.Adj (planeTranslate x z) (planeTranslate x w) := by
  obtain ⟨hne, hd⟩ := h
  have h0 : (z 0 - w 0).natAbs ≤ 1 := hd 0
  have h1 : (z 1 - w 1).natAbs ≤ 1 := hd 1
  refine ⟨?_, ?_, ?_⟩
  · intro he
    apply hne
    have e0 : z 0 = w 0 := by
      have hh : planeTranslate x z 0 = planeTranslate x w 0 := congrFun he 0
      rw [planeTranslate_apply_zero, planeTranslate_apply_zero] at hh
      omega
    have e1 : z 1 = w 1 := by
      have hh : planeTranslate x z 1 = planeTranslate x w 1 := congrFun he 1
      rw [planeTranslate_apply_one, planeTranslate_apply_one] at hh
      omega
    funext i
    fin_cases i
    · exact e0
    · exact e1
  · intro i
    fin_cases i
    · show |planeTranslate x z 0 - planeTranslate x w 0| ≤ 1
      rw [planeTranslate_apply_zero, planeTranslate_apply_zero,
        show x 0 + z 0 - (x 0 + w 0) = z 0 - w 0 by ring, abs_le]
      omega
    · show |planeTranslate x z 1 - planeTranslate x w 1| ≤ 1
      rw [planeTranslate_apply_one, planeTranslate_apply_one,
        show x 1 + z 1 - (x 1 + w 1) = z 1 - w 1 by ring, abs_le]
      omega
    · show |planeTranslate x z 2 - planeTranslate x w 2| ≤ 1
      rw [planeTranslate_apply_two, planeTranslate_apply_two]
      simp
    · show |planeTranslate x z 3 - planeTranslate x w 3| ≤ 1
      rw [planeTranslate_apply_three, planeTranslate_apply_three]
      simp
  · intro i hi
    fin_cases i
    · exact absurd hi (by norm_num)
    · exact absurd hi (by norm_num)
    · show planeTranslate x z 2 = planeTranslate x w 2
      rw [planeTranslate_apply_two, planeTranslate_apply_two]
    · show planeTranslate x z 3 = planeTranslate x w 3
      rw [planeTranslate_apply_three, planeTranslate_apply_three]


/-- The star hom from the plane rectangle into the ambient lattice. -/
def planeRectStarHom (ϑ : ℝ) (r : ℕ) (x : Site 4) :
    ((starLatticeGraph 2).induce ((planeRectangle ⌊ϑ * r⌋₊ r : Finset (Site 2)) : Set (Site 2)))
      →g starGraph where
  toFun := fun u => planeTranslate x (u : Site 2)
  map_rel' := fun h => starGraph_adj_planeTranslate h x

/-- Converse of `crossingValue_le_of_hasStarTopBottomCrossing`: a crossing
value at most `level` produces a `∗`-connected top-bottom crossing of the
low set. -/
lemma hasStarTopBottomCrossing_of_crossingValue_le {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (r : ℕ) (x : Site 4) (F : Site 4 → ℝ) (level : ℝ)
    (h : crossingValue (planeRectangle ⌊ϑ * r⌋₊ r)
        (fun z => F (planeTranslate x z)) ≤ level) :
    HasStarTopBottomCrossing ϑ r x {z | F z ≤ level} := by
  classical
  obtain ⟨a, b, p, ha, hb, hp⟩ :=
    rectangle_low_star_walk ⌊ϑ * r⌋₊ r (fun z => F (planeTranslate x z))
  set g := planeRectStarHom ϑ r x with hg
  set q : starGraph.Walk (planeTranslate x (b : Site 2)) (planeTranslate x (a : Site 2)) :=
    ((p.reverse).map g).copy rfl rfl with hq
  have hsupp : q.support = (p.reverse.support).map (⇑g) := by
    rw [hq, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
  refine ⟨q.support, q.support_ne_nil, ?_, q.isChain_adj_support, ?_, ?_⟩
  · intro z hz
    rw [hsupp] at hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
    have hu' : u ∈ p.support := by
      rw [SimpleGraph.Walk.support_reverse] at hu
      exact List.mem_reverse.mp hu
    refine ⟨le_trans (hp u hu') h, ?_⟩
    rw [ballRect_eq_image_planeRectangle hϑ r x]
    exact ⟨(u : Site 2), u.2, rfl⟩
  · intro z hz
    rw [List.head?_eq_some_head q.support_ne_nil] at hz
    have hz' : z = planeTranslate x (b : Site 2) := by
      have hh := Option.some_inj.mp hz.symm
      rw [hh]
      exact SimpleGraph.Walk.head_support q
    rw [hz', planeTranslate_apply_one, hb]
  · intro z hz
    rw [List.getLast?_eq_getLast_of_ne_nil q.support_ne_nil] at hz
    have hz' : z = planeTranslate x (a : Site 2) := by
      have hh := Option.some_inj.mp hz.symm
      rw [hh]
      exact SimpleGraph.Walk.getLast_support q
    rw [hz', planeTranslate_apply_one, ha]
    ring

/-- **The contrapositive of `hasStarTopBottomCrossing_of_crossingValue_le`.** If there is no
`∗`-connected top-bottom crossing of the low set, then the crossing value of the translated
rectangle strictly exceeds the level. -/
lemma lt_crossingValue_of_not_star {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (r : ℕ) (x : Site 4) (F : Site 4 → ℝ) (level : ℝ)
    (h : ¬ HasStarTopBottomCrossing ϑ r x {z | F z ≤ level}) :
    level < crossingValue (planeRectangle ⌊ϑ * r⌋₊ r)
      (fun z => F (planeTranslate x z)) :=
  lt_of_not_ge fun hle => h (hasStarTopBottomCrossing_of_crossingValue_le hϑ r x F level hle)

end Sandpile
