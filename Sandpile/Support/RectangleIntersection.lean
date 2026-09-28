import Sandpile.Support.WalkRay

/-!
# Nearest-neighbor and star crossing intersection

Intersection of opposite nearest-neighbor and star crossings, and exact rectangle duality.
`rectangle_nn_star_intersect` shows that a horizontal nearest-neighbor left-right crossing and
a vertical star bottom-top crossing of the same rectangle must share a site, using the
`walkRay` winding invariant along the induced infinite lattice walk that skirts the
nearest-neighbor crossing. This is packaged into the equivalence
`crossingValue_le_iff_low_star_walk` between a bound on the horizontal `crossingValue` and the
existence of a low vertical star walk.
-/

noncomputable section
namespace Sandpile

/-- If `f` is constant across every edge of the walk `p`, then `f` agrees at the two
endpoints `a` and `b`, proved by induction on `p`. -/
lemma walk_value_eq_of_adj {V T : Type*} {G : SimpleGraph V} (f : V → T)
    {a b : V} (p : G.Walk a b)
    (hf : ∀ x ∈ p.support, ∀ y ∈ p.support, G.Adj x y → f x = f y) : f a = f b := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
    exact (hf a (by simp) b (by simp) hab).trans
      (ih (fun x hx y hy hxy => hf x (by simp [hx]) y (by simp [hy]) hxy))

/-- A horizontal nearest-neighbor left-right walk `p` and a vertical star bottom-top walk `q`
of the same rectangle must share a site: some `z` on `q` coincides with some `t` on `p`. Proved
by extending `p` to an infinite lattice walk `P` past both sides of the rectangle and deriving
a contradiction from `walkRay_star_step`, `walkRay_below`, and `walkRay_above` if `q` never
meets `p`. -/
lemma rectangle_nn_star_intersect {w h : ℕ} {a b : planeRectangle w h}
    {c d : {x : Site 2 // x ∈ ((planeRectangle w h) : Set (Site 2))}}
    (p : (rectangleGraph (planeRectangle w h)).Walk a b)
    (q : ((starLatticeGraph 2).induce ((planeRectangle w h) : Set (Site 2))).Walk c d)
    (ha : a ∈ rectangleLeft (planeRectangle w h))
    (hb : b ∈ rectangleRight (planeRectangle w h))
    (hc : (c : Site 2) 1 = 0) (hd : (d : Site 2) 1 = h) :
    ∃ z : {x : Site 2 // x ∈ ((planeRectangle w h) : Set (Site 2))},
      ∃ t : planeRectangle w h, t ∈ p.support ∧ (z : Site 2) = (t : Site 2) ∧
        z ∈ q.support := by
  classical
  by_contra hno
  push Not at hno
  have ha0 := (mem_rectangleLeft_planeRectangle a).mp ha
  have hb0 := (mem_rectangleRight_planeRectangle b).mp hb
  let f : rectangleGraph (planeRectangle w h) →g lattice 2 := ⟨Subtype.val, fun h => h⟩
  let p₀ := p.map f
  let l : Site 2 := (a : Site 2) - unit (0 : Fin 2)
  let r : Site 2 := (b : Site 2) + unit (0 : Fin 2)
  have hl : (lattice 2).Adj l (a : Site 2) := ⟨0, Or.inl (by dsimp [l]; abel)⟩
  have hr : (lattice 2).Adj (b : Site 2) r := ⟨0, Or.inl rfl⟩
  let P : (lattice 2).Walk l r := .cons hl (p₀.append hr.toWalk)
  have hsupp (z : Site 2) (hz : z ∈ P.support) :
      z = l ∨ z = r ∨ ∃ t ∈ p.support, (t : Site 2) = z := by
    change z ∈ l :: (p₀.append hr.toWalk).support at hz
    rcases List.mem_cons.mp hz with hz | hz
    · exact Or.inl hz
    · rcases (SimpleGraph.Walk.mem_support_append_iff p₀ hr.toWalk).mp hz with hz | hz
      · rw [show p₀.support = p.support.map (fun t : planeRectangle w h => (t : Site 2))
          from SimpleGraph.Walk.support_map _ _] at hz
        exact Or.inr (Or.inr (List.mem_map.mp hz))
      · change z ∈ [(b : Site 2), r] at hz
        rcases List.mem_cons.mp hz with hz | hz
        · exact Or.inr (Or.inr ⟨b, p.end_mem_support, hz.symm⟩)
        · exact Or.inr (Or.inl (List.mem_singleton.mp hz))
  have hleft : l 0 = -1 := by simp [l, unit, ha0]
  have hright : r 0 = (w : ℤ) + 1 := by simp [r, unit, hb0]
  have hbounds (z : planeRectangle w h) :
      0 ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ w ∧
        0 ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ h := (mem_planeRectangle w h z).mp z.property
  have havoid (z : {x : Site 2 // x ∈ ((planeRectangle w h) : Set (Site 2))})
      (hz : z ∈ q.support) : (z : Site 2) ∉ P.support := by
    intro hzp
    rcases hsupp z hzp with hz' | hz' | ⟨t, ht, htz⟩
    · have hh := congrFun hz' 0
      rw [hleft] at hh
      have hzb := hbounds ⟨(z : Site 2), z.property⟩
      have : 0 ≤ (z : Site 2) 0 := hzb.1
      omega
    · have hh := congrFun hz' 0
      rw [hright] at hh
      have hzb := hbounds ⟨(z : Site 2), z.property⟩
      have : (z : Site 2) 0 ≤ w := hzb.2.1
      omega
    · exact hno z t ht htz.symm hz
  have hend (z : planeRectangle w h) : l 0 ≠ (z : Site 2) 0 ∧ r 0 ≠ (z : Site 2) 0 := by
    rw [hleft, hright]
    have hh := hbounds z
    omega
  have hrow (z : Site 2) (hz : z ∈ P.support) : 0 ≤ z 1 ∧ z 1 ≤ h := by
    rcases hsupp z hz with rfl | rfl | ⟨t, _, rfl⟩
    · simpa [l, unit] using (hbounds a).2.2
    · simpa [r, unit] using (hbounds b).2.2
    · exact (hbounds t).2.2
  have hsame : walkRay P (c : Site 2) = walkRay P (d : Site 2) := by
    apply walk_value_eq_of_adj (fun z : planeRectangle w h => walkRay P (z : Site 2)) q
    intro z hz t ht hzt
    exact walkRay_star_step P (havoid z hz) (havoid t ht)
      (hend z).1 (hend z).2 (hend t).1 (hend t).2 hzt
  have hbottom : walkRay P (c : Site 2) = 0 := walkRay_below P
    (havoid c q.start_mem_support) (fun z hz => by rw [hc]; exact (hrow z hz).1)
  have htop : walkRay P (d : Site 2) = 1 := walkRay_above P
    (fun z hz => by rw [hd]; exact (hrow z hz).2)
    (by rw [hleft]; have := (hbounds d).1; omega)
    (by rw [hright]; have := (hbounds d).2.1; omega)
  rw [hbottom, htop] at hsame
  exact zero_ne_one hsame

/-- If a vertical star walk `q` from the bottom edge to the top edge stays at most `level`,
then `crossingValue (planeRectangle w h) F ≤ level`: any optimal horizontal crossing witness
`p` must, by `rectangle_nn_star_intersect`, meet `q` at a shared site where `F` is at most
`level`. -/
lemma crossingValue_le_of_low_star_walk {w h : ℕ} (F : planeRectangle w h → ℝ)
    {a b : planeRectangle w h}
    (q : ((starLatticeGraph 2).induce ((planeRectangle w h) : Set (Site 2))).Walk a b)
    (ha : (a : Site 2) 1 = 0) (hb : (b : Site 2) 1 = h) {level : ℝ}
    (hq : ∀ z ∈ q.support, F z ≤ level) : crossingValue (planeRectangle w h) F ≤ level := by
  obtain ⟨c, d, p, _, hc, hd, he⟩ := (crossingValue_spec
    (isLatticeRectangle_planeRectangle w h) (planeRectangle_nonempty w h) F).2
  obtain ⟨z, t, htp, htz, hzq⟩ := rectangle_nn_star_intersect p q hc hd ha hb
  rw [← he]
  exact (walkBottleneck_le p F htp).trans (by
    have hF : F ⟨(z : Site 2), z.property⟩ ≤ level := hq ⟨(z : Site 2), z.property⟩ hzq
    have hzt : (⟨(z : Site 2), z.property⟩ : planeRectangle w h) = t := Subtype.ext htz
    rw [hzt] at hF
    exact hF)

/-- `crossingValue (planeRectangle w h) F ≤ level` is equivalent to the existence of a vertical
star walk from the bottom edge to the top edge along which `F ≤ level`, combining
`rectangle_low_star_walk` for the forward direction with `crossingValue_le_of_low_star_walk`
for the reverse. -/
lemma crossingValue_le_iff_low_star_walk (w h : ℕ) (F : planeRectangle w h → ℝ) (level : ℝ) :
    crossingValue (planeRectangle w h) F ≤ level ↔
      ∃ (a b : planeRectangle w h)
        (p : ((starLatticeGraph 2).induce ((planeRectangle w h) : Set (Site 2))).Walk a b),
        (a : Site 2) 1 = 0 ∧ (b : Site 2) 1 = h ∧ ∀ z ∈ p.support, F z ≤ level := by
  constructor
  · intro hle
    obtain ⟨a, b, p, ha, hb, hp⟩ := rectangle_low_star_walk w h F
    exact ⟨a, b, p, ha, hb, fun z hz => (hp z hz).trans hle⟩
  · rintro ⟨a, b, p, ha, hb, hp⟩
    exact crossingValue_le_of_low_star_walk F p ha hb hp

end Sandpile
