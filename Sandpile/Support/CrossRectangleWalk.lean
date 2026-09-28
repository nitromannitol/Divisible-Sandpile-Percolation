import Sandpile.Support.CrossFixBlocking

/-!
# Rectangle-confined walk approximations of connected sets

Approximation of connected planar sets by walks that remain in their rectangle: a compact
connected set inside a mesh-aligned square yields a nearest-neighbour walk of the rounded
lattice sites that stays inside the square and within `3t` of the set at every vertex
(`exists_rectangle_walk_connected`), and this is used to show that two compact connected
crossings of a rectangle in opposite directions must intersect
(`rectangle_crossings_intersect`, `not_crosses_opposite_levels`).
-/

open Set
namespace Sandpile.Support
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A diagonal grid step can be filled using one coordinate corner. -/
theorem exists_lattice_walk_pair_corner {z w : Site 2}
    (h : ∀ i : Fin 2, (z i - w i).natAbs ≤ 1) :
    ∃ p : (lattice 2).Walk z w,
      ∀ v ∈ p.support, v = z ∨ v = w ∨ v = Function.update z 0 (w 0) := by
  let m := Function.update z 0 (w 0)
  have step {a b : Site 2} (i : Fin 2) (he : ∀ j ≠ i, a j = b j)
      (hi : (a i - b i).natAbs ≤ 1) :
      ∃ p : (lattice 2).Walk a b, ∀ v ∈ p.support, v = a ∨ v = b := by
    by_cases hab : a = b
    · subst b
      exact ⟨.nil, by simp⟩
    · have hi' : (a i - b i).natAbs = 1 := by
        have : a i ≠ b i := fun h => hab (funext fun j => by
          by_cases hj : j = i
          · simpa [hj] using h
          · exact he j hj)
        omega
      exact ⟨(adj_of_coord i he hi').toWalk, by simp⟩
  obtain ⟨p, hp⟩ := step (a := z) (b := m) 0
    (fun j hj => by simp [m, hj]) (by simpa [m] using h 0)
  obtain ⟨q, hq⟩ := step (a := m) (b := w) 1
    (fun j hj => by fin_cases j <;> simp_all [m]) (by simpa [m] using h 1)
  refine ⟨p.append q, fun v hv => ?_⟩
  rcases (SimpleGraph.Walk.mem_support_append_iff p q).mp hv with hv | hv
  · rcases hp v hv with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  · rcases hq v hv with rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

/-- Two nearby sites in a lattice rectangle can be joined inside it, with all
vertices within three mesh lengths of the same planar set. -/
theorem exists_rectangle_walk_pair {w h : ℕ} {z v : planeRectangle w h}
    {Γ : Set (Space 2)} {t : ℝ} (ht : 0 ≤ t)
    (hz : ∃ u ∈ Γ, dist (gridPt t z) u ≤ t)
    (hv : ∃ u ∈ Γ, dist (gridPt t v) u ≤ t)
    (hstep : ∀ i : Fin 2, ((z : Site 2) i - (v : Site 2) i).natAbs ≤ 1) :
    ∃ p : (rectangleGraph (planeRectangle w h)).Walk z v,
      ∀ a ∈ p.support, ∃ u ∈ Γ, dist (gridPt t a) u ≤ 3 * t := by
  obtain ⟨p, hp⟩ := exists_lattice_walk_pair_corner hstep
  have hm : Function.update (z : Site 2) 0 ((v : Site 2) 0) ∈ planeRectangle w h := by
    have hz' := (mem_planeRectangle w h z).mp z.property
    have hv' := (mem_planeRectangle w h v).mp v.property
    apply (mem_planeRectangle w h _).mpr
    simpa using And.intro hv'.1 (And.intro hv'.2.1 hz'.2.2)
  have hrect : ∀ a ∈ p.support, a ∈ planeRectangle w h := by
    intro a ha
    rcases hp a ha with rfl | rfl | rfl
    exacts [z.property, v.property, hm]
  have hnear : ∀ a ∈ p.support, ∃ u ∈ Γ, dist (gridPt t a) u ≤ 3 * t := by
    intro a ha
    rcases hp a ha with rfl | rfl | rfl
    · obtain ⟨u, hu, hd⟩ := hz
      exact ⟨u, hu, by linarith⟩
    · obtain ⟨u, hu, hd⟩ := hv
      exact ⟨u, hu, by linarith⟩
    · obtain ⟨u, hu, hd⟩ := hz
      refine ⟨u, hu, ?_⟩
      have := dist_gridPt_update_le ht (hstep 0)
      have := dist_triangle (gridPt t (Function.update (z : Site 2) 0 ((v : Site 2) 0)))
        (gridPt t z) u
      linarith
  refine ⟨p.induce _ hrect, fun a ha => hnear a ?_⟩
  change a ∈ (p.induce (↑(planeRectangle w h)) hrect).support at ha
  rw [SimpleGraph.Walk.support_induce p hrect] at ha
  exact (List.mem_attachWith hrect a).mp ha

/-- Rounding preserves a square whose sides lie on the mesh. -/
theorem roundSite_mem_square {t s : ℝ} {n : ℕ} (ht : 0 < t)
    (hts : t * (n : ℝ) = s) {u : Space 2} (hu : u ∈ rectSet ![0, 0] ![s, s]) :
    roundSite t u ∈ planeRectangle n n := by
  have hcoord (i : Fin 2) : 0 ≤ roundSite t u i ∧ roundSite t u i ≤ (n : ℤ) := by
    have hui : 0 ≤ u i ∧ u i ≤ s := by
      fin_cases i
      · simpa using hu 0
      · simpa using hu 1
    have he := abs_le.mp (abs_sub_roundSite_le ht u i)
    constructor
    · have hh : (-1 : ℝ) < (roundSite t u i : ℝ) := by nlinarith
      have : (-1 : ℤ) < roundSite t u i := by exact_mod_cast hh
      omega
    · have hh : (roundSite t u i : ℝ) < (n : ℝ) + 1 := by nlinarith
      have : roundSite t u i < (n : ℤ) + 1 := by exact_mod_cast hh
      omega
  exact (mem_planeRectangle n n _).mpr ⟨(hcoord 0).1, (hcoord 0).2, hcoord 1⟩

/-- Rounding a point on a mesh-aligned face keeps that face. -/
theorem roundSite_face {t s : ℝ} {n : ℕ} (ht : 0 < t) (hts : t * (n : ℝ) = s)
    {u : Space 2} {i : Fin 2} (hu : u i = s) : roundSite t u i = (n : ℤ) := by
  simp [roundSite, hu, ← hts, mul_div_cancel_left₀ _ ht.ne']

/-- A chain of nearby rounded sites yields a walk inside the square. -/
theorem exists_rectangle_walk_chain {n m : ℕ} (v : ℕ → planeRectangle n n)
    {Γ : Set (Space 2)} {t : ℝ} (ht : 0 ≤ t)
    (hΓ : ∀ j ≤ m, ∃ u ∈ Γ, dist (gridPt t (v j)) u ≤ t)
    (hstep : ∀ j < m, ∀ i : Fin 2,
      ((v j : Site 2) i - (v (j + 1) : Site 2) i).natAbs ≤ 1) :
    ∃ p : (rectangleGraph (planeRectangle n n)).Walk (v 0) (v m),
      ∀ a ∈ p.support, ∃ u ∈ Γ, dist (gridPt t a) u ≤ 3 * t := by
  induction m with
  | zero =>
    refine ⟨.nil, ?_⟩
    intro a ha
    have ha' : a = v 0 := by simpa using ha
    subst a
    obtain ⟨u, hu, hd⟩ := hΓ 0 le_rfl
    exact ⟨u, hu, by linarith⟩
  | succ m ih =>
    obtain ⟨p, hp⟩ := ih (fun j hj => hΓ j (by omega)) (fun j hj => hstep j (by omega))
    obtain ⟨q, hq⟩ := exists_rectangle_walk_pair ht (hΓ m (by omega))
      (hΓ (m + 1) (by omega)) (hstep m (by omega))
    refine ⟨p.append q, fun a ha => ?_⟩
    rcases (SimpleGraph.Walk.mem_support_append_iff p q).mp ha with ha | ha
    exacts [hp a ha, hq a ha]

/-- A connected set in a mesh-aligned square is approximated on any positive
mesh, with both endpoints and every intermediate vertex inside the square. -/
theorem exists_rectangle_walk_connected {Γ : Set (Space 2)} (hc : IsConnected Γ)
    {s t : ℝ} {n : ℕ} (ht : 0 < t) (hts : t * (n : ℝ) = s)
    (hΓ : Γ ⊆ rectSet ![0, 0] ![s, s]) {x y : Space 2} (hx : x ∈ Γ) (hy : y ∈ Γ) :
    ∃ (a b : planeRectangle n n) (p : (rectangleGraph (planeRectangle n n)).Walk a b),
      (a : Site 2) = roundSite t x ∧ (b : Site 2) = roundSite t y ∧
      ∀ z ∈ p.support, ∃ u ∈ Γ, dist (gridPt t z) u ≤ 3 * t := by
  have ht2 : 0 < t / 2 := by positivity
  obtain ⟨m, v, hv0, hvm, hvΓ, hvstep⟩ := exists_vertices_of_reflTransGen ht2 hx
    (reflTransGen_of_isPreconnected hc.isPreconnected ht2 hx y hy)
  let v' (j : ℕ) : planeRectangle n n :=
    ⟨roundSite t (v (min j (m + 1))),
      roundSite_mem_square ht hts (hΓ (hvΓ _ (min_le_right _ _)))⟩
  have he (j : ℕ) (hj : j ≤ m + 1) : (v' j : Site 2) = roundSite t (v j) := by
    simp [v', min_eq_left hj]
  obtain ⟨p, hp⟩ := exists_rectangle_walk_chain (m := m + 1) v' ht.le
    (fun j hj => by rw [he j hj]; exact ⟨v j, hvΓ j hj, dist_gridPt_roundSite_le ht _⟩)
    (fun j hj i => by
      rw [he j (by omega), he (j + 1) (by omega)]
      exact natAbs_roundSite_le_one ht (by linarith) (hvstep j (by omega)).le i)
  refine ⟨v' 0, v' (m + 1), p, ?_, ?_, hp⟩
  · rw [he 0 (by omega), hv0]
  · rw [he (m + 1) le_rfl, hvm]

/-- Compact connected crossings in opposite directions of a square meet. -/
theorem square_crossings_intersect {s : ℝ} (hs : 0 < s) {A B : Set (Space 2)}
    (hA : Crosses ![0, 0] ![s, s] 0 A)
    (hB : Crosses ![0, 0] ![s, s] 1 B) : (A ∩ B).Nonempty := by
  obtain ⟨Γ, hΓ, hΓc, hΓn, ⟨x, hx, hx0⟩, ⟨y, hy, hy0⟩⟩ := hA
  obtain ⟨Δ, hΔ, hΔc, hΔn, ⟨u, hu, hu1⟩, ⟨v, hv, hv1⟩⟩ := hB
  by_contra hno
  have hd : Disjoint Γ Δ := Set.disjoint_left.mpr fun z hz hz' =>
    hno ⟨z, (hΓ hz).1, (hΔ hz').1⟩
  obtain ⟨ε, hε, hsep⟩ := hd.exists_thickenings hΓc hΔc.isClosed
  obtain ⟨n, hn, hns, hmesh⟩ := exists_mesh hs (show 0 < ε / 2 by positivity)
  have ht : 0 < s / (n : ℝ) := div_pos hs hn
  obtain ⟨a, b, p, ha, hb, hp⟩ := exists_rectangle_walk_connected hΓn ht hns
    (fun z hz => (hΓ hz).2) hx hy
  obtain ⟨c, d, q, hc, hd, hq⟩ := exists_rectangle_walk_connected hΔn ht hns
    (fun z hz => (hΔ hz).2) hu hv
  let f : rectangleGraph (planeRectangle n n) →g
      (starLatticeGraph 2).induce (↑(planeRectangle n n)) :=
    ⟨id, fun he => lattice_le_starLatticeGraph 2 he⟩
  have ha0 : a ∈ rectangleLeft (planeRectangle n n) := by
    apply (mem_rectangleLeft_planeRectangle _).mpr
    rw [ha]
    simp [roundSite, show x 0 = 0 from hx0]
  have hb0 : b ∈ rectangleRight (planeRectangle n n) := by
    apply (mem_rectangleRight_planeRectangle _).mpr
    rw [hb]
    exact roundSite_face ht hns hy0
  have hc1 : (c : Site 2) 1 = 0 := by
    rw [hc]
    simp [roundSite, show u 1 = 0 from hu1]
  have hd1 : (d : Site 2) 1 = n := by
    rw [hd]
    exact roundSite_face ht hns hv1
  obtain ⟨z, z', hz', hzz', hz⟩ := rectangle_nn_star_intersect p (q.map f) ha0 hb0 hc1 hd1
  have hzq : z ∈ q.support := by
    have he : (q.map f).support = q.support := by
      rw [SimpleGraph.Walk.support_map]
      exact List.map_id _
    rwa [he] at hz
  obtain ⟨g, hg, hzg⟩ := hp z' hz'
  obtain ⟨e, he, hze⟩ := hq z hzq
  have hzΓ : gridPt (s / n) z ∈ Metric.thickening ε Γ := by
    apply Metric.mem_thickening_iff.mpr
    refine ⟨g, hg, ?_⟩
    rw [hzz']
    linarith
  have hzΔ : gridPt (s / n) z ∈ Metric.thickening ε Δ :=
    Metric.mem_thickening_iff.mpr ⟨e, he, by linarith⟩
  exact Set.disjoint_left.mp hsep hzΓ hzΔ

/-- Compact connected crossings in opposite directions of a nondegenerate
rectangle meet. -/
theorem rectangle_crossings_intersect {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i)
    {A B : Set (Space 2)} (hA : Crosses a b 0 A) (hB : Crosses a b 1 B) :
    (A ∩ B).Nonempty := by
  let f (u : Space 2) : Space 2 := WithLp.toLp 2 (fun i => (u i - a i) / (b i - a i))
  have hf : Continuous f := by
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun i =>
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i).sub continuous_const).div_const _
  have hinj : Function.Injective f := by
    intro u v huv
    ext i
    have he : (u i - a i) / (b i - a i) = (v i - a i) / (b i - a i) := congrArg (fun z => z i) huv
    have hne := (sub_pos.mpr (hab i)).ne'
    field_simp at he
    nlinarith
  have hcross {S : Set (Space 2)} {i : Fin 2} (h : Crosses a b i S) :
      Crosses ![0, 0] ![1, 1] i (f '' S) := by
    obtain ⟨Γ, hΓ, hΓc, hΓn, ⟨x, hx, hxa⟩, ⟨y, hy, hyb⟩⟩ := h
    refine ⟨f '' Γ, ?_, hΓc.image hf, hΓn.image _ hf.continuousOn,
      ⟨f x, ⟨x, hx, rfl⟩, ?_⟩, ⟨f y, ⟨y, hy, rfl⟩, ?_⟩⟩
    · rintro z ⟨u, hu, rfl⟩
      refine ⟨⟨u, (hΓ hu).1, rfl⟩, ?_⟩
      have hbnd (k : Fin 2) : 0 ≤ f u k ∧ f u k ≤ 1 := by
        change 0 ≤ (u k - a k) / (b k - a k) ∧ (u k - a k) / (b k - a k) ≤ 1
        exact ⟨div_nonneg (sub_nonneg.mpr ((hΓ hu).2 k).1) (sub_pos.mpr (hab k)).le,
          (div_le_one (sub_pos.mpr (hab k))).mpr (sub_le_sub_right ((hΓ hu).2 k).2 _)⟩
      intro k
      fin_cases k
      · simpa using hbnd 0
      · simpa using hbnd 1
    · have he : f x i = 0 := by dsimp [f]; rw [hxa, sub_self, zero_div]
      fin_cases i <;> simpa using he
    · have he : f y i = 1 := by dsimp [f]; rw [hyb, div_self (sub_pos.mpr (hab i)).ne']
      fin_cases i <;> simpa using he
  obtain ⟨z, ⟨u, hu, huf⟩, ⟨v, hv, hvf⟩⟩ :=
    square_crossings_intersect one_pos (hcross hA) (hcross hB)
  have huv := hinj (huf.trans hvf.symm)
  exact ⟨u, hu, huv ▸ hv⟩

/-- A positive horizontal crossing and a nonpositive vertical crossing
cannot coexist. No regularity assumption on the field is needed. -/
theorem not_crosses_opposite_levels {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i)
    {f : Space 2 → ℝ} {l : ℝ}
    (hpos : Crosses a b 0 {u | l < f u}) : ¬ Crosses a b 1 {u | f u ≤ l} := by
  intro hneg
  obtain ⟨u, hu, hv⟩ := rectangle_crossings_intersect hab hpos hneg
  exact (not_lt_of_ge (show f u ≤ l from hv)) (show l < f u from hu)

end Sandpile.Support
