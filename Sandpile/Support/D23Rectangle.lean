/-
Rectangle confinement in the continuum-to-discrete percolation step,
`sandpile.tex:2645-2660`. Coordinate projection preserves nearest-neighbor
walks after repeated vertices are removed. Applied to the continuous field
composed with the rectangle projection, this gives crossings at every
sufficiently fine aligned mesh, and hence all four good-block conditions.
-/
import Sandpile.Support.D23Mesh
import Sandpile.Support.BlockVerticalWalk

open Set
namespace Sandpile.Support
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

noncomputable def rectClamp (b : Fin 2 → ℝ) (u : Space 2) : Space 2 :=
  WithLp.toLp 2 (fun i => max 0 (min (b i) (u i)))

noncomputable def latticeClamp (w h : ℕ) (z : Site 2) : planeRectangle w h :=
  ⟨fun i => max 0 (min (![w, h] i : ℤ) (z i)), by
    rw [mem_planeRectangle]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega⟩

theorem continuous_rectClamp (b : Fin 2 → ℝ) : Continuous (rectClamp b) := by
  apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
  exact continuous_pi fun i => continuous_const.max (continuous_const.min (by fun_prop))

theorem rectClamp_eq {b : Fin 2 → ℝ} {u : Space 2}
    (hu : u ∈ rectSet ![0, 0] b) : rectClamp b u = u := by
  apply PiLp.ext
  intro i
  have hi := hu i
  have hz : ![(0 : ℝ), 0] i = 0 := by fin_cases i <;> rfl
  simp only [hz] at hi
  exact (congrArg (max 0) (min_eq_right hi.2)).trans (max_eq_right hi.1)

theorem gridPt_latticeClamp {t : ℝ} (ht : 0 ≤ t) (w h : ℕ) (z : Site 2) :
    gridPt t (latticeClamp w h z) = rectClamp ![t * w, t * h] (gridPt t z) := by
  apply PiLp.ext
  intro i
  change t * ((max 0 (min (![w, h] i : ℤ) (z i)) : ℤ) : ℝ) =
    max 0 (min (![t * w, t * h] i) (t * (z i : ℝ)))
  push_cast
  rw [mul_max_of_nonneg _ _ ht, mul_min_of_nonneg _ _ ht, mul_zero]
  fin_cases i <;> rfl

theorem latticeClamp_adj_or_eq (w h : ℕ) {z v : Site 2}
    (hzv : (lattice 2).Adj z v) :
    (latticeClamp w h z = latticeClamp w h v) ∨
      (rectangleGraph (planeRectangle w h)).Adj (latticeClamp w h z) (latticeClamp w h v) := by
  classical
  by_cases he : latticeClamp w h z = latticeClamp w h v
  · exact Or.inl he
  right
  obtain ⟨i, hi⟩ := hzv
  have hother : ∀ j ≠ i, z j = v j := by
    intro j hj
    rcases hi with hi | hi
    · have := congrFun hi j
      simpa [LatticeProb.unit, hj] using this.symm
    · have := congrFun hi j
      simpa [LatticeProb.unit, hj] using this
  have hone : z i - v i = 1 ∨ z i - v i = -1 := by
    rcases hi with hi | hi
    · have := congrFun hi i
      simp [LatticeProb.unit] at this
      omega
    · have := congrFun hi i
      simp [LatticeProb.unit] at this
      omega
  apply adj_of_coord i
  · intro j hj
    change max 0 (min (![w, h] j : ℤ) (z j)) = max 0 (min (![w, h] j : ℤ) (v j))
    rw [hother j hj]
  · have hne : (latticeClamp w h z : Site 2) i ≠ (latticeClamp w h v : Site 2) i := by
      intro hh
      apply he
      apply Subtype.ext
      funext j
      by_cases hj : j = i
      · subst j; exact hh
      · change max 0 (min (![w, h] j : ℤ) (z j)) = max 0 (min (![w, h] j : ℤ) (v j))
        rw [hother j hj]
    change (max 0 (min (![w, h] i : ℤ) (z i)) -
      max 0 (min (![w, h] i : ℤ) (v i))).natAbs = 1
    change max 0 (min (![w, h] i : ℤ) (z i)) ≠ max 0 (min (![w, h] i : ℤ) (v i)) at hne
    omega

theorem exists_rectangle_walk_of_lattice_walk (w h : ℕ) {z v : Site 2}
    (p : (lattice 2).Walk z v) :
    ∃ q : (rectangleGraph (planeRectangle w h)).Walk (latticeClamp w h z) (latticeClamp w h v),
      ∀ a ∈ q.support, ∃ b ∈ p.support, a = latticeClamp w h b := by
  induction p with
  | nil =>
    exact ⟨.nil, by simp⟩
  | @cons z v u hzv p ih =>
    obtain ⟨q, hq⟩ := ih
    rcases latticeClamp_adj_or_eq w h hzv with he | he
    · refine ⟨q.copy he.symm rfl, ?_⟩
      intro a ha
      obtain ⟨b, hb, hab⟩ := hq a (by simpa using ha)
      exact ⟨b, by simp [hb], hab⟩
    · refine ⟨q.cons he, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · exact ⟨z, by simp, ha⟩
      · obtain ⟨b, hb, hab⟩ := hq a ha
        exact ⟨b, by simp [hb], hab⟩

theorem latticeClamp_roundSite_face {t : ℝ} (ht : 0 < t) (w h : ℕ)
    (x : Space 2) (i : Fin 2) :
    (x i = 0 → (latticeClamp w h (roundSite t x) : Site 2) i = 0) ∧
    (x i = t * (![w, h] i : ℤ) →
      (latticeClamp w h (roundSite t x) : Site 2) i = (![w, h] i : ℤ)) := by
  constructor
  · intro hx
    change max 0 (min (![w, h] i : ℤ) (round (x i / t))) = 0
    simp [hx]
  · intro hx
    change max 0 (min (![w, h] i : ℤ) (round (x i / t))) = _
    rw [hx, mul_div_cancel_left₀ _ ht.ne']
    simp

/-- A continuum rectangle crossing gives a confined lattice crossing at every
sufficiently fine mesh aligned with its sides. -/
theorem exists_rectangle_walk_of_crosses_small_mesh
    {b : Fin 2 → ℝ} {X : Space 2 → ℝ} (hX : Continuous X)
    {i : Fin 2} {l η : ℝ} (hη : 0 < η)
    (hc : Crosses ![0, 0] b i {u | l ≤ X u}) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      ∀ w h : ℕ, b = ![t * w, t * h] →
        ∃ (a c : planeRectangle w h)
          (q : (rectangleGraph (planeRectangle w h)).Walk a c),
          (a : Site 2) i = 0 ∧ (c : Site 2) i = (![w, h] i : ℤ) ∧
          ∀ z ∈ q.support, l - η < X (gridPt t (z : Site 2)) := by
  obtain ⟨Γ, hΓ, hcomp, hconn, ⟨x, hx, hxface⟩, ⟨y, hy, hyface⟩⟩ := hc
  have hXc : Continuous (fun u => X (rectClamp b u)) := hX.comp (continuous_rectClamp b)
  obtain ⟨t₀, ht₀, hwalk⟩ := exists_lattice_walk_superlevel_of_small_mesh hXc
    hcomp hconn hη (fun u hu => by
      change l ≤ X (rectClamp b u)
      rw [rectClamp_eq (hΓ hu).2]
      exact (hΓ hu).1)
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht htt w h hb
  obtain ⟨p, hp⟩ := hwalk t ht htt x hx y hy
  obtain ⟨q, hq⟩ := exists_rectangle_walk_of_lattice_walk w h p
  refine ⟨_, _, q, (latticeClamp_roundSite_face ht w h x i).1 ?_,
    (latticeClamp_roundSite_face ht w h y i).2 ?_, ?_⟩
  · simpa only [show ![(0 : ℝ), 0] i = 0 by fin_cases i <;> rfl] using hxface
  · rw [hyface, hb]
    fin_cases i <;> simp
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := hq z hz
    obtain ⟨j, rfl, hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
    rw [gridPt_latticeClamp ht.le, ← hb]
    exact hp j hj

/-- The confined horizontal walk gives a crossing-value bound for any lattice
field above the sampled continuum field minus the prescribed margin. -/
theorem crossingValue_of_continuum_small_mesh
    {b : Fin 2 → ℝ} {X : Space 2 → ℝ} (hX : Continuous X)
    {l η : ℝ} (hη : 0 < η) (hc : Crosses ![0, 0] b 0 {u | l ≤ X u}) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      ∀ w h : ℕ, b = ![t * w, t * h] →
        ∀ F : Site 2 → ℝ, ∀ a : ℝ,
          (∀ z ∈ planeRectangle w h, l - η < X (gridPt t z) → a ≤ F z) →
          a ≤ crossingValue (planeRectangle w h) (fun z => F z) := by
  obtain ⟨t₀, ht₀, hwalk⟩ := exists_rectangle_walk_of_crosses_small_mesh hX hη hc
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht htt w h hb F a hF
  obtain ⟨x, y, p, hx, hy, hp⟩ := hwalk t ht htt w h hb
  apply le_crossingValue_of_walk (isLatticeRectangle_planeRectangle w h) p
    ((mem_rectangleLeft_planeRectangle x).mpr hx)
    ((mem_rectangleRight_planeRectangle y).mpr hy)
  exact fun z hz => hF z z.property (hp z hz)

/-- The same transfer for the vertical crossing value. -/
theorem verticalCrossingValue_of_continuum_small_mesh
    {b : Fin 2 → ℝ} {X : Space 2 → ℝ} (hX : Continuous X)
    {l η : ℝ} (hη : 0 < η) (hc : Crosses ![0, 0] b 1 {u | l ≤ X u}) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      ∀ w h : ℕ, b = ![t * w, t * h] →
        ∀ F : Site 2 → ℝ, ∀ a : ℝ,
          (∀ z ∈ planeRectangle w h, l - η < X (gridPt t z) → a ≤ F z) →
          a ≤ verticalCrossingValue w h (fun z => F z) := by
  obtain ⟨t₀, ht₀, hwalk⟩ := exists_rectangle_walk_of_crosses_small_mesh hX hη hc
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht htt w h hb F a hF
  obtain ⟨x, y, p, hx, hy, hp⟩ := hwalk t ht htt w h hb
  apply le_verticalCrossingValue_of_walk (fun z => F z) p hx hy
  exact fun z hz => hF z z.property (hp z hz)

/-- The four prescribed continuum crossings force a good block at every
sufficiently large integer scale, for any lattice field with the stated margin. -/
theorem blockGood_of_continuum_crossings
    {X : Space 2 → ℝ} (hX : Continuous X) {l η : ℝ} (hη : 0 < η)
    (hsqH : Crosses ![0, 0] ![2, 2] 0 {u | l ≤ X u})
    (hsqV : Crosses ![0, 0] ![2, 2] 1 {u | l ≤ X u})
    (hwide : Crosses ![0, 0] ![4, 2] 0 {u | l ≤ X u})
    (htall : Crosses ![0, 0] ![2, 4] 1 {u | l ≤ X u}) :
    ∃ R₀ : ℕ, 1 ≤ R₀ ∧ ∀ R : ℕ, R₀ ≤ R → ∀ F : Site 2 → ℝ, ∀ a : ℝ,
      (∀ z ∈ planeRectangle (4 * R) (4 * R),
        l - η < X (gridPt (1 / (R : ℝ)) z) → a ≤ F z) →
      BlockGood R F a 0 := by
  obtain ⟨t₁, ht₁, h₁⟩ := crossingValue_of_continuum_small_mesh hX hη hsqH
  obtain ⟨t₂, ht₂, h₂⟩ := verticalCrossingValue_of_continuum_small_mesh hX hη hsqV
  obtain ⟨t₃, ht₃, h₃⟩ := crossingValue_of_continuum_small_mesh hX hη hwide
  obtain ⟨t₄, ht₄, h₄⟩ := verticalCrossingValue_of_continuum_small_mesh hX hη htall
  let t₀ := min (min t₁ t₂) (min t₃ t₄)
  have ht₀ : 0 < t₀ := lt_min (lt_min ht₁ ht₂) (lt_min ht₃ ht₄)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / t₀)
  refine ⟨m + 1, by omega, ?_⟩
  intro R hR F a hF
  have hRp : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have ht : 0 < 1 / (R : ℝ) := by positivity
  have htt : 1 / (R : ℝ) ≤ t₀ := by
    apply (div_le_iff₀ hRp).mpr
    have hmR : (m : ℝ) ≤ R := by exact_mod_cast (show m ≤ R by omega)
    have := (div_lt_iff₀ ht₀).mp hm
    nlinarith
  have ha₁ : 1 / (R : ℝ) ≤ t₁ := htt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have ha₂ : 1 / (R : ℝ) ≤ t₂ := htt.trans ((min_le_left _ _).trans (min_le_right _ _))
  have ha₃ : 1 / (R : ℝ) ≤ t₃ := htt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha₄ : 1 / (R : ℝ) ≤ t₄ := htt.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbound (w h : ℕ) (hw : w ≤ 4 * R) (hh : h ≤ 4 * R)
      (z : Site 2) (hz : z ∈ planeRectangle w h) :
      l - η < X (gridPt (1 / (R : ℝ)) z) → a ≤ F z := by
    apply hF z
    have hz' := (mem_planeRectangle w h z).mp hz
    exact (mem_planeRectangle _ _ z).mpr
      ⟨hz'.1, hz'.2.1.trans (by exact_mod_cast hw), hz'.2.2.1,
        hz'.2.2.2.trans (by exact_mod_cast hh)⟩
  have halign (w h : ℕ) :
      ![(w : ℝ), (h : ℝ)] =
        ![(1 / (R : ℝ)) * (w * R : ℕ), (1 / (R : ℝ)) * (h * R : ℕ)] := by
    ext i
    fin_cases i <;> simp <;> field_simp
  have hh₁ := h₁ _ ht ha₁ (2 * R) (2 * R) (halign 2 2) F a
    (hbound _ _ (by omega) (by omega))
  have hh₂ := h₂ _ ht ha₂ (2 * R) (2 * R) (halign 2 2) F a
    (hbound _ _ (by omega) (by omega))
  have hh₃ := h₃ _ ht ha₃ (4 * R) (2 * R) (halign 4 2) F a
    (hbound _ _ (by omega) (by omega))
  have hh₄ := h₄ _ ht ha₄ (2 * R) (4 * R) (halign 2 4) F a
    (hbound _ _ (by omega) (by omega))
  have hshift (z : Site 2) : blockShift R 0 z = z := by
    funext i
    fin_cases i <;> simp [blockShift]
  simpa only [BlockGood, hshift] using And.intro hh₁ (And.intro hh₂ (And.intro hh₃ hh₄))

end Sandpile.Support
