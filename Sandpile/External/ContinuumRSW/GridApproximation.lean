import Sandpile.External.ContinuumRSW.SampledCrossing
import Sandpile.Support.CrossRectangleWalk
import Sandpile.Support.CrossingWitness

/-!
# Grid approximation of rectangle crossings

Connected crossings of a mesh-aligned rectangle admit lattice walks close to the
crossing, and lattice walks give polygonal crossings with a controlled level loss.
-/

open Set

namespace Sandpile.External.ContinuumRSW

open Sandpile Sandpile.Continuum Sandpile.Support Sandpile.Frozen.FixedScaleCrossings

/-- Rounding a point of a mesh-aligned rectangle stays in its lattice rectangle. -/
theorem roundSite_mem_rectangle {t a b : ℝ} {w h : ℕ} (ht : 0 < t)
    (htw : t * (w : ℝ) = a) (hth : t * (h : ℝ) = b)
    {u : Space 2} (hu : u ∈ rectSet ![0, 0] ![a, b]) :
    roundSite t u ∈ planeRectangle w h := by
  have hcoord (i : Fin 2) (n : ℕ) (s : ℝ) (hs : t * (n : ℝ) = s)
      (hui : 0 ≤ u i ∧ u i ≤ s) :
      0 ≤ roundSite t u i ∧ roundSite t u i ≤ (n : ℤ) := by
    have he := abs_le.mp (abs_sub_roundSite_le ht u i)
    constructor
    · have hh : (-1 : ℝ) < (roundSite t u i : ℝ) := by nlinarith
      have : (-1 : ℤ) < roundSite t u i := by exact_mod_cast hh
      omega
    · have hh : (roundSite t u i : ℝ) < (n : ℝ) + 1 := by nlinarith
      have : roundSite t u i < (n : ℤ) + 1 := by exact_mod_cast hh
      omega
  have h0 := hcoord 0 w a htw (by simpa using hu 0)
  have h1 := hcoord 1 h b hth (by simpa using hu 1)
  exact (mem_planeRectangle w h _).mpr ⟨h0.1, h0.2, h1⟩

/-- A chain of nearby grid sites in a rectangle can be joined by a nearby walk. -/
theorem exists_rectangle_walk_chain_general {w h m : ℕ} (v : ℕ → planeRectangle w h)
    {Γ : Set (Space 2)} {t : ℝ} (ht : 0 ≤ t)
    (hΓ : ∀ j ≤ m, ∃ u ∈ Γ, dist (gridPt t (v j)) u ≤ t)
    (hstep : ∀ j < m, ∀ i : Fin 2,
      ((v j : Site 2) i - (v (j + 1) : Site 2) i).natAbs ≤ 1) :
    ∃ p : (rectangleGraph (planeRectangle w h)).Walk (v 0) (v m),
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

/-- A connected set in a mesh-aligned rectangle has a nearby lattice walk
between the rounded endpoints. -/
theorem exists_rectangle_walk_connected_general {Γ : Set (Space 2)} (hc : IsConnected Γ)
    {a b t : ℝ} {w h : ℕ} (ht : 0 < t)
    (htw : t * (w : ℝ) = a) (hth : t * (h : ℝ) = b)
    (hΓ : Γ ⊆ rectSet ![0, 0] ![a, b]) {x y : Space 2} (hx : x ∈ Γ) (hy : y ∈ Γ) :
    ∃ (c d : planeRectangle w h) (p : (rectangleGraph (planeRectangle w h)).Walk c d),
      (c : Site 2) = roundSite t x ∧ (d : Site 2) = roundSite t y ∧
      ∀ z ∈ p.support, ∃ u ∈ Γ, dist (gridPt t z) u ≤ 3 * t := by
  have ht2 : 0 < t / 2 := by positivity
  obtain ⟨m, v, hv0, hvm, hvΓ, hvstep⟩ := exists_vertices_of_reflTransGen ht2 hx
    (reflTransGen_of_isPreconnected hc.isPreconnected ht2 hx y hy)
  let v' (j : ℕ) : planeRectangle w h :=
    ⟨roundSite t (v (min j (m + 1))),
      roundSite_mem_rectangle ht htw hth (hΓ (hvΓ _ (min_le_right _ _)))⟩
  have he (j : ℕ) (hj : j ≤ m + 1) : (v' j : Site 2) = roundSite t (v j) := by
    simp [v', min_eq_left hj]
  obtain ⟨p, hp⟩ := exists_rectangle_walk_chain_general (m := m + 1) v' ht.le
    (fun j hj => by rw [he j hj]; exact ⟨v j, hvΓ j hj, dist_gridPt_roundSite_le ht _⟩)
    (fun j hj i => by
      rw [he j (by omega), he (j + 1) (by omega)]
      exact natAbs_roundSite_le_one ht (by linarith) (hvstep j (by omega)).le i)
  refine ⟨v' 0, v' (m + 1), p, ?_, ?_, hp⟩
  · rw [he 0 (by omega), hv0]
  · rw [he (m + 1) le_rfl, hvm]

/-- Every grid point in a lattice rectangle lies in the corresponding plane rectangle. -/
theorem gridPt_mem_rectangle {t a b : ℝ} {w h : ℕ} (ht : 0 ≤ t)
    (htw : t * (w : ℝ) = a) (hth : t * (h : ℝ) = b)
    {z : Site 2} (hz : z ∈ planeRectangle w h) :
    gridPt t z ∈ rectSet ![0, 0] ![a, b] := by
  have hz' := (mem_planeRectangle w h z).mp hz
  have h0 : (0 : ℝ) ≤ (z 0 : ℝ) := by exact_mod_cast hz'.1
  have h1 : ((z 0 : ℤ) : ℝ) ≤ (w : ℝ) := by exact_mod_cast hz'.2.1
  have h2 : (0 : ℝ) ≤ (z 1 : ℝ) := by exact_mod_cast hz'.2.2.1
  have h3 : ((z 1 : ℤ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast hz'.2.2.2
  intro i
  fin_cases i
  · refine ⟨?_, ?_⟩
    · show (0 : ℝ) ≤ t * (z 0 : ℝ)
      exact mul_nonneg ht h0
    · show t * (z 0 : ℝ) ≤ a
      nlinarith
  · refine ⟨?_, ?_⟩
    · show (0 : ℝ) ≤ t * (z 1 : ℝ)
      exact mul_nonneg ht h2
    · show t * (z 1 : ℝ) ≤ b
      nlinarith

/-- The real binary encoding is at least one half exactly at the threshold. -/
theorem half_le_binaryToReal_threshold (level x : ℝ) :
    (1 / 2 : ℝ) ≤ ((threshold level x : ℕ) : ℝ) ↔ level ≤ x := by
  by_cases h : level ≤ x
  · norm_num [threshold, h]
  · simp [threshold, h]

/-- A continuum crossing gives a sampled lattice crossing when nearby field values
deviate by at most the permitted level loss. -/
theorem sampledCrossingEvent_of_crosses {Ω : Type} {X : Space 2 → Ω → ℝ}
    {ω : Ω} {a b t level ε : ℝ} {w h : ℕ} (ht : 0 < t)
    (htw : t * (w : ℝ) = a) (hth : t * (h : ℝ) = b)
    (hmod : ∀ x ∈ rectSet ![0, 0] ![a, b], ∀ y ∈ rectSet ![0, 0] ![a, b],
      dist x y ≤ 3 * t → |X x ω - X y ω| ≤ ε)
    (hc : Crosses ![0, 0] ![a, b] 0 {u | level ≤ X u ω}) :
    ω ∈ sampledCrossingEvent X t (level - ε) w h := by
  obtain ⟨Γ, hΓ, _, hconn, ⟨x, hx, hx0⟩, ⟨y, hy, hy0⟩⟩ := hc
  obtain ⟨c, d, p, hc, hd, hp⟩ := exists_rectangle_walk_connected_general hconn ht htw hth
    (fun u hu => (hΓ hu).2) hx hy
  change (1 / 2 : ℝ) ≤ crossingValue (planeRectangle w h)
    (fun z => binaryToReal (sampledThreshold X (gridPt t) (level - ε) ω) z)
  apply le_crossingValue_of_walk (isLatticeRectangle_planeRectangle w h) p
  · apply (mem_rectangleLeft_planeRectangle _).mpr
    rw [hc]
    simp [roundSite, show x 0 = 0 from hx0]
  · apply (mem_rectangleRight_planeRectangle _).mpr
    rw [hd]
    exact roundSite_face ht htw hy0
  · intro z hz
    change (1 / 2 : ℝ) ≤ ((threshold (level - ε) (X (gridPt t z) ω) : ℕ) : ℝ)
    rw [half_le_binaryToReal_threshold]
    obtain ⟨u, hu, hzu⟩ := hp z hz
    have hrect : gridPt t z ∈ rectSet ![0, 0] ![a, b] :=
      gridPt_mem_rectangle ht.le htw hth z.property
    have hdiff := hmod (gridPt t z) hrect u (hΓ hu).2 hzu
    have hlevel : level ≤ X u ω := (hΓ hu).1
    linarith [(abs_le.mp hdiff).1]

/-- A sampled lattice crossing gives a continuum crossing, with a level loss
controlled by the modulus of continuity. -/
theorem crosses_of_sampledCrossingEvent {Ω : Type} {X : Space 2 → Ω → ℝ}
    {ω : Ω} {a b t level ε δ : ℝ} {w h : ℕ} (ht : 0 ≤ t)
    (htw : t * (w : ℝ) = a) (hth : t * (h : ℝ) = b)
    (hδ : 0 ≤ δ) (hmesh : 2 * t ≤ δ)
    (hmod : ∀ x ∈ rectSet ![0, 0] ![a, b], ∀ y ∈ rectSet ![0, 0] ![a, b],
      dist x y ≤ δ → |X x ω - X y ω| ≤ ε)
    (hc : ω ∈ sampledCrossingEvent X t level w h) :
    Crosses ![0, 0] ![a, b] 0 {u | level - ε ≤ X u ω} := by
  change (1 / 2 : ℝ) ≤ crossingValue (planeRectangle w h)
    (fun z => binaryToReal (sampledThreshold X (gridPt t) level ω) z) at hc
  obtain ⟨c, d, p, hc, hd, hp⟩ :=
    (le_crossingValue_iff_exists_walk (isLatticeRectangle_planeRectangle w h)
      (planeRectangle_nonempty w h) _ _).mp hc
  have hrect : ∀ z : planeRectangle w h, gridPt t z ∈ rectSet ![0, 0] ![a, b] :=
    fun z => gridPt_mem_rectangle ht htw hth z.property
  refine crosses_of_walk p (fun z => gridPt t (z : Site 2)) hδ hrect ?_ ?_ ?_ ?_
  · intro z v hzv
    have hzv' : (lattice 2).Adj (z : Site 2) (v : Site 2) := hzv
    exact (dist_gridPt_le ht (abs_coord_sub_le_one (lattice_le_starLatticeGraph 2 hzv').2)).trans hmesh
  · intro z hz u hu hdu
    have hval : level ≤ X (gridPt t z) ω := by
      have hzval := hp z hz
      change (1 / 2 : ℝ) ≤ ((threshold level (X (gridPt t z) ω) : ℕ) : ℝ) at hzval
      exact (half_le_binaryToReal_threshold level _).mp hzval
    have hdiff := hmod u hu (gridPt t z) (hrect z) hdu
    show level - ε ≤ X u ω
    linarith [(abs_le.mp hdiff).1]
  · change gridPt t (c : Site 2) 0 = (0 : ℝ)
    rw [gridPt_apply, (mem_rectangleLeft_planeRectangle c).mp hc]
    simp
  · change gridPt t (d : Site 2) 0 = a
    rw [gridPt_apply, (mem_rectangleRight_planeRectangle d).mp hd]
    simpa using htw

end Sandpile.External.ContinuumRSW
