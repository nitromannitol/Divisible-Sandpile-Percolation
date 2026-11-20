import Sandpile.External.ContinuumRSW.GridApproximation
import Sandpile.Support.CrossVertex

/-!
# Grid crossings with a non-aligned face

Clipping the final grid column onto a prescribed vertical face turns a lattice
crossing into a crossing of a rectangle whose width need not be a mesh multiple.
-/

open Set

namespace Sandpile.External.ContinuumRSW

open Sandpile Sandpile.Continuum Sandpile.Support Sandpile.Frozen.FixedScaleCrossings

/-- A grid point with its first coordinate clipped at the right face. -/
noncomputable def clippedGridPt (t a : ℝ) (z : Site 2) : Space 2 :=
  WithLp.toLp 2 ![min a (t * (z 0 : ℝ)), t * (z 1 : ℝ)]

/-- A clipped point lies inside the rectangle bounded by the clipping face. -/
theorem clippedGridPt_mem_rectangle {t a b : ℝ} {w h : ℕ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hth : t * (h : ℝ) = b)
    {z : Site 2} (hz : z ∈ planeRectangle w h) :
    clippedGridPt t a z ∈ rectSet ![0, 0] ![a, b] := by
  have hz' := (mem_planeRectangle w h z).mp hz
  have h0 : (0 : ℝ) ≤ (z 0 : ℝ) := by exact_mod_cast hz'.1
  have h1 : (0 : ℝ) ≤ (z 1 : ℝ) := by exact_mod_cast hz'.2.2.1
  have h2 : (z 1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hz'.2.2.2
  intro i
  fin_cases i
  · change 0 ≤ min a (t * (z 0 : ℝ)) ∧ min a (t * (z 0 : ℝ)) ≤ a
    exact ⟨le_min ha (mul_nonneg ht h0), min_le_left _ _⟩
  · change 0 ≤ t * (z 1 : ℝ) ∧ t * (z 1 : ℝ) ≤ b
    exact ⟨mul_nonneg ht h1, by nlinarith⟩

/-- Clipping a grid point moves it by at most four mesh lengths when the final
column is at most one mesh beyond the clipping face. -/
theorem dist_clippedGridPt_le {t a : ℝ} {w h : ℕ} (ht : 0 < t)
    (hwidth : t * (w : ℝ) ≤ a + t) {z : Site 2} (hz : z ∈ planeRectangle w h) :
    dist (clippedGridPt t a z) (gridPt t z) ≤ 4 * t := by
  have hz' := (mem_planeRectangle w h z).mp hz
  have hz0 : (z 0 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hz'.2.1
  have hupper : t * (z 0 : ℝ) ≤ a + t := by nlinarith
  have hclip : |min a (t * (z 0 : ℝ)) - t * (z 0 : ℝ)| ≤ t := by
    apply abs_le.mpr
    constructor
    · have hmin : t * (z 0 : ℝ) - t ≤ min a (t * (z 0 : ℝ)) :=
        le_min (by linarith) (by linarith)
      linarith
    · have hmin := min_le_right a (t * (z 0 : ℝ))
      linarith
  apply (dist_lt_of_coords (show 0 < 4 * t by positivity) ?_ ?_).le
  · change |min a (t * (z 0 : ℝ)) - t * (z 0 : ℝ)| < 4 * t / 2
    linarith
  · change |t * (z 1 : ℝ) - t * (z 1 : ℝ)| < 4 * t / 2
    simp only [sub_self, abs_zero]
    positivity

/-- A sampled crossing of a rectangle whose right boundary is less than one
mesh beyond `a` yields a continuum crossing ending exactly at `a`. -/
theorem crosses_of_sampledCrossingEvent_clipped {Ω : Type} {X : Space 2 → Ω → ℝ}
    {ω : Ω} {a b bigA t level ε δ : ℝ} {w h : ℕ} (ht : 0 < t)
    (ha : 0 ≤ a) (hwidth : a ≤ t * (w : ℝ)) (hwidth' : t * (w : ℝ) ≤ a + t)
    (hbig : t * (w : ℝ) ≤ bigA) (hth : t * (h : ℝ) = b)
    (hmesh : 14 * t ≤ δ)
    (hmod : ∀ x ∈ rectSet ![0, 0] ![bigA, b], ∀ y ∈ rectSet ![0, 0] ![bigA, b],
      dist x y ≤ δ → |X x ω - X y ω| ≤ ε)
    (hc : ω ∈ sampledCrossingEvent X t level w h) :
    Crosses ![0, 0] ![a, b] 0 {u | level - ε ≤ X u ω} := by
  change (1 / 2 : ℝ) ≤ crossingValue (planeRectangle w h)
    (fun z => binaryToReal (sampledThreshold X (gridPt t) level ω) z) at hc
  obtain ⟨c, d, p, hc, hd, hp⟩ :=
    (le_crossingValue_iff_exists_walk (isLatticeRectangle_planeRectangle w h)
      (planeRectangle_nonempty w h) _ _).mp hc
  have hrect : ∀ z : planeRectangle w h, clippedGridPt t a z ∈ rectSet ![0, 0] ![a, b] :=
    fun z => clippedGridPt_mem_rectangle ht.le ha hth z.property
  have hgrid : ∀ z : planeRectangle w h, gridPt t z ∈ rectSet ![0, 0] ![bigA, b] := by
    intro z
    have hz := gridPt_mem_rectangle ht.le rfl hth z.property
    exact rectSet_mono (by intro i; rfl) (by intro i; fin_cases i <;> simp_all) hz
  have hsmall : rectSet ![0, 0] ![a, b] ⊆ rectSet ![0, 0] ![bigA, b] :=
    rectSet_mono (by intro i; rfl) (by
      intro i
      fin_cases i
      · simpa using hwidth.trans hbig
      · simp)
  refine crosses_of_walk p (fun z => clippedGridPt t a (z : Site 2)) (δ := 10 * t) (by positivity)
    hrect ?_ ?_ ?_ ?_
  · intro z v hzv
    have hzv' : (lattice 2).Adj (z : Site 2) (v : Site 2) := hzv
    have hdist := dist_gridPt_le ht.le (abs_coord_sub_le_one (lattice_le_starLatticeGraph 2 hzv').2)
    have hz := dist_clippedGridPt_le ht hwidth' z.property
    have hv := dist_clippedGridPt_le ht hwidth' v.property
    have htri := dist_triangle (clippedGridPt t a z) (gridPt t z) (clippedGridPt t a v)
    have htri' := dist_triangle (gridPt t z) (gridPt t v) (clippedGridPt t a v)
    rw [dist_comm (gridPt t v) (clippedGridPt t a v)] at htri'
    linarith
  · intro z hz u hu hdu
    have hval : level ≤ X (gridPt t z) ω := by
      have hzval := hp z hz
      change (1 / 2 : ℝ) ≤ ((threshold level (X (gridPt t z) ω) : ℕ) : ℝ) at hzval
      exact (half_le_binaryToReal_threshold level _).mp hzval
    have hclip := dist_clippedGridPt_le ht hwidth' z.property
    have htri := dist_triangle u (clippedGridPt t a z) (gridPt t z)
    have hdist : dist u (gridPt t z) ≤ δ := by linarith
    have hdiff := hmod u (hsmall hu) (gridPt t z) (hgrid z) hdist
    show level - ε ≤ X u ω
    linarith [(abs_le.mp hdiff).1]
  · change min a (t * ((c : Site 2) 0 : ℝ)) = 0
    rw [(mem_rectangleLeft_planeRectangle c).mp hc]
    simp [min_eq_right ha]
  · change min a (t * ((d : Site 2) 0 : ℝ)) = a
    rw [(mem_rectangleRight_planeRectangle d).mp hd]
    simpa using min_eq_left hwidth

end Sandpile.External.ContinuumRSW
