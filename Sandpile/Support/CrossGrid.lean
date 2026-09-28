import Sandpile.Support.CrossPath
import Sandpile.Support.RectangleIntersection
import Sandpile.Support.BlockGeometry

/-! # Discretized planar duality

Continuum planar duality for a square, by discretization onto a fine grid.

The square estimate of `sandpile.tex:2235-2236`, `P(H_{[-R,R]^2}(0)) ≥ 1/2`, is
planar duality together with the sign and coordinate symmetries of the field.
`Sandpile/Support/CrossDuality.lean` carries out the probabilistic half; the
deterministic half is here: for a CONTINUOUS field on the plane, either the
superlevel set crosses the square from left to right, or the sublevel set
crosses it from bottom to top.

Mathlib has neither the Jordan curve theorem nor Brouwer's fixed point theorem,
so the classical continuum routes are closed.  The route taken is the one the
repository already owns on the lattice: `rectangle_nn_star_intersect` of
`Sandpile/Support/RectangleIntersection.lean` says that a nearest-neighbour
left-right walk of a lattice rectangle and a star bottom-top walk of it always
meet, and `crossingValue_le_iff_low_star_walk` turns that into the exact
dichotomy on the crossing value.  A continuous field is transported to the grid
of mesh `t = s/n` by sampling; the dichotomy there returns a walk of grid sites,
and the polygonal chain through those sites is a compact connected crossing of
the plane square (`Sandpile/Support/CrossPath.lean`).

Sampling costs a level.  A grid step of the nearest-neighbour lattice moves each
coordinate by at most one, and a star step likewise, so consecutive chain points
are at distance at most twice the mesh; choosing the mesh below the modulus of
continuity of the field on the square at `η` keeps the field within `η` of its
value at the sampled site along the whole segment.  The dichotomy that comes out
is therefore between the superlevel set at `-η` and the sublevel set at `η`,
for every `η > 0`.

That `η` is the loss the square estimate already carries: `CrossDuality.lean`
compares two crossing events of equal law through the countable chain events of
`Sandpile/Support/CrossUnion.lean`, which brackets a crossing at a level by
chain events at levels a distance `ε` apart.  Since the conclusion is a bound on
the chain event at EVERY level below zero, adding `η` to `ε` changes nothing.
-/

open MeasureTheory Set
namespace Sandpile.Support
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- The grid point of mesh `t` at lattice site `z`: the plane point with coordinates
`t * z i`. -/
noncomputable def gridPt (t : ℝ) (z : Site 2) : Sandpile.Continuum.Space 2 :=
  WithLp.toLp 2 (fun i : Fin 2 => t * (z i : ℝ))

/-- `gridPt t z` evaluated at coordinate `i` is `t * (z i : ℝ)`, unfolding `gridPt`
by `rfl`. -/
theorem gridPt_apply (t : ℝ) (z : Site 2) (i : Fin 2) : gridPt t z i = t * (z i : ℝ) := rfl

/-- `rectSet a b` is compact, being the image under `WithLp.toLp` of the compact product
of closed intervals `∏ i, Icc (a i) (b i)`. -/
theorem isCompact_rectSet (a b : Fin 2 → ℝ) : IsCompact (rectSet a b) := by
  have hset : rectSet a b = (WithLp.toLp 2 : (Fin 2 → ℝ) → Sandpile.Continuum.Space 2) ''
      (Set.univ.pi fun i => Set.Icc (a i) (b i)) := by
    ext p
    constructor
    · intro hp
      exact ⟨fun i => p i, fun i _ => ⟨(hp i).1, (hp i).2⟩, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      intro i
      exact ⟨(hq i (Set.mem_univ i)).1, (hq i (Set.mem_univ i)).2⟩
  rw [hset]
  exact (isCompact_univ_pi fun i => isCompact_Icc).image (PiLp.continuous_toLp 2 fun _ => ℝ)

/-- A modulus of continuity for `f` on the compact set `K`: some `δ > 0` such that points
of `K` within `δ` have `f`-values within `η`, from uniform continuity of `f` on `K`. -/
theorem exists_modulus {K : Set (Sandpile.Continuum.Space 2)} (hK : IsCompact K)
    {f : Sandpile.Continuum.Space 2 → ℝ} (hf : Continuous f) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ δ → |f x - f y| ≤ η := by
  have hUC : UniformContinuousOn f K := hK.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hmain⟩ := Metric.uniformContinuousOn_iff_le.mp hUC η hη
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have h := hmain x hx y hy hxy
  rwa [Real.dist_eq] at h

/-- If two lattice sites differ by at most `1` in each integer coordinate, their real
coordinate differences are also bounded by `1` in absolute value. -/
theorem abs_coord_sub_le_one {z w : Site 2} (h : ∀ i : Fin 2, (z i - w i).natAbs ≤ 1) :
    ∀ i : Fin 2, |(z i : ℝ) - (w i : ℝ)| ≤ 1 := by
  intro i
  have hi : (z i - w i).natAbs ≤ 1 := h i
  have h1 : (-1 : ℤ) ≤ z i - w i := by omega
  have h2 : z i - w i ≤ (1 : ℤ) := by omega
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hr : ((-1 : ℤ) : ℝ) ≤ ((z i - w i : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at hr
    linarith
  · have hr : ((z i - w i : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at hr
    linarith

/-- Two grid points at mesh `t` whose lattice sites differ by at most `1` in each
coordinate are within Euclidean distance `2 * t`, from the coordinatewise bound and the
Euclidean norm formula. -/
theorem dist_gridPt_le {t : ℝ} (ht : 0 ≤ t) {z w : Site 2}
    (h : ∀ i : Fin 2, |(z i : ℝ) - (w i : ℝ)| ≤ 1) :
    dist (gridPt t z) (gridPt t w) ≤ 2 * t := by
  rw [EuclideanSpace.dist_eq]
  have hc : ∀ i : Fin 2, dist (gridPt t z i) (gridPt t w i) ^ 2 ≤ t ^ 2 := by
    intro i
    have h1 : dist (gridPt t z i) (gridPt t w i) = |t * (z i : ℝ) - t * (w i : ℝ)| := by
      rw [Real.dist_eq, gridPt_apply, gridPt_apply]
    have h2 : |t * (z i : ℝ) - t * (w i : ℝ)| ≤ t := by
      have he : t * (z i : ℝ) - t * (w i : ℝ) = t * ((z i : ℝ) - (w i : ℝ)) := by ring
      rw [he, abs_mul, abs_of_nonneg ht]
      nlinarith [abs_nonneg ((z i : ℝ) - (w i : ℝ)), h i]
    rw [h1]
    nlinarith [abs_nonneg (t * (z i : ℝ) - t * (w i : ℝ))]
  have hsum : ∑ i : Fin 2, dist (gridPt t z i) (gridPt t w i) ^ 2 ≤ (2 * t) ^ 2 := by
    rw [Fin.sum_univ_two]
    nlinarith [hc 0, hc 1]
  calc Real.sqrt (∑ i : Fin 2, dist (gridPt t z i) (gridPt t w i) ^ 2)
      ≤ Real.sqrt ((2 * t) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 2 * t := Real.sqrt_sq (by linarith)

/-- A grid point of mesh `t` at a site of the `n × n` lattice rectangle lies in the plane
square `[0, s]²`, where `s = t * n`. -/
theorem gridPt_mem_rectSet {t s : ℝ} (ht : 0 ≤ t) {n : ℕ} (hts : t * (n : ℝ) = s)
    {z : Site 2} (hz : z ∈ Sandpile.planeRectangle n n) :
    gridPt t z ∈ rectSet ![0, 0] ![s, s] := by
  have hz' := (Sandpile.mem_planeRectangle n n z).mp hz
  have h0 : (0 : ℝ) ≤ (z 0 : ℝ) := by exact_mod_cast hz'.1
  have h1 : ((z 0 : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hz'.2.1
  have h2 : (0 : ℝ) ≤ (z 1 : ℝ) := by exact_mod_cast hz'.2.2.1
  have h3 : ((z 1 : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hz'.2.2.2
  intro i
  fin_cases i
  · refine ⟨?_, ?_⟩
    · show (0 : ℝ) ≤ t * (z 0 : ℝ)
      exact mul_nonneg ht h0
    · show t * (z 0 : ℝ) ≤ s
      nlinarith
  · refine ⟨?_, ?_⟩
    · show (0 : ℝ) ≤ t * (z 1 : ℝ)
      exact mul_nonneg ht h2
    · show t * (z 1 : ℝ) ≤ s
      nlinarith

/-- Every point of the segment from `v` to `w` is no farther from `v` than `w` itself is,
since `segSet` parametrizes it as `v + t • (w - v)` for `t ∈ [0, 1]`. -/
theorem dist_mem_segSet {v w u : Sandpile.Continuum.Space 2} (hu : u ∈ segSet v w) :
    dist u v ≤ dist v w := by
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hu
  have hd : (0 : ℝ) ≤ dist v w := dist_nonneg
  have hnorm : dist (segPt v w t) v = |t| * dist v w := by
    rw [dist_eq_norm, segPt, dist_eq_norm]
    simp [norm_smul, norm_sub_rev]
  rw [hnorm, abs_of_nonneg ht0]
  nlinarith

/-- The polygonal chain through the images `g` of the vertices of a graph walk `p` from
`x` to `y` is a `Crosses` witness for `S`: consecutive images are within `δ`, every
segment point within `δ` of the rectangle lies in `S`, and the endpoints meet the two
faces `a i` and `b i`. Built from `crosses_of_pathSet`. -/
theorem crosses_of_walk {V : Type*} {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    (g : V → Sandpile.Continuum.Space 2) {a b : Fin 2 → ℝ} {i : Fin 2}
    {S : Set (Sandpile.Continuum.Space 2)} {δ : ℝ} (hδ : 0 ≤ δ)
    (hrect : ∀ z, g z ∈ rectSet a b)
    (hadj : ∀ z w : V, G.Adj z w → dist (g z) (g w) ≤ δ)
    (hS : ∀ z ∈ p.support, ∀ u ∈ rectSet a b, dist u (g z) ≤ δ → u ∈ S)
    (hx : g x i = a i) (hy : g y i = b i) :
    Crosses a b i S := by
  classical
  have hsupp : ∀ j : ℕ, p.getVert j ∈ p.support := fun j => p.getVert_mem_support j
  have hdist : ∀ j, j ≤ p.length → dist (g (p.getVert j)) (g (p.getVert (j + 1))) ≤ δ := by
    intro j hj
    rcases lt_or_eq_of_le hj with hlt | heq
    · exact hadj _ _ (p.adj_getVert_succ hlt)
    · have h1 : p.getVert j = y := p.getVert_of_length_le (le_of_eq heq.symm)
      have h2 : p.getVert (j + 1) = y := p.getVert_of_length_le (by omega)
      rw [h1, h2, dist_self]
      exact hδ
  refine crosses_of_pathSet p.length (fun j => g (p.getVert j)) ?_ ?_ ?_
  · intro u hu
    obtain ⟨j, hj, hu⟩ := Set.mem_iUnion₂.mp hu
    have hjm : j ≤ p.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hrec : u ∈ rectSet a b :=
      segSet_subset_rectSet (hrect (p.getVert j)) (hrect (p.getVert (j + 1))) hu
    exact ⟨hS (p.getVert j) (hsupp j) u hrec (le_trans (dist_mem_segSet hu) (hdist j hjm)), hrec⟩
  · show g (p.getVert 0) i = a i
    rw [p.getVert_zero]
    exact hx
  · show g (p.getVert (p.length + 1)) i = b i
    rw [p.getVert_of_length_le (by omega)]
    exact hy
/-- The left-right branch of the discretized planar duality: a nearest-neighbour
grid walk across the lattice square on which the field is nonnegative carries a
left-right crossing of the plane square by the superlevel set at `-η`. -/
theorem crosses_superlevel_of_lr_walk {s t η δ : ℝ} {n : ℕ}
    (ht0 : 0 ≤ t) (htn : t * (n : ℝ) = s) (h2t : 2 * t ≤ δ) (hδ : 0 ≤ δ)
    {f : Sandpile.Continuum.Space 2 → ℝ}
    (hmod : ∀ x ∈ rectSet ![0, 0] ![s, s], ∀ y ∈ rectSet ![0, 0] ![s, s],
      dist x y ≤ δ → |f x - f y| ≤ η)
    {c d : Sandpile.planeRectangle n n}
    (p : (Sandpile.rectangleGraph (Sandpile.planeRectangle n n)).Walk c d)
    (hc : (c : Site 2) 0 = 0) (hd : (d : Site 2) 0 = (n : ℤ))
    (hp : ∀ z ∈ p.support, 0 ≤ f (gridPt t (z : Site 2))) :
    Crosses ![0, 0] ![s, s] 0 {u | -η ≤ f u} := by
  have hrect : ∀ z : Sandpile.planeRectangle n n,
      gridPt t (z : Site 2) ∈ rectSet ![0, 0] ![s, s] :=
    fun z => gridPt_mem_rectSet ht0 htn z.2
  refine crosses_of_walk p (fun z => gridPt t (z : Site 2)) hδ hrect ?_ ?_ ?_ ?_
  · intro z w hzw
    have hzw' : (Sandpile.lattice 2).Adj (z : Site 2) (w : Site 2) := hzw
    have hstar := Sandpile.lattice_le_starLatticeGraph 2 hzw'
    exact le_trans (dist_gridPt_le ht0 (abs_coord_sub_le_one hstar.2)) h2t
  · intro z hz u hu hdu
    have h1 : |f u - f (gridPt t (z : Site 2))| ≤ η := hmod u hu _ (hrect z) hdu
    have h2 : 0 ≤ f (gridPt t (z : Site 2)) := hp z hz
    have h3 := (abs_le.mp h1).1
    show -η ≤ f u
    linarith
  · show gridPt t (c : Site 2) 0 = ![(0 : ℝ), 0] 0
    rw [gridPt_apply, hc]
    simp
  · show gridPt t (d : Site 2) 0 = ![s, s] 0
    rw [gridPt_apply, hd]
    simp only [Matrix.cons_val_zero]
    push_cast
    exact htn

/-- The bottom-top branch of the discretized planar duality: a star grid walk up
the lattice square on which the field is nonpositive carries a bottom-top
crossing of the plane square by the sublevel set at `η`. -/
theorem crosses_sublevel_of_star_walk {s t η δ : ℝ} {n : ℕ}
    (ht0 : 0 ≤ t) (htn : t * (n : ℝ) = s) (h2t : 2 * t ≤ δ) (hδ : 0 ≤ δ)
    {f : Sandpile.Continuum.Space 2 → ℝ}
    (hmod : ∀ x ∈ rectSet ![0, 0] ![s, s], ∀ y ∈ rectSet ![0, 0] ![s, s],
      dist x y ≤ δ → |f x - f y| ≤ η)
    {c d : {x : Site 2 // x ∈ ((Sandpile.planeRectangle n n : Finset (Site 2)) : Set (Site 2))}}
    (q : ((Sandpile.starLatticeGraph 2).induce
      ((Sandpile.planeRectangle n n : Finset (Site 2)) : Set (Site 2))).Walk c d)
    (hc : (c : Site 2) 1 = 0) (hd : (d : Site 2) 1 = (n : ℤ))
    (hq : ∀ z ∈ q.support, f (gridPt t (z : Site 2)) ≤ 0) :
    Crosses ![0, 0] ![s, s] 1 {u | f u ≤ η} := by
  have hrect :
      ∀ z : {x : Site 2 // x ∈ ((Sandpile.planeRectangle n n : Finset (Site 2)) : Set (Site 2))},
      gridPt t (z : Site 2) ∈ rectSet ![0, 0] ![s, s] :=
    fun z => gridPt_mem_rectSet ht0 htn (Finset.mem_coe.mp z.2)
  refine crosses_of_walk q (fun z => gridPt t (z : Site 2)) hδ hrect ?_ ?_ ?_ ?_
  · intro z w hzw
    have hstar : (Sandpile.starLatticeGraph 2).Adj (z : Site 2) (w : Site 2) := hzw
    exact le_trans (dist_gridPt_le ht0 (abs_coord_sub_le_one hstar.2)) h2t
  · intro z hz u hu hdu
    have h1 : |f u - f (gridPt t (z : Site 2))| ≤ η := hmod u hu _ (hrect z) hdu
    have h2 : f (gridPt t (z : Site 2)) ≤ 0 := hq z hz
    have h3 := (abs_le.mp h1).2
    show f u ≤ η
    linarith
  · show gridPt t (c : Site 2) 1 = ![(0 : ℝ), 0] 1
    rw [gridPt_apply, hc]
    simp
  · show gridPt t (d : Site 2) 1 = ![s, s] 1
    rw [gridPt_apply, hd]
    simp only [Matrix.cons_val_one]
    push_cast
    exact htn

/-- A mesh fine enough that a grid step is shorter than the modulus. -/
theorem exists_mesh {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    ∃ n : ℕ, (0 : ℝ) < (n : ℝ) ∧ (s / (n : ℝ)) * (n : ℝ) = s ∧ 2 * (s / (n : ℝ)) ≤ δ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * s / δ)
  have hmpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos m
  refine ⟨m + 1, hmpos, ?_, ?_⟩
  · field_simp
  · have hlt : 2 * s / δ < ((m + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    rw [div_lt_iff₀ hδ] at hlt
    rw [show 2 * (s / ((m + 1 : ℕ) : ℝ)) = (2 * s) / ((m + 1 : ℕ) : ℝ) from by ring,
      div_le_iff₀ hmpos]
    nlinarith


/-- Continuum planar duality for a square, at the cost of the level `η`: for a
continuous field on the plane and every `η > 0`, either the superlevel set at
`-η` contains a compact connected left-right crossing of the square `[0,s]²`, or
the sublevel set at `η` contains a compact connected bottom-top crossing of it.

The proof is the discretization of `sandpile.tex:2235-2236` onto a grid of mesh
`t = s/n` fine enough that a grid step is shorter than the modulus of continuity
of the field on the square at `η`.  On that grid the exact lattice duality of
`Sandpile/Support/RectangleIntersection.lean` applies: either the crossing value
of the square is nonnegative, and a nearest-neighbour left-right walk carries
field values at least zero, or it is nonpositive, and a star bottom-top walk
carries field values at most zero.  The polygonal chain through the grid points
of that walk is a compact connected crossing, and the modulus moves the level by
at most `η` along its segments.

The `η` is the same loss the square estimate already carries through the chain
events, so it costs nothing downstream. -/
theorem continuum_square_duality (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (f : Sandpile.Continuum.Space 2 → ℝ) (hf : Continuous f) :
    Crosses ![0, 0] ![s, s] 0 {u | -η ≤ f u} ∨
      Crosses ![0, 0] ![s, s] 1 {u | f u ≤ η} := by
  classical
  obtain ⟨δ, hδ, hmod⟩ := exists_modulus (isCompact_rectSet ![0, 0] ![s, s]) hf hη
  obtain ⟨n, hnpos, htn, h2t⟩ := exists_mesh hs hδ
  set t : ℝ := s / (n : ℝ) with ht
  have ht0 : 0 ≤ t := by
    rw [ht]
    exact le_of_lt (div_pos hs hnpos)
  by_cases hcv : (0 : ℝ) ≤ Sandpile.crossingValue (Sandpile.planeRectangle n n)
      (fun z : Sandpile.planeRectangle n n => f (gridPt t (z : Site 2)))
  · left
    obtain ⟨c, d, p, hc, hd, hp⟩ :=
      Sandpile.exists_lr_walk_of_le_crossingValue
        (fun z : Sandpile.planeRectangle n n => f (gridPt t (z : Site 2))) hcv
    exact crosses_superlevel_of_lr_walk ht0 htn h2t hδ.le hmod p
      ((Sandpile.mem_rectangleLeft_planeRectangle c).mp hc)
      ((Sandpile.mem_rectangleRight_planeRectangle d).mp hd) hp
  · right
    have hcv' : Sandpile.crossingValue (Sandpile.planeRectangle n n)
        (fun z : Sandpile.planeRectangle n n => f (gridPt t (z : Site 2))) ≤ 0 :=
      not_le.mp hcv |>.le
    obtain ⟨c, d, q, hc, hd, hq⟩ :=
      (Sandpile.crossingValue_le_iff_low_star_walk n n
        (fun z : Sandpile.planeRectangle n n => f (gridPt t (z : Site 2))) 0).mp hcv'
    exact crosses_sublevel_of_star_walk ht0 htn h2t hδ.le hmod q hc hd hq

end Sandpile.Support
