/-
The approximating chains of `Sandpile/Support/CrossPath.lean` can be taken with
vertices in a countable set, which is what turns the outer approximation of a
crossing into a countable union of events.

A vertex is admissible when each of its two coordinates is either rational or a
side of the rectangle (`VertexOK`).  There are countably many such points, and
they are dense in the rectangle in the strong sense that a point already lying
on a side keeps that coordinate: `exists_vertex_close`.  That last clause is
what allows the two ends of the chain to stay exactly on the two opposite sides
of the rectangle, which the crossing of `sandpile.tex:2112-2118` requires, while
the remaining coordinate is moved to a rational.

`exists_vertex_path_of_crosses` is then the outer approximation with admissible
vertices: a crossing of a continuous field at level `l` carries, for every
`ε > 0`, a chain of admissible vertices inside the rectangle, from one side to
the opposite side, on which the field is at least `l - ε`.  Together with
`measure_pathEvent_le_crossing` this sandwiches the crossing probability of an
almost surely continuous field between quantities computed from countably many
field values.  The sandwich is not exact: the inner bound is at the level `l`
and the outer bound at the level `l - ε`, and only the levels can be closed up,
by monotonicity in the level, and not the two bounds at one fixed level.
-/
import Sandpile.Support.CrossPath

open MeasureTheory Set

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A rational in a nondegenerate interval, as close as asked to a prescribed
point of the interval. -/
theorem exists_rat_mem_close {lo hi x η : ℝ} (hlohi : lo < hi) (hx0 : lo ≤ x) (hx1 : x ≤ hi)
    (hη : 0 < η) : ∃ q : ℚ, lo ≤ (q : ℝ) ∧ (q : ℝ) ≤ hi ∧ |x - (q : ℝ)| < η := by
  have hAB : max lo (x - η) < min hi (x + η) := by
    rw [max_lt_iff]
    constructor
    · rw [lt_min_iff]
      exact ⟨hlohi, by linarith⟩
    · rw [lt_min_iff]
      exact ⟨by linarith, by linarith⟩
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hAB
  refine ⟨q, le_of_lt (lt_of_le_of_lt (le_max_left _ _) hq1),
    le_of_lt (lt_of_lt_of_le hq2 (min_le_left _ _)), ?_⟩
  rw [abs_lt]
  constructor
  · have := lt_of_lt_of_le hq2 (min_le_right _ _)
    linarith
  · have := lt_of_le_of_lt (le_max_right _ _) hq1
    linarith

/-- A statement about both coordinates of the plane. -/
theorem fin2_forall {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ k, P k := by
  intro k
  fin_cases k
  exacts [h0, h1]

/-- The Euclidean distance is small when both coordinate differences are. -/
theorem dist_lt_of_coords {v w : Sandpile.Continuum.Space 2} {η : ℝ} (hη : 0 < η)
    (h0 : |v 0 - w 0| < η / 2) (h1 : |v 1 - w 1| < η / 2) : dist v w < η := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
  rw [show η = Real.sqrt (η ^ 2) by rw [Real.sqrt_sq hη.le]]
  apply Real.sqrt_lt_sqrt
  · positivity
  · have hs0 : |v 0 - w 0| ^ 2 < (η / 2) ^ 2 := by nlinarith [abs_nonneg (v 0 - w 0)]
    have hs1 : |v 1 - w 1| ^ 2 < (η / 2) ^ 2 := by nlinarith [abs_nonneg (v 1 - w 1)]
    nlinarith

/-- One coordinate of an admissible vertex: a rational in the interval, except
that an endpoint of the interval is kept as it is. -/
theorem exists_coord_close {lo hi x η : ℝ} (hlohi : lo < hi) (hx0 : lo ≤ x) (hx1 : x ≤ hi)
    (hη : 0 < η) : ∃ y : ℝ, lo ≤ y ∧ y ≤ hi ∧ |x - y| < η ∧
      ((∃ q : ℚ, y = (q : ℝ)) ∨ y = lo ∨ y = hi) ∧ (x = lo → y = lo) ∧ (x = hi → y = hi) := by
  by_cases hlo : x = lo
  · refine ⟨lo, le_refl _, le_of_lt hlohi, by simp [hlo, hη], Or.inr (Or.inl rfl),
      fun _ => rfl, fun hxhi => absurd (hlo ▸ hxhi) (ne_of_lt hlohi)⟩
  · by_cases hhi : x = hi
    · refine ⟨hi, le_of_lt hlohi, le_refl _, by simp [hhi, hη], Or.inr (Or.inr rfl),
        fun hxlo => absurd (hhi ▸ hxlo).symm (ne_of_lt hlohi), fun _ => rfl⟩
    · obtain ⟨q, hq1, hq2, hq3⟩ := exists_rat_mem_close hlohi hx0 hx1 hη
      exact ⟨(q : ℝ), hq1, hq2, hq3, Or.inl ⟨q, rfl⟩, fun h => absurd h hlo, fun h => absurd h hhi⟩

/-- An admissible vertex: each coordinate is rational or a side of the
rectangle. -/
def VertexOK (a b : Fin 2 → ℝ) (p : Sandpile.Continuum.Space 2) : Prop :=
  ∀ k : Fin 2, (∃ q : ℚ, p k = (q : ℝ)) ∨ p k = a k ∨ p k = b k

/-- An admissible vertex as close as asked to a prescribed point of the
rectangle, keeping every coordinate that already lies on a side. -/
theorem exists_vertex_close {a b : Fin 2 → ℝ} (h0 : a 0 < b 0) (h1 : a 1 < b 1)
    {v : Sandpile.Continuum.Space 2} (hv : v ∈ rectSet a b) {η : ℝ} (hη : 0 < η) :
    ∃ w : Sandpile.Continuum.Space 2, w ∈ rectSet a b ∧ dist v w < η ∧ VertexOK a b w ∧
      (∀ k : Fin 2, v k = a k → w k = a k) ∧ (∀ k : Fin 2, v k = b k → w k = b k) := by
  obtain ⟨y0, hy0lo, hy0hi, hy0d, hy0v, hy0a, hy0b⟩ :=
    exists_coord_close h0 (hv 0).1 (hv 0).2 (by positivity : (0:ℝ) < η / 2)
  obtain ⟨y1, hy1lo, hy1hi, hy1d, hy1v, hy1a, hy1b⟩ :=
    exists_coord_close h1 (hv 1).1 (hv 1).2 (by positivity : (0:ℝ) < η / 2)
  have e0 : hSeg y1 y0 0 = y0 := hSeg_apply_zero y1 y0
  have e1 : hSeg y1 y0 1 = y1 := hSeg_apply_one y1 y0
  refine ⟨hSeg y1 y0, fin2_forall ?_ ?_, dist_lt_of_coords hη ?_ ?_, fin2_forall ?_ ?_,
    fin2_forall ?_ ?_, fin2_forall ?_ ?_⟩
  · exact ⟨by rw [e0]; exact hy0lo, by rw [e0]; exact hy0hi⟩
  · exact ⟨by rw [e1]; exact hy1lo, by rw [e1]; exact hy1hi⟩
  · rw [e0]; exact hy0d
  · rw [e1]; exact hy1d
  · rw [e0]; exact hy0v
  · rw [e1]; exact hy1v
  · exact fun h => by rw [e0]; exact hy0a h
  · exact fun h => by rw [e1]; exact hy1a h
  · exact fun h => by rw [e0]; exact hy0b h
  · exact fun h => by rw [e1]; exact hy1b h

/-- A segment lies in the thickening of a set near one of its endpoints. -/
theorem segSet_subset_thickening' {δ ρ : ℝ} {Γ : Set (Sandpile.Continuum.Space 2)}
    {v w z : Sandpile.Continuum.Space 2} (hz : z ∈ Γ) (hvz : dist v z < ρ) (hd : dist v w < δ) :
    segSet v w ⊆ Metric.thickening (ρ + δ) Γ := by
  rintro u hu
  rw [Metric.mem_thickening_iff]
  refine ⟨z, hz, ?_⟩
  have huv : dist u v < δ := by
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hu
    have hnorm : dist (segPt v w t) v = |t| * dist v w := by
      rw [dist_eq_norm, segPt, dist_eq_norm]
      simp [norm_smul, norm_sub_rev]
    rw [hnorm, abs_of_nonneg ht0]
    have hdd : (0 : ℝ) ≤ dist v w := dist_nonneg
    nlinarith
  calc dist u z ≤ dist u v + dist v z := dist_triangle u v z
    _ < δ + ρ := by linarith
    _ = ρ + δ := by ring

theorem exists_vertex_path_of_crosses {X : Sandpile.Continuum.Space 2 → ℝ} (hX : Continuous X)
    {a b : Fin 2 → ℝ} (ha0 : a 0 < b 0) (ha1 : a 1 < b 1) {i : Fin 2} {l ε : ℝ} (hε : 0 < ε)
    (h : Crosses a b i {u | l ≤ X u}) :
    ∃ (m : ℕ) (v : ℕ → Sandpile.Continuum.Space 2),
      pathSet (m + 1) v ⊆ rectSet a b ∧
      (∀ u ∈ pathSet (m + 1) v, l - ε ≤ X u) ∧
      v 0 i = a i ∧ v (m + 1) i = b i ∧
      ∀ j ≤ m + 1, VertexOK a b (v j) := by
  obtain ⟨Γ, hsub, hcomp, hconn, ⟨p, hpΓ, hpa⟩, ⟨q, hqΓ, hqb⟩⟩ := h
  have hGopen : IsOpen {u : Sandpile.Continuum.Space 2 | l - ε < X u} :=
    isOpen_lt continuous_const hX
  have hΓG : Γ ⊆ {u : Sandpile.Continuum.Space 2 | l - ε < X u} := by
    intro u hu
    have hlu : l ≤ X u := (hsub hu).1
    show l - ε < X u
    linarith
  obtain ⟨δ, hδ, hδsub⟩ := hcomp.exists_thickening_subset_open hGopen hΓG
  have hδ4 : (0 : ℝ) < δ / 4 := by linarith
  have hchain := reflTransGen_of_isPreconnected hconn.isPreconnected hδ4 hpΓ q hqΓ
  obtain ⟨m, c, hc0, hcm, hcΓ, hcd⟩ := exists_vertices_of_reflTransGen hδ4 hpΓ hchain
  have hchoose : ∀ j : ℕ, ∃ w : Sandpile.Continuum.Space 2, j ≤ m + 1 →
      (w ∈ rectSet a b ∧ dist (c j) w < δ / 4 ∧ VertexOK a b w ∧
        (∀ k : Fin 2, c j k = a k → w k = a k) ∧ (∀ k : Fin 2, c j k = b k → w k = b k)) := by
    intro j
    by_cases hj : j ≤ m + 1
    · obtain ⟨w, hw1, hw2, hw3, hw4, hw5⟩ :=
        exists_vertex_close ha0 ha1 (hsub (hcΓ j hj)).2 hδ4
      exact ⟨w, fun _ => ⟨hw1, hw2, hw3, hw4, hw5⟩⟩
    · exact ⟨c j, fun hj' => absurd hj' hj⟩
  choose v hv using hchoose
  have hstep : ∀ j ≤ m, dist (v j) (v (j + 1)) < 3 * δ / 4 := by
    intro j hj
    have h1 : dist (v j) (c j) < δ / 4 := by
      rw [dist_comm]; exact (hv j (by omega)).2.1
    have h2 : dist (c j) (c (j + 1)) < δ / 4 := hcd j hj
    have h3 : dist (c (j + 1)) (v (j + 1)) < δ / 4 := (hv (j + 1) (by omega)).2.1
    calc dist (v j) (v (j + 1)) ≤ dist (v j) (c j) + dist (c j) (v (j + 1)) :=
          dist_triangle _ _ _
      _ ≤ dist (v j) (c j) + (dist (c j) (c (j + 1)) + dist (c (j + 1)) (v (j + 1))) := by
          gcongr
          exact dist_triangle _ _ _
      _ < δ / 4 + (δ / 4 + δ / 4) := by gcongr
      _ = 3 * δ / 4 := by ring
  refine ⟨m, v, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨j, hj, hu⟩ := Set.mem_iUnion₂.mp hu
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact segSet_subset_rectSet (hv j (by omega)).1 (hv (j + 1) (by omega)).1 hu
  · intro u hu
    obtain ⟨j, hj, hu⟩ := Set.mem_iUnion₂.mp hu
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hvz : dist (v j) (c j) < δ / 4 := by
      rw [dist_comm]; exact (hv j (by omega)).2.1
    have hthick : u ∈ Metric.thickening (δ / 4 + 3 * δ / 4) Γ :=
      segSet_subset_thickening' (hcΓ j (by omega)) hvz (hstep j hjm) hu
    have hrw : δ / 4 + 3 * δ / 4 = δ := by ring
    rw [hrw] at hthick
    exact le_of_lt (hδsub hthick)
  · exact (hv 0 (by omega)).2.2.2.1 i (by rw [hc0]; exact hpa)
  · exact (hv (m + 1) (by omega)).2.2.2.2 i (by rw [hcm]; exact hqb)
  · exact fun j hj => (hv j hj).2.2.1

end Sandpile.Support
