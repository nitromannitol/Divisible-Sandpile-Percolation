import Sandpile.Support.CrossGrid
import Sandpile.Support.CrossBlocking

/-!
# Transferring a connected set to a nearest-neighbour lattice walk

The blocking half of Step 1 of `prop:fixed-scale-crossings`
(`sandpile.tex:2233-2235`), continued: the transfer of a compact connected set of
the plane to a nearest-neighbour walk of the lattice of mesh `t`.

`exists_vertices_of_reflTransGen` and `reflTransGen_of_isPreconnected` of
`Sandpile/Support/CrossPath.lean` turn a compact connected set into a finite chain
of its own points at consecutive distance below any prescribed `δ`; sending each
point to its grid site `roundSite t u` gives consecutive sites at `L^∞` distance at
most one as soon as `2δ ≤ t`, and `exists_lattice_walk_of_chain` inserts the
intermediate site of a diagonal step, at the cost of one more mesh in the distance
to the set.  The grid site is within `t` of the point it rounds
(`dist_gridPt_roundSite_le`), so every vertex of the walk is within `2δ` of the set.
-/

open MeasureTheory Set
namespace Sandpile.Support
open Sandpile.Continuum

/-- The nearest site of the lattice of mesh `t` to a continuum point `u`: each coordinate of
`u / t` rounded to the nearest integer. -/
noncomputable def roundSite (t : ℝ) (u : Sandpile.Continuum.Space 2) : Site 2 :=
  fun i => round (u i / t)

/-- Each coordinate of the grid point `t * roundSite t u` is within `t / 2` of the
corresponding coordinate of `u`: the standard rounding-error bound `|x - round x| ≤ 1/2`,
rescaled by `t`. -/
theorem abs_sub_roundSite_le {t : ℝ} (ht : 0 < t) (u : Sandpile.Continuum.Space 2) (i : Fin 2) :
    |u i - t * (roundSite t u i : ℝ)| ≤ t / 2 := by
  have h1 : |u i / t - (roundSite t u i : ℝ)| ≤ 1 / 2 := abs_sub_round (u i / t)
  have h2 : t * |u i / t - (roundSite t u i : ℝ)| ≤ t * (1 / 2) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt ht)
  have h3 : t * |u i / t - (roundSite t u i : ℝ)| = |u i - t * (roundSite t u i : ℝ)| := by
    have hm : t * (u i / t - (roundSite t u i : ℝ)) = u i - t * (roundSite t u i : ℝ) := by
      field_simp
    rw [← hm, abs_mul, abs_of_pos ht]
  rw [← h3]
  linarith

/-- If `u` and `v` are within `δ`, their rounded sites' `i`-th coordinates differ by at most
`δ / t + 1`: a triangle inequality through the two rounding errors of at most `1/2` each. -/
theorem roundSite_close {t δ : ℝ} (ht : 0 < t) {u v : Sandpile.Continuum.Space 2}
    (huv : dist u v ≤ δ) (i : Fin 2) :
    |((roundSite t u i : ℤ) : ℝ) - ((roundSite t v i : ℤ) : ℝ)| ≤ δ / t + 1 := by
  have hcoord : |u i - v i| ≤ δ := by
    have h1 : |u i - v i| ≤ dist u v := by
      have h2 := PiLp.norm_apply_le (p := 2) (u - v) i
      have h3 : ‖(u - v).ofLp i‖ = |u i - v i| := by
        simp [PiLp.sub_apply, Real.norm_eq_abs]
      rw [h3] at h2
      simpa [dist_eq_norm] using h2
    linarith
  have h1 : |((roundSite t u i : ℤ) : ℝ) - u i / t| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round (u i / t)
  have h2 : |((roundSite t v i : ℤ) : ℝ) - v i / t| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round (v i / t)
  have h3 : |u i / t - v i / t| ≤ δ / t := by
    rw [div_sub_div_same, abs_div, abs_of_pos ht]
    exact div_le_div_of_nonneg_right hcoord (le_of_lt ht)
  have h4 : |((roundSite t u i : ℤ) : ℝ) - ((roundSite t v i : ℤ) : ℝ)|
      ≤ |((roundSite t u i : ℤ) : ℝ) - u i / t| + |u i / t - v i / t|
        + |v i / t - ((roundSite t v i : ℤ) : ℝ)| := by
    have ha := abs_sub_le ((roundSite t u i : ℤ) : ℝ) (u i / t) (v i / t)
    have hb := abs_sub_le ((roundSite t u i : ℤ) : ℝ) (v i / t) ((roundSite t v i : ℤ) : ℝ)
    linarith
  have h5 : |v i / t - ((roundSite t v i : ℤ) : ℝ)| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact h2
  have h6 : |((roundSite t u i : ℤ) : ℝ) - ((roundSite t v i : ℤ) : ℝ)| ≤ δ / t + 1 := by
    linarith
  exact h6

/-- Sharpens `roundSite_close` to an integer bound: once the mesh is at least twice the
proximity `δ` (`2δ ≤ t`), points within `δ` round to sites whose `i`-th coordinates differ by
at most `1`. -/
theorem natAbs_roundSite_le_one {t δ : ℝ} (ht : 0 < t) (hδt : 2 * δ ≤ t)
    {u v : Sandpile.Continuum.Space 2} (huv : dist u v ≤ δ) (i : Fin 2) :
    (roundSite t u i - roundSite t v i).natAbs ≤ 1 := by
  have h := roundSite_close ht huv i
  have hle : δ / t + 1 ≤ 3 / 2 := by
    have h2 : δ / t ≤ 1 / 2 := by
      rw [div_le_iff₀ ht]; linarith
    linarith
  have h5 : |((roundSite t u i : ℤ) : ℝ) - ((roundSite t v i : ℤ) : ℝ)| ≤ 3 / 2 := by
    linarith
  have h6 : |((roundSite t u i : ℤ) : ℝ) - ((roundSite t v i : ℤ) : ℝ)| =
      |(((roundSite t u i - roundSite t v i : ℤ)) : ℝ)| := by
    push_cast
    ring
  rw [h6] at h5
  have h7 : |(roundSite t u i - roundSite t v i : ℤ)| ≤ 1 := by
    by_contra hc
    have h8 : (2 : ℤ) ≤ |(roundSite t u i - roundSite t v i : ℤ)| := by omega
    have h9 : (2 : ℝ) ≤ |(((roundSite t u i - roundSite t v i : ℤ)) : ℝ)| := by
      exact_mod_cast h8
    linarith
  rw [abs_le] at h7
  omega

/-- The grid point of the rounded site is within `t` of the point it rounds: the per-coordinate
bound `abs_sub_roundSite_le` combined into the Euclidean norm on `Space 2`. -/
theorem dist_gridPt_roundSite_le {t : ℝ} (ht : 0 < t) (u : Sandpile.Continuum.Space 2) :
    dist (gridPt t (roundSite t u)) u ≤ t := by
  rw [dist_eq_norm]
  have hcoord : ∀ i : Fin 2, |(gridPt t (roundSite t u) - u) i| ≤ t / 2 := by
    intro i
    have h := abs_sub_roundSite_le ht u i
    have he : (gridPt t (roundSite t u) - u) i = t * (roundSite t u i : ℝ) - u i := by
      simp [gridPt, PiLp.sub_apply]
    rw [he, abs_sub_comm]
    exact h
  have hsum : ‖gridPt t (roundSite t u) - u‖ ^ 2 =
      ∑ i : Fin 2, ((gridPt t (roundSite t u) - u) i) ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2]
  have hb : ∀ i : Fin 2, ((gridPt t (roundSite t u) - u) i) ^ 2 ≤ (t / 2) ^ 2 := by
    intro i
    have h := hcoord i
    rw [sq_le_sq]
    rw [abs_of_nonneg (by linarith : 0 ≤ t / 2)]
    simpa using h
  have hfin : ∑ i : Fin 2, ((gridPt t (roundSite t u) - u) i) ^ 2 ≤ 2 * (t / 2) ^ 2 := by
    calc ∑ i : Fin 2, ((gridPt t (roundSite t u) - u) i) ^ 2
        ≤ ∑ _i : Fin 2, (t / 2) ^ 2 := Finset.sum_le_sum (fun i _ => hb i)
      _ = 2 * (t / 2) ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
  have hsq : ‖gridPt t (roundSite t u) - u‖ ^ 2 ≤ t ^ 2 := by
    rw [hsum]
    nlinarith
  have hnn : 0 ≤ ‖gridPt t (roundSite t u) - u‖ := norm_nonneg _
  nlinarith

/-- Updating the `0`-th coordinate of a site `z` to that of a site `w` at `L^∞` distance `1`
moves the grid point by at most `2t`, via `dist_gridPt_le` and `abs_coord_sub_le_one`. -/
theorem dist_gridPt_update_le {t : ℝ} (ht : 0 ≤ t) {z w : Site 2}
    (h : (z 0 - w 0).natAbs ≤ 1) :
    dist (gridPt t (Function.update z 0 (w 0))) (gridPt t z) ≤ 2 * t := by
  refine dist_gridPt_le ht (fun i => ?_)
  have hi : ((Function.update z 0 (w 0)) i - z i).natAbs ≤ 1 := by
    by_cases hi0 : i = 0
    · subst hi0
      rw [Function.update_self]
      rw [show w 0 - z 0 = -(z 0 - w 0) by ring, Int.natAbs_neg]
      exact h
    · rw [Function.update_of_ne hi0]; simp
  exact abs_coord_sub_le_one (fun i => hi) i

/-- Two sites `z`, `w` at `L^∞` coordinate distance at most `1`, each near a point of `Γ` (within
`t` of a grid point), are joined by a nearest-neighbour lattice walk of length at most `2` whose
every vertex's grid point stays within `3t` of `Γ`; the extra mesh covers the intermediate site
inserted for a diagonal step. -/
theorem exists_lattice_walk_pair_bound {z w : Site 2} {Γ : Set (Sandpile.Continuum.Space 2)}
    {t : ℝ} (ht : 0 ≤ t)
    (hz : ∃ u ∈ Γ, dist (gridPt t z) u ≤ t) (hw : ∃ u ∈ Γ, dist (gridPt t w) u ≤ t)
    (h : ∀ i : Fin 2, (z i - w i).natAbs ≤ 1) :
    ∃ p : (lattice 2).Walk z w,
      ∀ j ≤ p.length, ∃ u ∈ Γ, dist (gridPt t (p.getVert j)) u ≤ 3 * t := by
  by_cases hzw : z = w
  · subst hzw
    refine ⟨SimpleGraph.Walk.nil, fun j hj => ?_⟩
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    obtain ⟨u, huΓ, hu⟩ := hz
    rw [SimpleGraph.Walk.getVert_zero]
    exact ⟨u, huΓ, by nlinarith [ht]⟩
  · by_cases h0 : z 0 = w 0
    · have h1 : (z 1 - w 1).natAbs = 1 := by
        rcases Nat.eq_zero_or_pos (z 1 - w 1).natAbs with hh | hh
        · exfalso; apply hzw; ext j; fin_cases j
          · exact h0
          · exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp hh)
        · exact Nat.le_antisymm (h 1) hh
      have hother : ∀ j ≠ (1 : Fin 2), z j = w j := by
        intro j hj; fin_cases j
        · exact h0
        · exact absurd rfl hj
      have hadj := adj_of_coord 1 hother h1
      refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, fun j hj => ?_⟩
      have hj1 : j ≤ 1 := by simpa using hj
      have hcases : j = 0 ∨ j = 1 := by omega
      rcases hcases with hj0 | hj1'
      · subst hj0
        obtain ⟨u, huΓ, hu⟩ := hz
        rw [SimpleGraph.Walk.getVert_zero]
        exact ⟨u, huΓ, by nlinarith [ht]⟩
      · subst hj1'
        obtain ⟨u, huΓ, hu⟩ := hw
        rw [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero]
        exact ⟨u, huΓ, by nlinarith [ht]⟩
    · have h0' : (z 0 - w 0).natAbs = 1 := by
        rcases Nat.eq_zero_or_pos (z 0 - w 0).natAbs with hh | hh
        · exfalso; apply h0; exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp hh)
        · exact Nat.le_antisymm (h 0) hh
      by_cases h1 : z 1 = w 1
      · have hother : ∀ j ≠ (0 : Fin 2), z j = w j := by
          intro j hj; fin_cases j
          · exact absurd rfl hj
          · exact h1
        have hadj := adj_of_coord 0 hother h0'
        refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, fun j hj => ?_⟩
        have hj1 : j ≤ 1 := by simpa using hj
        have hcases : j = 0 ∨ j = 1 := by omega
        rcases hcases with hj0 | hj1'
        · subst hj0
          obtain ⟨u, huΓ, hu⟩ := hz
          rw [SimpleGraph.Walk.getVert_zero]
          exact ⟨u, huΓ, by nlinarith [ht]⟩
        · subst hj1'
          obtain ⟨u, huΓ, hu⟩ := hw
          rw [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero]
          exact ⟨u, huΓ, by nlinarith [ht]⟩
      · have h1' : (z 1 - w 1).natAbs = 1 := by
          rcases Nat.eq_zero_or_pos (z 1 - w 1).natAbs with hh | hh
          · exfalso; apply h1; exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp hh)
          · exact Nat.le_antisymm (h 1) hh
        let m : Site 2 := Function.update z 0 (w 0)
        have hzm : (lattice 2).Adj z m := by
          refine adj_of_coord 0 ?_ ?_
          · intro j hj; simp only [m, Function.update_of_ne hj]
          · simp only [m, Function.update_self]; exact h0'
        have hmw : (lattice 2).Adj m w := by
          refine adj_of_coord 1 ?_ ?_
          · intro j hj
            have hj0 : j = 0 := by fin_cases j <;> simp_all
            subst hj0; simp [m]
          · have hm1 : m 1 = z 1 := by simp [m]
            rw [hm1]; exact h1'
        refine ⟨SimpleGraph.Walk.cons hzm (SimpleGraph.Walk.cons hmw SimpleGraph.Walk.nil),
          fun j hj => ?_⟩
        have hj2 : j ≤ 2 := by simpa using hj
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with hj0 | hj1'' | hj2'
        · subst hj0
          obtain ⟨u, huΓ, hu⟩ := hz
          rw [SimpleGraph.Walk.getVert_zero]
          exact ⟨u, huΓ, by nlinarith [ht]⟩
        · subst hj1''
          obtain ⟨u, huΓ, hu⟩ := hz
          rw [SimpleGraph.Walk.getVert_cons_succ]
          rw [SimpleGraph.Walk.getVert_zero]
          refine ⟨u, huΓ, ?_⟩
          have h2 : dist (gridPt t m) (gridPt t z) ≤ 2 * t :=
            dist_gridPt_update_le ht (le_of_eq h0')
          calc dist (gridPt t m) u ≤ dist (gridPt t m) (gridPt t z) + dist (gridPt t z) u :=
                dist_triangle _ _ _
            _ ≤ 2 * t + t := by linarith
            _ = 3 * t := by ring
        · subst hj2'
          obtain ⟨u, huΓ, hu⟩ := hw
          rw [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_cons_succ,
            SimpleGraph.Walk.getVert_zero]
          exact ⟨u, huΓ, by nlinarith [ht]⟩

/-- Chains `exists_lattice_walk_pair_bound` by induction on `m` along a finite sequence of sites
`v 0, …, v (m + 1)` with consecutive `L^∞` coordinate distance at most `1`, each near `Γ`, to
produce one lattice walk from `v 0` to `v (m + 1)` all of whose vertices stay within `3t`
of `Γ`. -/
theorem exists_lattice_walk_of_chain {v : ℕ → Site 2} {m : ℕ}
    {Γ : Set (Sandpile.Continuum.Space 2)} {t : ℝ} (ht : 0 ≤ t)
    (hΓ : ∀ j ≤ m + 1, ∃ u ∈ Γ, dist (gridPt t (v j)) u ≤ t)
    (hstep : ∀ j < m + 1, ∀ i : Fin 2, (v j i - v (j + 1) i).natAbs ≤ 1) :
    ∃ p : (lattice 2).Walk (v 0) (v (m + 1)),
      ∀ j ≤ p.length, ∃ u ∈ Γ, dist (gridPt t (p.getVert j)) u ≤ 3 * t := by
  induction m with
  | zero =>
      exact exists_lattice_walk_pair_bound ht (hΓ 0 (by omega)) (hΓ 1 (by omega))
        (hstep 0 (by omega))
  | succ m ih =>
      obtain ⟨p, hp⟩ := ih (fun j hj => hΓ j (by omega)) (fun j hj i => hstep j (by omega) i)
      obtain ⟨q, hq⟩ := exists_lattice_walk_pair_bound ht (hΓ (m + 1) (by omega))
        (hΓ (m + 2) (by omega)) (hstep (m + 1) (by omega))
      refine ⟨p.append q, fun j hj => ?_⟩
      rw [SimpleGraph.Walk.getVert_append]
      by_cases hjn : j < p.length
      · rw [if_pos hjn]; exact hp j (by omega)
      · rw [if_neg hjn]
        have hjl : j - p.length ≤ q.length := by
          rw [SimpleGraph.Walk.length_append] at hj
          omega
        exact hq (j - p.length) hjl

/-- Combines `reflTransGen_of_isPreconnected` and `exists_vertices_of_reflTransGen` (extracting a
finite chain of points of a compact connected `Γ` at consecutive distance below `t / 2`) with
`exists_lattice_walk_of_chain` to produce a lattice walk between the rounded sites of `x` and `y`
whose vertices' grid points stay within `2δ` of `Γ`, once `3t ≤ 2δ`. -/
theorem exists_lattice_walk_of_connected {Γ : Set (Sandpile.Continuum.Space 2)}
    (_hcomp : IsCompact Γ) (hconn : IsConnected Γ) {t δ : ℝ} (ht : 0 < t) (_hδ : 0 < δ)
    (hδt : 3 * t ≤ 2 * δ) {x y : Sandpile.Continuum.Space 2} (hx : x ∈ Γ) (hy : y ∈ Γ)
    (hround : ∀ {u v : Sandpile.Continuum.Space 2}, u ∈ Γ → v ∈ Γ → dist u v ≤ t / 2 →
      ∀ i : Fin 2, (roundSite t u i - roundSite t v i).natAbs ≤ 1)
    (hgrid : ∀ u ∈ Γ, dist (gridPt t (roundSite t u)) u ≤ t) :
    ∃ p : (lattice 2).Walk (roundSite t x) (roundSite t y),
      ∀ j ≤ p.length, ∃ u ∈ Γ, dist (gridPt t (p.getVert j)) u ≤ 2 * δ := by
  have ht2 : 0 < t / 2 := by linarith
  have hrt := reflTransGen_of_isPreconnected hconn.isPreconnected ht2 hx y hy
  obtain ⟨m, v, hv0, hvm, hvΓ, hvstep⟩ := exists_vertices_of_reflTransGen ht2 hx hrt
  have hΓ : ∀ j ≤ m + 1, ∃ u ∈ Γ, dist (gridPt t (roundSite t (v j))) u ≤ t := by
    intro j hj
    exact ⟨v j, hvΓ j hj, hgrid (v j) (hvΓ j hj)⟩
  have hstep : ∀ j < m + 1, ∀ i : Fin 2,
      (roundSite t (v j) i - roundSite t (v (j + 1)) i).natAbs ≤ 1 := by
    intro j hj i
    exact hround (hvΓ j (by omega)) (hvΓ (j + 1) (by omega)) (le_of_lt (hvstep j (by omega))) i
  obtain ⟨p, hp⟩ := exists_lattice_walk_of_chain (le_of_lt ht) hΓ hstep
  rw [← hv0, ← hvm]
  exact ⟨p, fun j hj => by
    obtain ⟨u, huΓ, hu⟩ := hp j hj
    exact ⟨u, huΓ, by linarith⟩⟩

/-- The transfer of a compact connected set of the plane to a nearest-neighbour
lattice walk, in the form the blocking argument uses it: a compact connected set
on which the continuous field is at least `l` carries a lattice walk of some mesh
whose grid points all satisfy `l - η ≤ X`. -/
theorem exists_lattice_walk_of_connected_superlevel
    {X : Sandpile.Continuum.Space 2 → ℝ} (hX : Continuous X)
    {Γ : Set (Sandpile.Continuum.Space 2)} (hcomp : IsCompact Γ) (hconn : IsConnected Γ)
    {l η : ℝ} (hη : 0 < η) (hΓ : Γ ⊆ {u | l ≤ X u})
    {x y : Sandpile.Continuum.Space 2} (hx : x ∈ Γ) (hy : y ∈ Γ) :
    ∃ (t : ℝ) (p : (lattice 2).Walk (roundSite t x) (roundSite t y)),
      0 < t ∧ ∀ j ≤ p.length, l - η ≤ X (gridPt t (p.getVert j)) := by
  have hGopen : IsOpen {u : Sandpile.Continuum.Space 2 | l - η < X u} :=
    isOpen_lt continuous_const hX
  have hΓG : Γ ⊆ {u : Sandpile.Continuum.Space 2 | l - η < X u} := by
    intro u hu
    have hlu : l ≤ X u := hΓ hu
    show l - η < X u
    linarith
  obtain ⟨δ, hδ, hδsub⟩ := IsCompact.exists_thickening_subset_open hcomp hGopen hΓG
  have ht : (0 : ℝ) < δ / 8 := by linarith
  obtain ⟨p, hp⟩ := exists_lattice_walk_of_connected hcomp hconn ht (by linarith)
    (by linarith : 3 * (δ / 8) ≤ 2 * (δ / 4)) hx hy
    (fun {u v} _ _ huv i => natAbs_roundSite_le_one ht (by linarith) huv i)
    (fun u _ => dist_gridPt_roundSite_le ht u)
  refine ⟨δ / 8, p, ht, fun j hj => ?_⟩
  obtain ⟨u, huΓ, hdu⟩ := hp j hj
  have hmem : gridPt (δ / 8) (p.getVert j) ∈ Metric.thickening δ Γ :=
    Metric.mem_thickening_iff.mpr ⟨u, huΓ, by linarith⟩
  exact le_of_lt (hδsub hmem)


/-- The transfer of a positive crossing to a lattice walk: a compact connected
set on which the continuous field is positive, joining two points of a
rectangle, carries a nearest-neighbour lattice walk of some mesh whose grid
points all satisfy `-η ≤ X`. -/
theorem exists_lattice_walk_of_crosses {X : Sandpile.Continuum.Space 2 → ℝ}
    (hX : Continuous X)
    {Γ : Set (Sandpile.Continuum.Space 2)} (hΓc : IsCompact Γ) (hΓn : IsConnected Γ)
    (hΓ : Γ ⊆ {u | 0 < X u}) {η : ℝ} (hη : 0 < η)
    {x y : Sandpile.Continuum.Space 2} (hx : x ∈ Γ) (hy : y ∈ Γ) :
    ∃ (t : ℝ) (p : (lattice 2).Walk (roundSite t x) (roundSite t y)),
      0 < t ∧ ∀ j ≤ p.length, -η ≤ X (gridPt t (p.getVert j)) := by
  simpa using Sandpile.Support.exists_lattice_walk_of_connected_superlevel hX hΓc hΓn hη
    (fun u hu => show (0:ℝ) ≤ X u from le_of_lt (hΓ hu)) hx hy

/-- The transfer of a nonpositive crossing to a lattice walk: a compact connected
set on which the continuous field is nonpositive, joining two points of a
rectangle, carries a nearest-neighbour lattice walk of some mesh whose grid
points all satisfy `X ≤ η`. -/
theorem exists_lattice_walk_of_crosses_nonpos {X : Sandpile.Continuum.Space 2 → ℝ}
    (hX : Continuous X)
    {Γ : Set (Sandpile.Continuum.Space 2)} (hΓc : IsCompact Γ) (hΓn : IsConnected Γ)
    (hΓ : Γ ⊆ {u | X u ≤ 0}) {η : ℝ} (hη : 0 < η)
    {x y : Sandpile.Continuum.Space 2} (hx : x ∈ Γ) (hy : y ∈ Γ) :
    ∃ (t : ℝ) (p : (lattice 2).Walk (roundSite t x) (roundSite t y)),
      0 < t ∧ ∀ j ≤ p.length, X (gridPt t (p.getVert j)) ≤ η := by
  obtain ⟨t, p, ht, hp⟩ :=
    Sandpile.Support.exists_lattice_walk_of_connected_superlevel (X := fun u => -X u) (hX.neg)
      hΓc hΓn hη (fun u hu => show (0:ℝ) ≤ -X u from neg_nonneg.mpr (hΓ hu)) hx hy
  refine ⟨t, p, ht, fun j hj => ?_⟩
  have h : -η ≤ -X (gridPt t (p.getVert j)) := by
    simpa using hp j hj
  exact neg_le_neg_iff.mp h


/-- The arm gives a nearest-neighbour left-right lattice walk of the rectangle:
a compact connected set on which the field is positive, joining the left side of
a lattice rectangle to its right side, carries such a walk whose grid points all
satisfy `-η ≤ X`. -/
theorem exists_leftRight_walk_of_arm {X : Sandpile.Continuum.Space 2 → ℝ}
    (hX : Continuous X) {Γ : Set (Sandpile.Continuum.Space 2)}
    (hΓc : IsCompact Γ) (hΓn : IsConnected Γ) (hΓ : Γ ⊆ {u | 0 < X u})
    {η : ℝ} (hη : 0 < η) {w : ℕ}
    {x y : Sandpile.Continuum.Space 2} (hx : x ∈ Γ) (hy : y ∈ Γ)
    (_hxL : x 0 = -(w : ℝ)) (_hyR : y 0 = (w : ℝ)) :
    ∃ (t : ℝ) (p : (lattice 2).Walk (roundSite t x) (roundSite t y)),
      0 < t ∧ ∀ j ≤ p.length, -η ≤ X (gridPt t (p.getVert j)) :=
  Sandpile.Support.exists_lattice_walk_of_crosses hX hΓc hΓn hΓ hη hx hy


/-- The blocking of the arm by the circuit, in the sign the arm bound uses: a
left-right nearest-neighbour lattice walk of a lattice rectangle on which the
field is at least `-η` cannot coexist with a bottom-top star walk of the same
rectangle on which the field is at most `l'`, when `l' < -η`. -/
theorem arm_walk_blocks_circuit {X : Sandpile.Continuum.Space 2 → ℝ}
    {t η l' : ℝ} (hlt : l' < -η) {w h : ℕ}
    {a b : Sandpile.planeRectangle w h}
    (p : (Sandpile.rectangleGraph (Sandpile.planeRectangle w h)).Walk a b)
    (ha : a ∈ Sandpile.rectangleLeft (Sandpile.planeRectangle w h))
    (hb : b ∈ Sandpile.rectangleRight (Sandpile.planeRectangle w h))
    (hp : ∀ z ∈ p.support, -η ≤ X (gridPt t (z : Site 2)))
    {c d : {x : Site 2 // x ∈ ((Sandpile.planeRectangle w h : Finset (Site 2)) : Set (Site 2))}}
    (q : ((Sandpile.starLatticeGraph 2).induce
      ((Sandpile.planeRectangle w h : Finset (Site 2)) : Set (Site 2))).Walk c d)
    (hc : (c : Site 2) 1 = 0) (hd : (d : Site 2) 1 = (h : ℤ))
    (hq : ∀ z ∈ q.support, X (gridPt t (z : Site 2)) ≤ l') :
    False :=
  Sandpile.Support.no_lattice_walk_of_levels hlt p ha hb hp q hc hd hq

end Sandpile.Support
