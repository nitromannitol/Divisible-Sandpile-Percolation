import Sandpile.Frozen.DGT4LevelShiftDecoupling
import Sandpile.Support.RealBoxes
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Star-lattice walk prefixes and annular crossing witnesses

Walk prefixes and annular crossing witnesses on the star lattice. Shows that a walk leaving a
set `Q` has a first-exit prefix (`walk_prefix_exit`), relates the star-adjacency graph
`starLatticeGraph` to nearest-neighbor lattice adjacency and to the integer box distance
`boxDist`, and uses these to extract, from any star-connected set spanning from radius `R` to
beyond `2 * R`, a connected sub-piece confined to the annulus that still spans it exactly
(`exists_star_subcrossing`).
-/

namespace Sandpile

/-- Along any walk `p` from `a` to `b` with `a ∈ Q` and `b ∉ Q`, there is a prefix `q` of `p`
ending at some `v ∈ Q` adjacent to a first vertex `w ∉ Q` leaving `Q`; `q` uses only vertices
of `p` and stays entirely in `Q`. -/
lemma walk_prefix_exit {V : Type*} (G : SimpleGraph V) (Q : Set V) {a b : V}
    (p : G.Walk a b) : a ∈ Q → b ∉ Q →
    ∃ (v w : V) (q : G.Walk a v), q.support ⊆ p.support ∧
      (∀ z ∈ q.support, z ∈ Q) ∧ G.Adj v w ∧ w ∉ Q := by
  induction p with
  | nil => intro ha hb; exact (hb ha).elim
  | @cons u v w huv p ih =>
    intro hu hw
    by_cases hv : v ∈ Q
    · obtain ⟨v', w', q, hsub, hQ, hadj, hout⟩ := ih hv hw
      refine ⟨v', w', SimpleGraph.Walk.cons huv q, ?_, ?_, hadj, hout⟩
      · intro z hz
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz ⊢
        rcases hz with rfl | hz
        · exact Or.inl rfl
        · exact Or.inr (hsub hz)
      · intro z hz
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hu
        · exact hQ z hz
    · refine ⟨u, v, SimpleGraph.Walk.nil, ?_, ?_, huv, hv⟩
      · intro z hz
        have hz' : z = u := by simpa using hz
        subst z
        exact (SimpleGraph.Walk.cons huv p).start_mem_support
      · simpa using hu

/-- The star-adjacency graph on `Site d`, an abbreviation for
`Frozen.DGT4LevelShiftDecoupling.starLattice d`. -/
abbrev starLatticeGraph (d : ℕ) : SimpleGraph (Site d) :=
  Frozen.DGT4LevelShiftDecoupling.starLattice d

/-- Nearest-neighbor lattice adjacency implies star-lattice adjacency:
`lattice d ≤ starLatticeGraph d`, since a unit step changes exactly one coordinate by `± 1`,
which is a valid star step. -/
lemma lattice_le_starLatticeGraph (d : ℕ) : lattice d ≤ starLatticeGraph d := by
  intro u v huv
  refine ⟨huv.ne, ?_⟩
  obtain ⟨i, hi | hi⟩ := huv
  · rw [hi]
    intro j
    by_cases h : i = j
    · subst j
      simp [unit]
    · simp [unit, Pi.single_eq_of_ne (Ne.symm h)]
  · rw [hi]
    intro j
    by_cases h : i = j
    · subst j
      simp [unit]
    · simp [unit, Pi.single_eq_of_ne (Ne.symm h)]

/-- If `u` lies within `boxDist R` of `x` and a star-adjacent `v` lies outside, some coordinate
`i` has `(u i - x i).natAbs = R` exactly: some coordinate of `v` must already exceed `R`, and
the star step changes each coordinate by at most `1`, pinning `u`'s value there to `R`. -/
lemma exists_boundary_coord_of_star_exit {d : ℕ} (x u v : Site d) (R : ℕ)
    (hu : boxDist u x ≤ R) (hv : R < boxDist v x) (hadj : (starLatticeGraph d).Adj u v) :
    ∃ i : Fin d, (u i - x i).natAbs = R := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin d, R < (v i - x i).natAbs := by
    by_contra hn
    push Not at hn
    have hb : boxDist v x ≤ R := Finset.sup_le (fun i _ => hn i)
    omega
  have hui : (u i - x i).natAbs ≤ R :=
    (Finset.le_sup (f := fun j => (u j - x j).natAbs) (Finset.mem_univ i)).trans hu
  have hstep := hadj.2 i
  have heq : (u i - x i).natAbs = R := by omega
  exact ⟨i, heq⟩

/-- Strengthens `exists_boundary_coord_of_star_exit` to `boxDist u x = R`: the witnessed
coordinate already realizes the sup-norm distance. -/
lemma boxDist_eq_radius_of_star_exit {d : ℕ} (x u v : Site d) (R : ℕ)
    (hu : boxDist u x ≤ R) (hv : R < boxDist v x) (hadj : (starLatticeGraph d).Adj u v) :
    boxDist u x = R := by
  obtain ⟨i, hi⟩ := exists_boundary_coord_of_star_exit x u v R hu hv hadj
  apply le_antisymm hu
  rw [← hi]
  exact Finset.le_sup (f := fun j => (u j - x j).natAbs) (Finset.mem_univ i)

/-- Given a coordinate `i` with `(u i - x i).natAbs = R`, stepping `u` by `± unit i` (away
from `x`) produces a lattice-adjacent site `z` with `boxDist z x > R`. -/
lemma lattice_exit_of_boundary_coord {d : ℕ} (x u : Site d) (R : ℕ)
    (i : Fin d) (heq : (u i - x i).natAbs = R) :
    ∃ z : Site d, R < boxDist z x ∧ (lattice d).Adj z u := by
  by_cases hxu : x i ≤ u i
  · refine ⟨u + unit i, ?_, ?_⟩
    · have hlarge : R < ((u + unit i) i - x i).natAbs := by
        simp only [Pi.add_apply, unit, Pi.single_eq_same]
        omega
      exact hlarge.trans_le (Finset.le_sup (f := fun j => ((u + unit i) j - x j).natAbs)
        (Finset.mem_univ i))
    · apply SimpleGraph.Adj.symm
      exact ⟨i, Or.inl rfl⟩
  · refine ⟨u - unit i, ?_, ?_⟩
    · have hlarge : R < ((u - unit i) i - x i).natAbs := by
        simp only [Pi.sub_apply, unit, Pi.single_eq_same]
        omega
      exact hlarge.trans_le (Finset.le_sup (f := fun j => ((u - unit i) j - x j).natAbs)
        (Finset.mem_univ i))
    · apply SimpleGraph.Adj.symm
      exact ⟨i, Or.inr (by abel)⟩

/-- If `boxDist u x = R`, some coordinate of `u` realizes the defining supremum, so
`lattice_exit_of_boundary_coord` produces a lattice-adjacent site `z` with
`boxDist z x > R`. -/
lemma lattice_exit_of_boxDist_eq {d : ℕ} [NeZero d] (x u : Site d) (R : ℕ)
    (hu : boxDist u x = R) :
    ∃ z : Site d, R < boxDist z x ∧ (lattice d).Adj z u := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    Finset.univ_nonempty (fun i => (u i - x i).natAbs)
  have he : (u i - x i).natAbs = R := hi.symm.trans hu
  exact lattice_exit_of_boundary_coord x u R i he

/-- Combines `exists_boundary_coord_of_star_exit` with `lattice_exit_of_boundary_coord`: a star
step from inside `boxDist ≤ R` to outside produces a genuinely lattice-adjacent site `z` with
`boxDist z x > R`. -/
lemma star_step_exit {d : ℕ} (x u v : Site d) (R : ℕ)
    (hu : boxDist u x ≤ R) (hv : R < boxDist v x) (hadj : (starLatticeGraph d).Adj u v) :
    ∃ z : Site d, R < boxDist z x ∧ (lattice d).Adj z u := by
  obtain ⟨i, heq⟩ := exists_boundary_coord_of_star_exit x u v R hu hv hadj
  exact lattice_exit_of_boundary_coord x u R i heq

/-- `u` lies in the inner boundary of the real box `boxAt x R` iff `boxDist u x = R` exactly,
translating the real-valued inner-boundary condition (existence of an adjacent exit point)
into the integer sup-norm distance via `boxDist_eq_radius_of_star_exit` and
`lattice_exit_of_boxDist_eq`. -/
lemma innerBoundary_nat_box_iff {d : ℕ} [NeZero d] (x u : Site d) (R : ℕ) :
    u ∈ Frozen.DGT4LevelShiftDecoupling.innerBoundary
      (Frozen.DGT4LevelShiftDecoupling.boxAt x (R : ℝ)) ↔ boxDist u x = R := by
  constructor
  · rintro ⟨hu, z, hz, hzu⟩
    change (boxDist u x : ℝ) ≤ (R : ℝ) at hu
    have hu' : boxDist u x ≤ R := by exact_mod_cast hu
    have hz' : R < boxDist z x := by
      have : ¬ (boxDist z x : ℝ) ≤ (R : ℝ) := hz
      exact_mod_cast lt_of_not_ge this
    exact boxDist_eq_radius_of_star_exit x u z R hu' hz'
      (lattice_le_starLatticeGraph d hzu.symm)
  · intro hu
    obtain ⟨z, hz, hzu⟩ := lattice_exit_of_boxDist_eq x u R hu
    refine ⟨?_, z, ?_, hzu⟩
    · change (boxDist u x : ℝ) ≤ (R : ℝ)
      exact_mod_cast hu.le
    · change ¬ (boxDist z x : ℝ) ≤ (R : ℝ)
      exact not_le.mpr (by exact_mod_cast hz)

/-- Given a star-connected set `T` containing `a` (within `boxDist ≤ R` of `x`) and `b`
(beyond `boxDist 2 * R`), extracts a connected sub-piece `U ⊆ T` confined to
`boxDist ≤ 2 * R` that still reaches from radius `≤ R` out to radius exactly `2 * R`, by
truncating a connecting path with `walk_prefix_exit`. -/
lemma exists_star_subcrossing {d : ℕ} (T : Set (Site d))
    (hT : ((starLatticeGraph d).induce T).Connected) {a b : Site d} (ha : a ∈ T) (hb : b ∈ T)
    (x : Site d) (R : ℕ) (haR : boxDist a x ≤ R) (hbR : 2 * R < boxDist b x) :
    ∃ U : Set (Site d), U ⊆ T ∧ U ⊆ {z | boxDist z x ≤ 2 * R} ∧
      ((starLatticeGraph d).induce U).Connected ∧
      (∃ z ∈ U, boxDist z x ≤ R) ∧ (∃ z ∈ U, boxDist z x = 2 * R) := by
  obtain ⟨p⟩ := hT.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  let p' : (starLatticeGraph d).Walk a b :=
    p.map (SimpleGraph.Embedding.induce T).toHom
  have hpT : ∀ z ∈ p'.support, z ∈ T := by
    intro z hz
    rw [show p'.support = p.support.map (fun z : T => (z : Site d)) from
      SimpleGraph.Walk.support_map _ _] at hz
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hz
    exact y.property
  obtain ⟨v, w, q, hsub, hQ, hvw, hw⟩ :=
    walk_prefix_exit (starLatticeGraph d) {z | boxDist z x ≤ 2 * R} p'
      (by change boxDist a x ≤ 2 * R; omega)
      (by change ¬ boxDist b x ≤ 2 * R; omega)
  refine ⟨{z | z ∈ q.support}, fun z hz => hpT z (hsub hz), hQ,
    q.connected_induce_support, ⟨a, q.start_mem_support, haR⟩,
    ⟨v, q.end_mem_support, ?_⟩⟩
  exact boxDist_eq_radius_of_star_exit x v w (2 * R) (hQ v q.end_mem_support)
    (lt_of_not_ge hw) hvw

end Sandpile
