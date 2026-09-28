import Sandpile.Support.PercolationEvents

/-!
# The plane embedding into the `d`-dimensional lattice

The coordinate plane of the dimension-two and dimension-three critical
level-set theorem (`sandpile.tex:2560-2575`): the embedding `ℤ² → ℤ^d` sending
`(z₀, z₁)` to the site with those first two coordinates and all remaining
coordinates zero.  Its image is `ℤ²` when `d = 2` and the slab `ℤ² × {0}` when
`d = 3`.  It lives here rather than in the frozen file of the theorem so that
the support chain of that theorem can name it without importing the theorem's
own file. The embedding `planeSite` is shown injective for `d ≥ 2`
(`planeSite_injective`), additive (`planeSite_add`), compatible with the standard basis vectors
(`planeSite_add_unit`), and a graph homomorphism of the nearest-neighbour lattices
(`planeSiteHom`, from `planeSite_adj`); the last fact is used in `hasInfiniteComponent_planeSite`
to transport an infinite nearest-neighbour component of the embedded plane to one of the
ambient `d`-dimensional lattice.
-/

namespace Sandpile

/-- The embedding of the plane into the lattice, `(z₀, z₁) ↦ (z₀, z₁, 0, …, 0)`.
Its image is `ℤ²` when `d = 2` and the slab `ℤ² × {0}` when `d = 3`. -/
def planeSite {d : ℕ} (z : Sandpile.Site 2) : Sandpile.Site d :=
  fun i => if h : (i : ℕ) < 2 then z ⟨(i : ℕ), h⟩ else 0

/-- The plane embedding `planeSite` is injective for `d ≥ 2`: `z` is recovered from
`planeSite z` by reading off its first two coordinates, which is exactly `z`. -/
lemma planeSite_injective {d : ℕ} (hd : 2 ≤ d) : Function.Injective (planeSite (d := d)) := by
  intro z w h
  funext i
  have hi : (i : ℕ) < 2 := i.isLt
  have hh := congrFun h (⟨(i : ℕ), by omega⟩ : Fin d)
  simp only [planeSite, hi, dif_pos] at hh
  simpa using hh

/-- On a coordinate `i < 2`, the plane embedding just copies the corresponding coordinate of
`z`, unfolding the `dif_pos` branch of `planeSite`. -/
lemma planeSite_apply_lt {d : ℕ} (z : Site 2) (i : Fin d) (hi : (i : ℕ) < 2) :
    planeSite (d := d) z i = z ⟨(i : ℕ), hi⟩ := by
  simp [planeSite, hi]

/-- On a coordinate `i ≥ 2`, the plane embedding pads with zero, unfolding the `dif_neg` branch
of `planeSite`. -/
lemma planeSite_apply_ge {d : ℕ} (z : Site 2) (i : Fin d) (hi : ¬ (i : ℕ) < 2) :
    planeSite (d := d) z i = 0 := by
  simp [planeSite, hi]

/-- The plane embedding is additive. -/
lemma planeSite_add {d : ℕ} (a b : Site 2) :
    planeSite (d := d) (a + b) = planeSite (d := d) a + planeSite (d := d) b := by
  funext i
  by_cases hi : (i : ℕ) < 2
  · rw [planeSite_apply_lt _ _ hi]
    simp only [Pi.add_apply, planeSite_apply_lt _ _ hi]
  · rw [planeSite_apply_ge _ _ hi]
    simp only [Pi.add_apply, planeSite_apply_ge _ _ hi]
    ring

/-- The plane embedding sends translation by a standard basis vector `unit i` of `ℤ²` to
translation by the corresponding basis vector of `ℤ^d`, matched up by `i ↦ ⟨i, _⟩ : Fin d`. -/
lemma planeSite_add_unit {d : ℕ} (hd : 2 ≤ d) (z : Site 2) (i : Fin 2) :
    planeSite (d := d) (z + unit i) =
      planeSite (d := d) z + unit (⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin d) := by
  funext j
  by_cases hj : (j : ℕ) < 2
  · rw [planeSite_apply_lt _ _ hj]
    simp only [Pi.add_apply, planeSite_apply_lt z j hj, unit, Pi.single_apply]
    congr 1
    by_cases hji : (j : ℕ) = (i : ℕ)
    · rw [if_pos, if_pos] <;> simp [Fin.ext_iff, hji]
    · rw [if_neg, if_neg] <;> simp [Fin.ext_iff, hji]
  · rw [planeSite_apply_ge _ _ hj]
    simp only [Pi.add_apply, planeSite_apply_ge z j hj, unit, Pi.single_apply]
    rw [if_neg]
    · simp
    · simp only [Fin.ext_iff]
      have := i.isLt
      omega

/-- Nearest neighbours of the plane are nearest neighbours of `ℤ^d`. -/
lemma planeSite_adj {d : ℕ} (hd : 2 ≤ d) {z w : Site 2} (h : (lattice 2).Adj z w) :
    (lattice d).Adj (planeSite (d := d) z) (planeSite (d := d) w) := by
  obtain ⟨i, hi | hi⟩ := h
  · exact ⟨⟨(i : ℕ), by have := i.isLt; omega⟩,
      Or.inl (by rw [hi, planeSite_add_unit hd])⟩
  · exact ⟨⟨(i : ℕ), by have := i.isLt; omega⟩,
      Or.inr (by rw [hi, planeSite_add_unit hd])⟩

/-- The plane embedding as a graph homomorphism of nearest-neighbour lattices. -/
def planeSiteHom {d : ℕ} (hd : 2 ≤ d) : lattice 2 →g lattice d where
  toFun := planeSite
  map_rel' := planeSite_adj hd

/-- An infinite nearest-neighbour component inside the coordinate plane is an
infinite nearest-neighbour component of the ambient lattice. -/
lemma hasInfiniteComponent_planeSite {d : ℕ} (hd : 2 ≤ d) {T : Set (Site d)}
    (h : LatticeProb.HasInfiniteComponent {z : Site 2 | planeSite (d := d) z ∈ T}) :
    LatticeProb.HasInfiniteComponent T := by
  obtain ⟨x, hx, hxi⟩ := h
  refine ⟨planeSite x, hx, ?_⟩
  have hsub : planeSite (d := d) ''
      (LatticeProb.componentIn {z : Site 2 | planeSite (d := d) z ∈ T} x)
      ⊆ LatticeProb.componentIn T (planeSite x) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨p, hp⟩ := (mem_componentIn_iff_walk _ x y).mp hy
    have hgoal : planeSiteHom hd y ∈ LatticeProb.componentIn T (planeSiteHom hd x) := by
      refine (mem_componentIn_iff_walk T _ _).mpr ⟨p.map (planeSiteHom hd), ?_⟩
      intro z hz
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
      exact hp u hu
    exact hgoal
  exact Set.Infinite.mono hsub (hxi.image (planeSite_injective hd).injOn)

end Sandpile
