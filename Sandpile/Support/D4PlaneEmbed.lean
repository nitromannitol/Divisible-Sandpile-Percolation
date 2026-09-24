/-
The coordinate plane `Π = ℤ² × {0}² ⊂ ℤ⁴` of `eq:d4-coordinate-plane`
(`sandpile.tex:3432-3434`), presented as an embedding of `ℤ²`, together with
the transfer of an infinite nearest-neighbour component of the plane to one of
the ambient lattice.
-/
import Sandpile.Support.PercolationEvents

namespace Sandpile

/-- The coordinate plane `Π = ℤ² × {0}² ⊂ ℤ⁴` of `eq:d4-coordinate-plane`,
presented as the embedding of `ℤ²` that sends `(z₀, z₁)` to `(z₀, z₁, 0, 0)`. -/
def planeEmbed (z : Sandpile.Site 2) : Sandpile.Site 4 :=
  fun i => if h : (i : ℕ) < 2 then z ⟨(i : ℕ), h⟩ else 0

lemma planeEmbed_apply_lt (z : Site 2) (i : Fin 4) (hi : (i : ℕ) < 2) :
    planeEmbed z i = z ⟨(i : ℕ), hi⟩ := by
  simp [planeEmbed, hi]

lemma planeEmbed_apply_ge (z : Site 2) (i : Fin 4) (hi : ¬ (i : ℕ) < 2) :
    planeEmbed z i = 0 := by
  simp [planeEmbed, hi]

lemma planeEmbed_zero (v : Site 2) : planeEmbed v 0 = v 0 := rfl

lemma planeEmbed_one (v : Site 2) : planeEmbed v 1 = v 1 := rfl

lemma planeEmbed_two (v : Site 2) : planeEmbed v 2 = 0 := rfl

lemma planeEmbed_three (v : Site 2) : planeEmbed v 3 = 0 := rfl

lemma planeEmbed_injective : Function.Injective planeEmbed := by
  intro z w h
  funext i
  have hi : (i : ℕ) < 2 := i.isLt
  have hh := congrFun h (⟨(i : ℕ), by omega⟩ : Fin 4)
  simp only [planeEmbed, hi, dif_pos] at hh
  simpa using hh

lemma planeEmbed_add_unit (z : Site 2) (i : Fin 2) :
    planeEmbed (z + unit i) =
      planeEmbed z + unit (⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin 4) := by
  funext j
  by_cases hj : (j : ℕ) < 2
  · rw [planeEmbed_apply_lt _ _ hj]
    simp only [Pi.add_apply, planeEmbed_apply_lt z j hj, unit, Pi.single_apply]
    congr 1
    by_cases hji : (j : ℕ) = (i : ℕ)
    · rw [if_pos, if_pos] <;> simp [Fin.ext_iff, hji]
    · rw [if_neg, if_neg] <;> simp [Fin.ext_iff, hji]
  · rw [planeEmbed_apply_ge _ _ hj]
    simp only [Pi.add_apply, planeEmbed_apply_ge z j hj, unit, Pi.single_apply]
    rw [if_neg]
    · simp
    · simp only [Fin.ext_iff]
      have := i.isLt
      omega

/-- Nearest neighbours of the plane are nearest neighbours of `ℤ⁴`. -/
lemma planeEmbed_adj {z w : Site 2} (h : (lattice 2).Adj z w) :
    (lattice 4).Adj (planeEmbed z) (planeEmbed w) := by
  obtain ⟨i, hi | hi⟩ := h
  · exact ⟨⟨(i : ℕ), by have := i.isLt; omega⟩, Or.inl (by rw [hi, planeEmbed_add_unit])⟩
  · exact ⟨⟨(i : ℕ), by have := i.isLt; omega⟩, Or.inr (by rw [hi, planeEmbed_add_unit])⟩

/-- The plane embedding as a graph homomorphism of nearest-neighbour lattices. -/
def planeEmbedHom : lattice 2 →g lattice 4 where
  toFun := planeEmbed
  map_rel' := planeEmbed_adj

/-- An infinite nearest-neighbour component inside the coordinate plane is an
infinite nearest-neighbour component of the ambient lattice. -/
lemma hasInfiniteComponent_planeEmbed {T : Set (Site 4)}
    (h : HasInfiniteComponent {z : Site 2 | planeEmbed z ∈ T}) :
    HasInfiniteComponent T := by
  obtain ⟨x, hx, hxi⟩ := h
  refine ⟨planeEmbed x, hx, ?_⟩
  have hsub : planeEmbed '' (LatticeProb.componentIn {z : Site 2 | planeEmbed z ∈ T} x)
      ⊆ LatticeProb.componentIn T (planeEmbed x) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨p, hp⟩ := (mem_componentIn_iff_walk _ x y).mp hy
    have hgoal : planeEmbedHom y ∈ LatticeProb.componentIn T (planeEmbedHom x) := by
      refine (mem_componentIn_iff_walk T _ _).mpr ⟨p.map planeEmbedHom, ?_⟩
      intro z hz
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
      exact hp u hu
    exact hgoal
  exact Set.Infinite.mono hsub (hxi.image planeEmbed_injective.injOn)

end Sandpile
