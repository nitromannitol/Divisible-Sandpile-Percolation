import Sandpile.Support.CrossFixBlocking

/-!
# Lattice approximation at every sufficiently fine mesh

The prescribed-mesh step in `sandpile.tex:2645-2660`: a compact connected
subset of an open planar set admits lattice approximations at every
sufficiently fine mesh, with a threshold independent of the endpoints.
-/

open Set

namespace Sandpile.Support
open Sandpile.Continuum

/-- A compact connected set inside an open set can be followed by a lattice
walk at every sufficiently fine prescribed mesh. -/
theorem exists_lattice_walk_in_open_of_small_mesh
    {Γ G : Set (Space 2)} (hΓc : IsCompact Γ) (hΓn : IsConnected Γ)
    (hG : IsOpen G) (hΓG : Γ ⊆ G) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      ∀ x ∈ Γ, ∀ y ∈ Γ,
        ∃ p : (lattice 2).Walk (roundSite t x) (roundSite t y),
          ∀ j ≤ p.length, gridPt t (p.getVert j) ∈ G := by
  obtain ⟨δ, hδ, hδG⟩ := hΓc.exists_thickening_subset_open hG hΓG
  refine ⟨δ / 8, by positivity, ?_⟩
  intro t ht htt x hx y hy
  obtain ⟨p, hp⟩ := exists_lattice_walk_of_connected hΓc hΓn ht
    (show 0 < δ / 4 by positivity) (show 3 * t ≤ 2 * (δ / 4) by linarith)
    hx hy
    (fun {u v} _ _ huv i => natAbs_roundSite_le_one ht (by linarith) huv i)
    (fun u _ => dist_gridPt_roundSite_le ht u)
  refine ⟨p, fun j hj => hδG ?_⟩
  obtain ⟨u, hu, hdist⟩ := hp j hj
  exact Metric.mem_thickening_iff.mpr ⟨u, hu, by linarith⟩

/-- A strict level margin is preserved at every sufficiently fine mesh,
uniformly over the endpoints of the connected set. -/
theorem exists_lattice_walk_superlevel_of_small_mesh
    {X : Space 2 → ℝ} (hX : Continuous X)
    {Γ : Set (Space 2)} (hΓc : IsCompact Γ) (hΓn : IsConnected Γ)
    {l η : ℝ} (hη : 0 < η) (hΓ : Γ ⊆ {u | l ≤ X u}) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      ∀ x ∈ Γ, ∀ y ∈ Γ,
        ∃ p : (lattice 2).Walk (roundSite t x) (roundSite t y),
          ∀ j ≤ p.length, l - η < X (gridPt t (p.getVert j)) := by
  apply exists_lattice_walk_in_open_of_small_mesh hΓc hΓn
    (isOpen_lt continuous_const hX)
  intro u hu
  have h : l ≤ X u := hΓ hu
  change l - η < X u
  linarith

end Sandpile.Support
