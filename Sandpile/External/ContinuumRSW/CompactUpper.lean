import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.UpperLower.Closure

/-!
# Finite-coordinate approximations of compact upper sets

A compact set of configurations generates an upper set that is the intersection
of its finite-coordinate upper approximations. This is useful for extending
finite-dimensional positive association to increasing events.
-/

open Set

namespace Sandpile.External.ContinuumRSW

variable {ι β : Type*} [Preorder β]

/-- Configurations that dominate a point of `K` on the coordinates in `s`. -/
def finiteUpperApprox (K : Set (ι → β)) (s : Finset ι) : Set (ι → β) :=
  {x | ∃ y ∈ K, ∀ i ∈ s, y i ≤ x i}

/-- A finite-coordinate upper approximation is increasing. -/
theorem isUpperSet_finiteUpperApprox (K : Set (ι → β)) (s : Finset ι) :
    IsUpperSet (finiteUpperApprox K s) := by
  rintro x z hxz ⟨y, hy, h⟩
  exact ⟨y, hy, fun i hi => (h i hi).trans (hxz i)⟩

/-- Each approximation depends only on the selected coordinates. -/
theorem mem_finiteUpperApprox_congr (K : Set (ι → β)) (s : Finset ι)
    {x z : ι → β} (h : ∀ i ∈ s, x i = z i) :
    x ∈ finiteUpperApprox K s ↔ z ∈ finiteUpperApprox K s := by
  constructor <;> rintro ⟨y, hy, hyx⟩
  · exact ⟨y, hy, fun i hi => (h i hi) ▸ hyx i hi⟩
  · exact ⟨y, hy, fun i hi => (h i hi).symm ▸ hyx i hi⟩

/-- Finite-coordinate upper approximations decrease as the coordinate set grows. -/
theorem finiteUpperApprox_antitone (K : Set (ι → β)) : Antitone (finiteUpperApprox K) := by
  intro s t hst x hx
  obtain ⟨y, hy, h⟩ := hx
  exact ⟨y, hy, fun i hi => h i (hst hi)⟩

variable [TopologicalSpace β] [OrderClosedTopology β]

/-- Finite-coordinate upper approximations of a compact set are compact. -/
theorem isCompact_finiteUpperApprox [CompactSpace β] (K : Set (ι → β))
    (hK : IsCompact K) (s : Finset ι) : IsCompact (finiteUpperApprox K s) := by
  let C : Set ((ι → β) × (ι → β)) :=
    {p | ∀ i ∈ s, p.1 i ≤ p.2 i}
  have hC : IsClosed C := by
    have hrepr : C = ⋂ i, ⋂ (_ : i ∈ s), {p | p.1 i ≤ p.2 i} := by
      ext p
      simp only [C, mem_ofPred_eq, mem_iInter]
    rw [hrepr]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro _
    exact isClosed_le ((continuous_apply i).comp continuous_fst)
      ((continuous_apply i).comp continuous_snd)
  have heq : finiteUpperApprox K s = Prod.snd '' ((K ×ˢ univ) ∩ C) := by
    ext x
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨(y, x), ⟨⟨hy, mem_univ x⟩, h⟩, rfl⟩
    · rintro ⟨⟨y, z⟩, ⟨⟨hy, _⟩, h⟩, rfl⟩
      exact ⟨y, hy, h⟩
  rw [heq]
  exact ((hK.prod isCompact_univ).inter_right hC).image continuous_snd

/-- A compact set has the finite intersection property for coordinatewise domination. -/
theorem mem_upperClosure_iff_forall_finiteUpperApprox {K : Set (ι → β)} (hK : IsCompact K)
    (x : ι → β) : x ∈ upperClosure K ↔ ∀ s : Finset ι, x ∈ finiteUpperApprox K s := by
  constructor
  · rintro ⟨y, hy, hyx⟩ s
    exact ⟨y, hy, fun i _ => hyx i⟩
  · intro h
    let C : ι → Set (ι → β) := fun i => {y | y i ≤ x i}
    have hclosed : ∀ i, IsClosed (C i) := fun i =>
      isClosed_le (continuous_apply i) continuous_const
    have hfinite : ∀ s : Finset ι, (K ∩ ⋂ i ∈ s, C i).Nonempty := by
      intro s
      obtain ⟨y, hy, hys⟩ := h s
      exact ⟨y, hy, mem_iInter₂.mpr hys⟩
    obtain ⟨y, hyK, hy⟩ := hK.inter_iInter_nonempty C hclosed hfinite
    exact ⟨y, hyK, fun i => mem_iInter.mp hy i⟩

end Sandpile.External.ContinuumRSW
