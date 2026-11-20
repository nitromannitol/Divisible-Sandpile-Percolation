import Sandpile.External.RSW.KSTPathRestriction
import Sandpile.External.RSW.QuasiCascadeCover

/-!
# Subpaths under restriction

KST subpaths depend on the ambient lattice walk, so restricting a path to a smaller
rectangle preserves the absence of smaller KST subpaths.
-/

open Set

namespace Sandpile.External.RSW

/-- A KST subpath transfers between two presentations of the same lattice walk. -/
theorem hasKSTSubpath_of_eq_ambient_walk {Q R : Finset (Site 2)} {a b : Site 2}
    {ha : a ∈ Q} {hb : b ∈ Q} {hc : a ∈ R} {hd : b ∈ R}
    (p : (rectangleGraph Q).Walk ⟨a, ha⟩ ⟨b, hb⟩)
    (q : (rectangleGraph R).Walk ⟨a, hc⟩ ⟨b, hd⟩) (k : ℕ)
    (heq : p.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom =
      q.map (SimpleGraph.Embedding.induce (R : Set (Site 2))).toHom)
    (hq : HasKSTSubpath k q) : HasKSTSubpath k p := by
  change ((lattice 2).induce (Q : Set (Site 2))).Walk ⟨a, ha⟩ ⟨b, hb⟩ at p
  change ((lattice 2).induce (R : Set (Site 2))).Walk ⟨a, hc⟩ ⟨b, hd⟩ at q
  obtain ⟨u, v, r, hrsub, hr⟩ := hq
  change ((lattice 2).induce (R : Set (Site 2))).Walk u v at r
  let r₀ := r.map (SimpleGraph.Embedding.induce (R : Set (Site 2))).toHom
  have heqs : p.support.map Subtype.val = q.support.map Subtype.val := by
    have hh := congrArg (fun w => w.support) heq
    exact (SimpleGraph.Walk.support_map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom p).symm.trans
      (hh.trans (SimpleGraph.Walk.support_map (SimpleGraph.Embedding.induce (R : Set (Site 2))).toHom q))
  have hrs : r₀.support = r.support.map Subtype.val := by
    change (r.map (SimpleGraph.Embedding.induce (R : Set (Site 2))).toHom).support = _
    exact SimpleGraph.Walk.support_map (SimpleGraph.Embedding.induce (R : Set (Site 2))).toHom r
  have hrQ : ∀ z ∈ r₀.support, z ∈ (Q : Set (Site 2)) := by
    intro z hz
    rw [hrs] at hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    have hxq : x ∈ q.support := hrsub.support_subset hx
    have hxp : (x : Site 2) ∈ p.support.map Subtype.val := by
      rw [heqs]
      exact List.mem_map.mpr ⟨x, hxq, rfl⟩
    obtain ⟨y, _, hy⟩ := List.mem_map.mp hxp
    rw [← hy]
    exact y.property
  let r' := r₀.induce (Q : Set (Site 2)) hrQ
  have hrmap : r'.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom = r₀ :=
    SimpleGraph.Walk.map_induce r₀ hrQ
  have hri : r'.support.map Subtype.val = r₀.support := by
    change (r₀.induce (Q : Set (Site 2)) hrQ).support.map Subtype.val = r₀.support
    rw [SimpleGraph.Walk.support_induce]
    simp only [List.attachWith_map_subtype_val]
  have hsub : r'.IsSubwalk p := by
    apply SimpleGraph.Walk.isSubwalk_iff_support_isInfix.mpr
    have hi : r₀.support <:+: p.support.map Subtype.val := by
      rw [hrs, heqs]
      exact (SimpleGraph.Walk.isSubwalk_iff_support_isInfix.mp hrsub).map Subtype.val
    rw [← hri] at hi
    obtain ⟨l, hl, he⟩ := List.infix_map_iff.mp hi
    have he' : r'.support = l := (List.map_injective_iff.mpr Subtype.val_injective) he
    simpa only [he'] using hl
  refine ⟨⟨u, hrQ _ r₀.start_mem_support⟩, ⟨v, hrQ _ r₀.end_mem_support⟩, r', hsub, ?_⟩
  have hrpath : r₀.IsPath := hr.1.map Subtype.val_injective
  have hr'path : r'.IsPath := by
    have h : (r'.map (SimpleGraph.Embedding.induce (Q : Set (Site 2))).toHom).IsPath := by
      rw [hrmap]
      exact hrpath
    exact h.of_map
  refine ⟨hr'path, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
    hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, ?_⟩
  intro z hz
  have hz' : (z : Site 2) ∈ r₀.support := by
    rw [← hri]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  rw [hrs] at hz'
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hz'
  rw [← he]
  exact hr.2.2.2.2.2.2.2 x hx

/-- Restriction preserves the absence of KST subpaths at a smaller scale. -/
theorem IsKSTPath.exists_restrict_without_subpath {Q : Finset (Site 2)} {a b : Q}
    {p : (rectangleGraph Q).Walk a b} {m k : ℕ} (hp : IsKSTPath m p)
    {ω : Sym2 (Site 2) → Bool} (hopen : IsBondOpenWalk ω p)
    (hbad : ¬ HasKSTSubpath k p) :
    ∃ (ha : (a : Site 2) ∈ centeredPlaneRectangle (m + m / 12) m)
      (hb : (b : Site 2) ∈ centeredPlaneRectangle (m + m / 12) m)
      (q : (rectangleGraph (centeredPlaneRectangle (m + m / 12) m)).Walk ⟨a, ha⟩ ⟨b, hb⟩),
      IsKSTPath m q ∧ IsBondOpenWalk ω q ∧ ¬ HasKSTSubpath k q := by
  obtain ⟨ha, hb, q, hq, hqo, heq⟩ := hp.exists_restrict hopen
  refine ⟨ha, hb, q, hq, hqo, ?_⟩
  intro hsub
  exact hbad (hasKSTSubpath_of_eq_ambient_walk p q k heq.symm hsub)

end Sandpile.External.RSW
