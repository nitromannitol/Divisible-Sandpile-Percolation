import Mathlib
import Sandpile.Support.BlockChain
import Sandpile.Support.BlockVerticalWalk

/-!
# From good blocks to an infinite fine component

Support for the block-percolation step of the dimension-four critical-level
percolation argument (`sandpile.tex`, block construction): an infinite
component of good blocks at the coarse scale forces an infinite component of
the fine superlevel set.

All results in this file are local support lemmas.
-/

set_option maxHeartbeats 1000000
open scoped NNReal
open LatticeProb
noncomputable section
namespace Sandpile

/-- An infinite set of coarse sites has an infinite subset inside one
residue class modulo three. -/
theorem infinite_residue_class (C : Set (Site 2)) (hC : C.Infinite) :
    ∃ k : ℤ × ℤ, k ∈ Set.Ico 0 3 ×ˢ Set.Ico 0 3 ∧
      (C ∩ {z : Site 2 | z 0 % 3 = k.1 ∧ z 1 % 3 = k.2}).Infinite := by
  by_contra h
  push Not at h
  have hf : ∀ k ∈ (Set.Ico 0 3 ×ˢ Set.Ico 0 3 : Set (ℤ × ℤ)),
      (C ∩ {z : Site 2 | z 0 % 3 = k.1 ∧ z 1 % 3 = k.2}).Finite := fun k hk => h k hk
  have hfin : C.Finite :=
    Set.Finite.subset
      (Set.Finite.biUnion (Set.toFinite (Set.Ico 0 3 ×ˢ Set.Ico 0 3 : Set (ℤ × ℤ))) hf) (by
      intro z hz
      simp only [Set.mem_iUnion]
      refine ⟨(z 0 % 3, z 1 % 3), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, hz, by omega,
        by omega⟩)
  exact Set.Finite.not_infinite hfin hC

/-- Distinct coarse sites in the same residue class modulo three differ
by at least three in some coordinate. -/
theorem residue_far (z z' : Site 2)
    (h0 : z 0 % 3 = z' 0 % 3) (h1 : z 1 % 3 = z' 1 % 3) (hne : z ≠ z') :
    3 ≤ |z 0 - z' 0| ∨ 3 ≤ |z 1 - z' 1| := by
  by_contra h
  push Not at h
  obtain ⟨ha, hb⟩ := abs_lt.mp h.1
  obtain ⟨hc, hd⟩ := abs_lt.mp h.2
  have e0 : z 0 = z' 0 := by omega
  have e1 : z 1 = z' 1 := by omega
  exact hne (by funext i; fin_cases i <;> simp_all)

/-- Reachability in the induced graph gives a walk in the ambient graph
whose support stays inside the set. -/
theorem walk_of_induced_reachable {d : ℕ} (S : Set (Site d)) {x y : Site d}
    (hx : x ∈ S) (hy : y ∈ S)
    (h : ((lattice d).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    ∃ p : (lattice d).Walk x y, ∀ w ∈ p.support, w ∈ S := by
  obtain ⟨p⟩ := h
  refine ⟨p.map (SimpleGraph.Hom.comap (Function.Embedding.subtype (fun x => x ∈ S)) (lattice d)),
    ?_⟩
  intro w hw
  obtain ⟨w', hw', rfl⟩ := List.mem_map.mp ((SimpleGraph.Walk.support_map
    (SimpleGraph.Hom.comap (Function.Embedding.subtype (fun x => x ∈ S)) (lattice d)) p) ▸ hw)
  exact w'.2

/-- Distinct coarse sites in one residue class modulo three anchor
disjoint blocks: the shifted rectangle points determine the coarse site. -/
theorem blockShift_injective_residue {r : ℕ} (hr : 1 ≤ r) (z z' : Site 2)
    (c c' : planeRectangle (2 * r) (2 * r))
    (h0 : z 0 % 3 = z' 0 % 3) (h1 : z 1 % 3 = z' 1 % 3)
    (h : blockShift r z (c : Site 2) = blockShift r z' (c' : Site 2)) :
    z = z' := by
  obtain hc := (mem_planeRectangle (2*r) (2*r) (c : Site 2)).mp c.property
  obtain hc' := (mem_planeRectangle (2*r) (2*r) (c' : Site 2)).mp c'.property
  have h0' : (c : Site 2) 0 + 2*r*z 0 = (c' : Site 2) 0 + 2*r*z' 0 := by
    simpa [blockShift] using congrFun h 0
  have h1' : (c : Site 2) 1 + 2*r*z 1 = (c' : Site 2) 1 + 2*r*z' 1 := by
    simpa [blockShift] using congrFun h 1
  have key : ∀ (u v a b : ℤ), 1 ≤ r → a + 2*r*u = b + 2*r*v → 0 ≤ a → a ≤ 2*r →
      0 ≤ b → b ≤ 2*r → |u - v| ≤ 1 := by
    intro u v a b hr' hEq ha ha' hb hb'
    have hring : 2*r*((u - v) - 1) = 2*r*u - 2*r*v - 2*r := by ring
    have hring2 : 2*r*((v - u) - 1) = 2*r*v - 2*r*u - 2*r := by ring
    have hm : 2*r*((u - v) - 1) = b - a - 2*r := by linarith
    have hm2 : 2*r*((v - u) - 1) = a - b - 2*r := by linarith
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have e0 : z 0 = z' 0 := by
    have habs := key (z 0) (z' 0) ((c : Site 2) 0) ((c' : Site 2) 0) hr h0'
      hc.1 hc.2.1 hc'.1 hc'.2.1
    rcases abs_le.mp habs with ⟨ha, hb⟩
    omega
  have e1 : z 1 = z' 1 := by
    have habs := key (z 1) (z' 1) ((c : Site 2) 1) ((c' : Site 2) 1) hr h1'
      hc.2.2.1 hc.2.2.2 hc'.2.2.1 hc'.2.2.2
    rcases abs_le.mp habs with ⟨ha, hb⟩
    omega
  funext i
  fin_cases i
  · show z 0 = z' 0; exact e0
  · show z 1 = z' 1; exact e1

/-- An ambient walk whose support stays in `S` gives reachability in the
induced graph on `S`. -/
theorem induced_reachable_of_walk {d : ℕ} (S : Set (Site d)) {x y : Site d}
    (p : (lattice d).Walk x y) (hp : ∀ w ∈ p.support, w ∈ S) :
    ((lattice d).induce S).Reachable ⟨x, hp x (SimpleGraph.Walk.start_mem_support p)⟩
      ⟨y, hp y (SimpleGraph.Walk.end_mem_support p)⟩ := by
  have key : ∀ (a b : Site d) (p : (lattice d).Walk a b), (∀ w ∈ p.support, w ∈ S) →
      ∃ (ha : a ∈ S) (hb : b ∈ S), ((lattice d).induce S).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro a b p
    induction p using SimpleGraph.Walk.rec with
    | nil =>
      intro hp
      exact ⟨hp _ (by simp [SimpleGraph.Walk.support]), hp _ (by simp [SimpleGraph.Walk.support]),
        ⟨SimpleGraph.Walk.nil⟩⟩
    | cons hAdj p IH =>
      intro hp
      rename_i u v w
      have hu : u ∈ S := hp u (by simp [SimpleGraph.Walk.support_cons])
      obtain ⟨hv, hw, ⟨q⟩⟩ := IH (fun z hz => hp z (by
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
        exact Or.inr hz))
      exact ⟨hu, hw, ⟨SimpleGraph.Walk.cons (SimpleGraph.induce_adj.mpr hAdj) q⟩⟩
  obtain ⟨ha, hb, q⟩ := key x y p hp
  exact q
/-- An infinite component of the good-block relation `BlockGood r F ℓ` forces an infinite
component of the fine superlevel set `{u | ℓ ≤ F u}`: the coarse component is thinned to a
residue-class-injective infinite family of coarse sites, each of which is chained by
`block_chain` to a common fine witness `ws`. -/
theorem block_component_infinite {r : ℕ} (hr : 1 ≤ r) (F : Site 2 → ℝ) (ℓ : ℝ)
    (h : HasInfiniteComponent {z : Site 2 | BlockGood r F ℓ z}) :
    HasInfiniteComponent {u : Site 2 | ℓ ≤ F u} := by
  obtain ⟨z₀, hz₀, hC⟩ := h
  obtain ⟨k, _, hC₀⟩ := infinite_residue_class _ hC
  obtain ⟨zs, hzs⟩ := hC₀.nonempty
  obtain ⟨hzsC, hzsR⟩ := (Set.mem_inter_iff _ _ _).mp hzs
  -- membership in componentIn unfolds to reachability plus set membership
  simp only [componentIn, Set.mem_setOf_eq] at hzsC
  obtain ⟨hxzs, hyzs, hreachzs⟩ := hzsC
  -- seed walk for zs
  have hgoods : BlockGood r F ℓ zs := hyzs
  have hseeds := exists_tb_walk_of_le_verticalCrossingValue
    (fun w => F (blockShift r zs w)) hgoods.2.1
  obtain ⟨as, bs, qs, has, hbs, hqs⟩ := hseeds
  set ws : Site 2 := blockShift r zs (as : Site 2) with hwsdef
  have hws : ℓ ≤ F ws := hqs _ (SimpleGraph.Walk.start_mem_support qs)
  -- the chained witness for every coarse site of the residue component
  have key : ∀ z ∈ (componentIn {z : Site 2 | BlockGood r F ℓ z} z₀ ∩
      {z : Site 2 | z 0 % 3 = k.1 ∧ z 1 % 3 = k.2}),
      ∃ c : planeRectangle (2 * r) (2 * r),
        ℓ ≤ F (blockShift r z c) ∧
        blockShift r z (c : Site 2) ∈ componentIn {u : Site 2 | ℓ ≤ F u} ws := by
    intro z hz
    obtain ⟨hzC, hzR⟩ := (Set.mem_inter_iff _ _ _).mp hz
    simp only [componentIn, Set.mem_setOf_eq] at hzC
    obtain ⟨hxz, hyz, hreachz⟩ := hzC
    -- coarse walk from zs to z inside the good-block set
    obtain ⟨Q1, hQ1⟩ :=
      walk_of_induced_reachable {z : Site 2 | BlockGood r F ℓ z} hxzs hyzs hreachzs
    obtain ⟨Q2, hQ2⟩ := walk_of_induced_reachable {z : Site 2 | BlockGood r F ℓ z} hxz hyz hreachz
    set Q := Q1.reverse.append Q2 with hQdef
    have hQgood : ∀ w ∈ Q.support, BlockGood r F ℓ w := by
      intro w hw
      rw [hQdef, SimpleGraph.Walk.support_append] at hw
      obtain hw | hw := List.mem_append.mp hw
      · rw [SimpleGraph.Walk.support_reverse] at hw
        exact hQ1 w (List.mem_reverse.mp hw)
      · exact hQ2 w (List.mem_of_mem_tail hw)
    -- seed walk for z
    have hseedz := exists_tb_walk_of_le_verticalCrossingValue
      (fun w => F (blockShift r z w)) hyz.2.1
    obtain ⟨az, bz, qz, haz, hbz, hqz⟩ := hseedz
    -- chain from the seed of zs to a witness of z
    obtain ⟨c₂, d₂, q₂, p, hp, hq₂, hc₂, hd₂⟩ :=
      block_chain hr F ℓ zs z Q hQgood as bs qs hqs has hbs
    refine ⟨c₂, hp _ (SimpleGraph.Walk.end_mem_support p), ?_⟩
    exact ⟨hws, hp _ (SimpleGraph.Walk.end_mem_support p),
      induced_reachable_of_walk {u : Site 2 | ℓ ≤ F u} p hp⟩
  choose! c hcval hcmem using key
  -- injectivity of z ↦ blockShift r z (c z) on the residue component
  classical
  set Φ : Site 2 → Site 2 := fun z =>
    if hz : z ∈ (componentIn {z : Site 2 | BlockGood r F ℓ z} z₀ ∩
      {z : Site 2 | z 0 % 3 = k.1 ∧ z 1 % 3 = k.2}) then
      blockShift r z (c z hz : Site 2) else 0 with hΦdef
  have hΦ : ∀ z (hz : z ∈ (componentIn {z : Site 2 | BlockGood r F ℓ z} z₀ ∩
      {z : Site 2 | z 0 % 3 = k.1 ∧ z 1 % 3 = k.2})),
      Φ z = blockShift r z (c z hz : Site 2) := fun z hz => dif_pos hz
  have hinj : Set.InjOn Φ (componentIn {z : Site 2 | BlockGood r F ℓ z} z₀ ∩
      {z : Site 2 | z 0 % 3 = k.1 ∧ z 1 % 3 = k.2}) := by
    intro a ha b hb heq
    rw [hΦ a ha, hΦ b hb] at heq
    obtain ⟨_, hzR⟩ := (Set.mem_inter_iff _ _ _).mp ha
    obtain ⟨_, hzR'⟩ := (Set.mem_inter_iff _ _ _).mp hb
    simp only [Set.mem_setOf_eq] at hzR hzR'
    exact blockShift_injective_residue hr a b (c a ha) (c b hb)
      (hzR.1.trans hzR'.1.symm) (hzR.2.trans hzR'.2.symm) heq
  -- the image is an infinite subset of the fine component of ws
  have himg : Φ '' (componentIn {z : Site 2 | BlockGood r F ℓ z} z₀ ∩
      {z : Site 2 | z 0 % 3 = k.1 ∧ z 1 % 3 = k.2}) ⊆
      componentIn {u : Site 2 | ℓ ≤ F u} ws := by
    intro u hu
    obtain ⟨z, hz, rfl⟩ := hu
    rw [hΦ z hz]
    exact hcmem z hz
  have hinf : (componentIn {u : Site 2 | ℓ ≤ F u} ws).Infinite :=
    Set.Infinite.mono himg (Set.Infinite.image hinj hC₀)
  exact ⟨ws, hws, hinf⟩

end Sandpile