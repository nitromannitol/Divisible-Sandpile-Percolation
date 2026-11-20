import Sandpile.External.RSW.WiredConnection
import Sandpile.External.RSW.ArmBridge
import Sandpile.External.RSW.BondWalk
import Sandpile.External.RSW.FirstRectangleExit

/-!
# Arms from wired boundary crossings

A crossing between two added boundary rows yields an arm when all open entrance
edges meet the targets and the original bonds are preserved in the arm rectangle.
-/

open Percolation.Literature

namespace Sandpile.External.RSW

/-- A wired vertical crossing contains an arm with the original bond states. -/
theorem kstArmEvent_of_wired_crossing (m : ℕ) (hm : 0 < m)
    (ω η : Sym2 (Site 2) → Bool)
    (hupper : ∀ (x y : centeredPlaneRectangle (m + m / 64) (m + 1)),
      (x : Site 2) 1 = (m : ℤ) + 1 → (y : Site 2) 1 ≠ (m : ℤ) + 1 →
      (rectangleGraph (centeredPlaneRectangle (m + m / 64) (m + 1))).Adj x y →
      η s((x : Site 2), (y : Site 2)) = true →
      -((m / 64 : ℕ) : ℤ) ≤ (y : Site 2) 0 ∧ (y : Site 2) 0 ≤ m / 64)
    (hlower : ∀ (x y : centeredPlaneRectangle (m + m / 64) (m + 1)),
      (y : Site 2) 1 = -((m : ℤ) + 1) → (x : Site 2) 1 ≠ -((m : ℤ) + 1) →
      (rectangleGraph (centeredPlaneRectangle (m + m / 64) (m + 1))).Adj x y →
      η s((x : Site 2), (y : Site 2)) = true →
      -((m / 64 : ℕ) : ℤ) ≤ (x : Site 2) 0 ∧ (x : Site 2) 0 ≤ m / 64)
    (hag : ∀ e : Sym2 (centeredPlaneRectangle (m + m / 64) (m + 1)),
      (∀ z ∈ e, (z : Site 2) ∈ centeredPlaneRectangle (m + m / 64) m) →
      η (Sym2.map Subtype.val e) = true → ω (Sym2.map Subtype.val e) = true)
    (hcross : ∃ (a b : centeredPlaneRectangle (m + m / 64) (m + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (m + m / 64) (m + 1))).Walk a b),
      (a : Site 2) 1 = (m : ℤ) + 1 ∧ (b : Site 2) 1 = -((m : ℤ) + 1) ∧
      IsBondOpenWalk η p) : ω ∈ kstArmEvent m := by
  classical
  let S := centeredPlaneRectangle (m + m / 64) (m + 1)
  let R := centeredPlaneRectangle (m + m / 64) m
  let A : S → Prop := fun z => (z : Site 2) 1 = (m : ℤ) + 1
  let B : S → Prop := fun z => (z : Site 2) 1 = -((m : ℤ) + 1)
  let C : S → Prop := fun z => (z : Site 2) ∈ R
  let U : S → Prop := fun z => (z : Site 2) 1 = m ∧
    -((m / 64 : ℕ) : ℤ) ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ m / 64
  let W : S → Prop := fun z => (z : Site 2) 1 = -(m : ℤ) ∧
    -((m / 64 : ℕ) : ℤ) ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ m / 64
  let E : Set (Sym2 S) := {e | η (Sym2.map Subtype.val e) = true}
  have hdiff {x y : S} (h : (rectangleGraph S).Adj x y) :
      (x : Site 2) 1 ≤ (y : Site 2) 1 + 1 ∧
      (y : Site 2) 1 ≤ (x : Site 2) 1 + 1 := by
    change (lattice 2).Adj x y at h
    rw [lattice_eq_zdGraph] at h
    exact (zdGraph_adj_apply_le h 1).symm
  have hdis : ∀ z, A z → ¬ B z := by
    intro z hz hz'
    dsimp [A, B] at *
    omega
  have hsep : ∀ x y, A x → B y → ¬ (rectangleGraph S).Adj x y := by
    intro x y hx hy hxy
    have hh := hdiff hxy
    dsimp [A, B] at *
    omega
  have hinner : ∀ z, ¬ A z → ¬ B z → C z := by
    intro z ha hb
    have hz := (mem_centeredPlaneRectangle _ _ (z : Site 2)).mp z.property
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    dsimp [A, B] at ha hb
    push_cast at hz
    exact ⟨hz.1, hz.2.1, by omega, by omega⟩
  have hu : ∀ x y, A x → ¬ A y → (rectangleGraph S).Adj x y → s(x, y) ∈ E → U y := by
    intro x y hx hy hxy he
    have hh := hdiff hxy
    have hz := (mem_centeredPlaneRectangle _ _ (y : Site 2)).mp y.property
    have ht := hupper x y hx hy hxy he
    dsimp [A] at hx hy
    dsimp [U]
    push_cast at hz
    exact ⟨by omega, ht⟩
  have hw : ∀ x y, B y → ¬ B x → (rectangleGraph S).Adj x y → s(x, y) ∈ E → W x := by
    intro x y hy hx hxy he
    have hh := hdiff hxy
    have hz := (mem_centeredPlaneRectangle _ _ (x : Site 2)).mp x.property
    have ht := hlower x y hy hx hxy he
    dsimp [B] at hx hy
    dsimp [W]
    push_cast at hz
    exact ⟨by omega, ht⟩
  obtain ⟨a, b, p, ha, hb, hp⟩ := hcross
  have hp' : ∀ e ∈ p.edges, e ∈ E := by
    intro e he
    exact (isBondOpenWalk_iff_local_edges η p).mp hp e he
  obtain ⟨x, y, q, hx, hy, hqC, hqE⟩ :=
    exists_interior_path_between_boundaries A B C U W E hdis hsep hinner hu hw p ha hb hp'
  let f : rectangleGraph S →g lattice 2 :=
    (SimpleGraph.Embedding.induce (S : Set (Site 2))).toHom
  let P := q.map f
  have hP : ∀ z ∈ P.support, z ∈ (R : Set (Site 2)) := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact hqC z' hz'
  let q' := P.induce (R : Set (Site 2)) hP
  refine ⟨⟨x, hP _ P.start_mem_support⟩, ⟨y, hP _ P.end_mem_support⟩, q', hx, hy, ?_⟩
  apply (isBondOpenWalk_iff_edges ω q').mpr
  intro e he
  rw [SimpleGraph.Walk.map_induce] at he
  change e ∈ (q.map f).edges at he
  rw [SimpleGraph.Walk.edges_map] at he
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  apply hag e' ?_ (hqE e' he')
  intro z hz
  induction e' using Sym2.ind with
  | _ z₁ z₂ =>
    simp only [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact hqC z (q.fst_mem_support_of_mem_edges he')
    · exact hqC z (q.snd_mem_support_of_mem_edges he')

end Sandpile.External.RSW
