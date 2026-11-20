import Sandpile.External.RSW.WiredConnection
import Sandpile.External.RSW.QuasiCrossing
import Sandpile.External.RSW.BondWalk
import Sandpile.External.RSW.FirstRectangleExit

/-!
# Scale paths from wired boundary crossings

A crossing of a rectangle with two added boundary rows contains a KST path
when the crossing can enter the interior only through the scale targets.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- A wired vertical crossing contains an open KST path in the original strip. -/
theorem exists_kstPath_of_wired_crossing (k : ℕ) (hk : 0 < k)
    (ω η : Sym2 (Site 2) → Bool)
    (hupper : ∀ (x y : centeredPlaneRectangle (k + k / 12) (k + 1)),
      (x : Site 2) 1 = (k : ℤ) + 1 → (y : Site 2) 1 ≠ (k : ℤ) + 1 →
      (rectangleGraph (centeredPlaneRectangle (k + k / 12) (k + 1))).Adj x y →
      η s((x : Site 2), (y : Site 2)) = true →
      -((k / 12 : ℕ) : ℤ) ≤ (y : Site 2) 0 ∧ (y : Site 2) 0 ≤ k / 12)
    (hlower : ∀ (x y : centeredPlaneRectangle (k + k / 12) (k + 1)),
      (y : Site 2) 1 = -((k : ℤ) + 1) → (x : Site 2) 1 ≠ -((k : ℤ) + 1) →
      (rectangleGraph (centeredPlaneRectangle (k + k / 12) (k + 1))).Adj x y →
      η s((x : Site 2), (y : Site 2)) = true →
      -((k / 12 : ℕ) : ℤ) ≤ (x : Site 2) 0 ∧ (x : Site 2) 0 ≤ k / 12)
    (hag : ∀ edge : Sym2 (centeredPlaneRectangle (k + k / 12) (k + 1)),
      (∀ z ∈ edge, (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k) →
      η (Sym2.map Subtype.val edge) = true → ω (Sym2.map Subtype.val edge) = true)
    (hcross : ∃ (a b : centeredPlaneRectangle (k + k / 12) (k + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (k + k / 12) (k + 1))).Walk a b),
      (a : Site 2) 1 = (k : ℤ) + 1 ∧ (b : Site 2) 1 = -((k : ℤ) + 1) ∧
      IsBondOpenWalk η p) :
    ∃ (a b : centeredPlaneRectangle (k + k / 12) (k + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (k + k / 12) (k + 1))).Walk a b),
      IsKSTPath k p ∧ IsBondOpenWalk ω p := by
  classical
  let S := centeredPlaneRectangle (k + k / 12) (k + 1)
  let R := centeredPlaneRectangle (k + k / 12) k
  let A : S → Prop := fun z => (z : Site 2) 1 = (k : ℤ) + 1
  let B : S → Prop := fun z => (z : Site 2) 1 = -((k : ℤ) + 1)
  let C : S → Prop := fun z => (z : Site 2) ∈ R
  let U : S → Prop := fun z => (z : Site 2) 1 = k ∧
    -((k / 12 : ℕ) : ℤ) ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ k / 12
  let W : S → Prop := fun z => (z : Site 2) 1 = -(k : ℤ) ∧
    -((k / 12 : ℕ) : ℤ) ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ k / 12
  let E : Set (Sym2 S) := {edge | η (Sym2.map Subtype.val edge) = true}
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
  have hp' : ∀ edge ∈ p.edges, edge ∈ E := by
    intro edge he
    exact (isBondOpenWalk_iff_local_edges η p).mp hp edge he
  obtain ⟨x, y, q, hx, hy, hqC, hqE⟩ :=
    exists_interior_path_between_boundaries A B C U W E hdis hsep hinner hu hw p ha hb hp'
  refine ⟨x, y, q.bypass, ⟨q.bypass_isPath, hx.1, hy.1, hx.2.1, hx.2.2,
    hy.2.1, hy.2.2, fun z hz => hqC z (q.support_bypass_subset_support hz)⟩, ?_⟩
  · rw [isBondOpenWalk_iff_local_edges]
    intro edge he
    have he' := q.edges_bypass_subset_edges he
    apply hag edge ?_ (hqE edge he')
    intro z hz
    exact hqC z (q.mem_support_of_mem_edges he' hz)

end Sandpile.External.RSW
