import Sandpile.Support.BlockAdjacency
import Sandpile.Support.PercSquareToTall

/-!
# Vertical adjacency of good coarse blocks

If two vertically neighbouring coarse sites of the `(2r)`-lattice are both good for the
field `F` at level `ℓ`, then the level-`ℓ` superlevel set of `F` contains a
nearest-neighbour walk joining a site of the lower block's square to a site of the upper
block's square.  This is the vertical counterpart of `Sandpile.Support.BlockAdjacency`,
obtained by intersecting a top-bottom crossing of the tall rectangle with a left-right
crossing of the upper square instead of a wide rectangle with a right square.
-/

open scoped NNReal
noncomputable section
namespace Sandpile

/-- If two vertically adjacent coarse sites are both good, the superlevel set contains a
nearest-neighbour walk from the block at `z` to the block at `z + e₁`, obtained by
intersecting the top-bottom crossing of the tall rectangle at `z` with the left-right
crossing of the square at `z + e₁`. -/
theorem blockGood_adj_e1 {r : ℕ} (hr : 1 ≤ r) (F : Site 2 → ℝ) (ℓ : ℝ) (z : Site 2)
    (h1 : BlockGood r F ℓ z) (h2 : BlockGood r F ℓ (z + ![(0 : ℤ), (1 : ℤ)])) :
    ∃ a b : Site 2, ∃ p : (lattice 2).Walk a b,
      (∀ u ∈ p.support, ℓ ≤ F u) ∧
      (∃ u ∈ p.support, ∀ i : Fin 2, |u i - 2 * r * z i| ≤ 2 * r) ∧
      (∃ u ∈ p.support, ∀ i : Fin 2, |u i - 2 * r * (z + ![(0 : ℤ), (1 : ℤ)]) i| ≤ 2 * r) := by
  -- Step 1: TB walk of the tall rectangle at z
  simp only [BlockGood] at h1
  rw [show 4 * r = 2 * r + 2 * r from by omega] at h1
  obtain ⟨c₁, d₁, p₁, hc₁, hd₁, hp₁⟩ :=
    exists_tb_walk_of_le_verticalCrossingValue
      (fun w : planeRectangle (2 * r) (2 * r + 2 * r) => F (blockShift r z w)) h1.2.2.2
  -- Step 2: LR walk of the square at z+e₁, translated into the tall rectangle
  obtain ⟨c, d, q, hc, hd, hq, hqhalf⟩ := lr_square_to_tall hr F ℓ z h2
  -- Step 4: intersection
  have hqc : c ∈ rectangleLeft (planeRectangle (2 * r) (2 * r + 2 * r)) :=
    (mem_rectangleLeft_planeRectangle _).mpr hc
  have hqd : d ∈ rectangleRight (planeRectangle (2 * r) (2 * r + 2 * r)) :=
    (mem_rectangleRight_planeRectangle _).mpr hd
  obtain ⟨s₀, hs₀q, hs₀p⟩ := nn_lr_tb_intersect q p₁ hqc hqd hc₁ hd₁
  -- Step 5: the shared site as a rectangle element
  rw [List.mem_map] at hs₀p
  obtain ⟨s, hs, rfl⟩ := hs₀p
  -- Step 6: subwalk of p₁ from c₁ to s
  obtain ⟨p', hp's⟩ := exists_subwalk p₁ p₁.start_mem_support hs
  -- Step 7: absolute walk
  refine ⟨blockShift r z (c₁ : Site 2), blockShift r z (s : Site 2),
    p'.map (rectAbsHom r z (2 * r) (2 * r + 2 * r)), ?_, ?_, ?_⟩
  · exact walk_abs_support z p' F ℓ (fun u hu => hp₁ u (hp's u hu))
  · refine ⟨blockShift r z (c₁ : Site 2),
      (p'.map (rectAbsHom r z (2 * r) (2 * r + 2 * r))).start_mem_support, ?_⟩
    have hmem := (mem_planeRectangle _ _ (c₁ : Site 2)).mp c₁.property
    have h0 : (c₁ : Site 2) 0 ≤ 2 * (r:ℤ) := by simpa using hmem.2.1
    have h1' : 0 ≤ (c₁ : Site 2) 0 := hmem.1
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · set_option linter.unusedSimpArgs false in
      simp only [blockShift, Pi.add_apply, Matrix.cons_val_zero, add_zero, sub_self]
      rw [abs_le]
      constructor <;> nlinarith [h0, h1']
    · simp only [blockShift, Pi.add_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [hc₁, abs_le]
      constructor <;> nlinarith
  · -- the shared site lies in the top half, hence in the square of z + e₁
    have hsq : s ∈ q.support := by
      have hmem : (s : Site 2) ∈ List.map
          (fun x : planeRectangle (2 * r) (2 * r + 2 * r) => (x : Site 2)) q.support := hs₀q
      rw [List.mem_map] at hmem
      obtain ⟨t, ht, htval⟩ := hmem
      have hts : t = s := Subtype.ext htval
      exact hts ▸ ht
    have hsright : 2 * r ≤ (s : Site 2) 1 := hqhalf s hsq
    have hsmem := (mem_planeRectangle _ _ (s : Site 2)).mp s.property
    refine ⟨blockShift r z (s : Site 2), ?_, ?_⟩
    · exact (p'.map (rectAbsHom r z (2 * r) (2 * r + 2 * r))).end_mem_support
    · have hz1 : (z + ![(0 : ℤ), (1 : ℤ)] : Site 2) = ![z 0, z 1 + 1] := by
        funext i
        fin_cases i <;> simp
      have hs1 : 2 * (r:ℤ) ≤ (s : Site 2) 1 := by simpa using hsright
      have hs1' : (s : Site 2) 1 ≤ 2 * (r:ℤ) + 2 * (r:ℤ) := by simpa using hsmem.2.2.2
      have hs0 : (s : Site 2) 0 ≤ 2 * (r:ℤ) := by simpa using hsmem.2.1
      have hs0' : 0 ≤ (s : Site 2) 0 := hsmem.1
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · set_option linter.unusedSimpArgs false in
        simp only [blockShift, Pi.add_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, hz1, add_zero]
        rw [abs_le]
        constructor <;> nlinarith [hs0, hs0']
      · set_option linter.unusedSimpArgs false in
        simp only [blockShift, Pi.add_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, hz1, add_zero]
        rw [abs_le]
        constructor <;> nlinarith [hs1, hs1']

end Sandpile