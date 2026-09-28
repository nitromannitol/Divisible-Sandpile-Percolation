import Sandpile.Support.BlockAdjacency
import Sandpile.Support.PercSquareToWide
import Sandpile.Support.BlockVerticalWalk
import Sandpile.Support.BlockSubwalk

/-!
# Routing across adjacent good coarse blocks

Routing across adjacent good coarse blocks: `block_route_adj_e0` handles blocks at `z` and
`z + e₀` (horizontally adjacent) and `block_route_adj_e1` handles blocks at `z` and `z + e₁`
(vertically adjacent). If both blocks are good for the field `F` at level `ℓ`, then for any
crossing walk of each square transverse to the adjacency direction (both with field values at
least `ℓ`), the starts of the two walks are joined by a nearest-neighbour walk on the lattice
whose every site has field value at least `ℓ`. The route runs along the first crossing walk to
its intersection with the wide/tall crossing of the block at `z` (`nn_lr_tb_intersect`), along
that wide/tall crossing to its intersection with the translate of the second crossing walk, and
along the second crossing walk to its start.
-/

open scoped NNReal
set_option maxHeartbeats 1000000
noncomputable section
namespace Sandpile

/-- For horizontally adjacent good blocks at `z` and `z + e₀`, any two bottom-top crossing walks
`TB₁`, `TB₂` of the respective squares (with field values at least `ℓ`) have their starts joined
by a lattice walk of field values at least `ℓ`, routed through the wide left-right crossing of the
block at `z`. -/
theorem block_route_adj_e0 {r : ℕ} (hr : 1 ≤ r) (F : Site 2 → ℝ) (ℓ : ℝ) (z : Site 2)
    (h1 : BlockGood r F ℓ z)
    (c₁ d₁ : planeRectangle (2 * r) (2 * r))
    (TB₁ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₁ d₁)
    (hc₁ : (c₁ : Site 2) 1 = 0) (hd₁ : (d₁ : Site 2) 1 = ↑(2 * r))
    (hTB₁ : ∀ u ∈ TB₁.support, ℓ ≤ F (blockShift r z u))
    (c₂ d₂ : planeRectangle (2 * r) (2 * r))
    (TB₂ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₂ d₂)
    (hc₂ : (c₂ : Site 2) 1 = 0) (hd₂ : (d₂ : Site 2) 1 = ↑(2 * r))
    (hTB₂ : ∀ u ∈ TB₂.support, ℓ ≤ F (blockShift r (z + ![(1 : ℤ), (0 : ℤ)]) u)) :
    ∃ a b : Site 2, ∃ p : (lattice 2).Walk a b,
      a = blockShift r z (c₁ : Site 2) ∧ b = blockShift r (z + ![(1 : ℤ), (0 : ℤ)]) (c₂ : Site 2) ∧
      (∀ u ∈ p.support, ℓ ≤ F u) := by
  -- Step 1: the wide left-right crossing of the block at z
  simp only [BlockGood] at h1
  rw [show 4 * r = 2 * r + 2 * r from by omega] at h1
  obtain ⟨a₁, b₁, p₁, ha₁, hb₁, hp₁⟩ :=
    exists_lr_walk_of_le_crossingValue
      (fun w : planeRectangle (2 * r + 2 * r) (2 * r) => F (blockShift r z w)) h1.2.2.1
  -- Step 2: TB₁ and TB₂ as bottom-top walks of the wide rectangle
  -- field bounds for the two translated walks, in wide-rectangle coordinates
  have hTB₁' : ∀ w ∈ (TB₁.map (rectangleIncl (show 2 * r ≤ 2 * r + 2 * r by omega))).support,
      ℓ ≤ F (blockShift r z w) := by
    intro w hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact hTB₁ v hv
  have hTB₂' : ∀ w ∈ (TB₂.map (rectTranslateHom (2 * r) (2 * r) (2 * r) 0)).support,
      ℓ ≤ F (blockShift r z w) := by
    intro w hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    have hv' : ((rectTranslateHom (2 * r) (2 * r) (2 * r) 0) v : Site 2)
        = (v : Site 2) + ![(2 * r : ℤ), (0 : ℤ)] := rfl
    have hid : blockShift r (z + ![(1 : ℤ), (0 : ℤ)]) (v : Site 2)
        = blockShift r z ((v : Site 2) + ![(2 * r : ℤ), (0 : ℤ)]) := by
      funext i
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;>
        simp only [blockShift, Pi.add_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;> ring
    rw [hv', ← hid]
    exact hTB₂ v hv
  -- Step 3: the two intersection sites
  obtain ⟨u, hu₁, hu₁'⟩ := nn_lr_tb_intersect p₁
    (TB₁.map (rectangleIncl (show 2 * r ≤ 2 * r + 2 * r by omega))) ha₁ hb₁
    (show (((rectangleIncl (show 2 * r ≤ 2 * r + 2 * r by omega)) c₁ : Site 2)) 1 = 0 by
      exact hc₁)
    (show (((rectangleIncl (show 2 * r ≤ 2 * r + 2 * r by omega)) d₁ : Site 2)) 1 = ↑(2 * r) by
      exact hd₁)
  obtain ⟨u', hu'₁, hu'₂⟩ := nn_lr_tb_intersect p₁
    (TB₂.map (rectTranslateHom (2 * r) (2 * r) (2 * r) 0)) ha₁ hb₁
    (show (((rectTranslateHom (2 * r) (2 * r) (2 * r) 0) c₂ : Site 2)) 1 = 0 by
      simpa [rectTranslateHom, Pi.add_apply, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.vecTail, Matrix.vecHead] using hc₂)
    (show (((rectTranslateHom (2 * r) (2 * r) (2 * r) 0) d₂ : Site 2)) 1 = ↑(2 * r) by
      simpa [rectTranslateHom, Pi.add_apply, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.vecTail, Matrix.vecHead] using hd₂)
  -- Step 4: subtypes on the supports
  rw [List.mem_map] at hu₁
  obtain ⟨s₁, hs₁, rfl⟩ := hu₁
  rw [SimpleGraph.Walk.support_map] at hu₁'
  obtain ⟨t₁, ht₁, hut₁⟩ := List.mem_map.mp hu₁'
  obtain ⟨w, hw, hwv⟩ := List.mem_map.mp ht₁
  have ht₁ : w ∈ TB₁.support := hw
  have hutw : (w : Site 2) = (s₁ : Site 2) := by
    have hw1 : (w : Site 2) = (t₁ : Site 2) := congrArg Subtype.val hwv
    rw [hw1]
    exact hut₁
  rw [List.mem_map] at hu'₁
  obtain ⟨s₁', hs₁', rfl⟩ := hu'₁
  rw [SimpleGraph.Walk.support_map] at hu'₂
  obtain ⟨t₂, ht₂, hut₂⟩ := List.mem_map.mp hu'₂
  obtain ⟨w', hw', hwv'⟩ := List.mem_map.mp ht₂
  have ht₂ : w' ∈ TB₂.support := hw'
  have hutw' : ((w' : Site 2) + ![(2 * r : ℤ), (0 : ℤ)] : Site 2) = (s₁' : Site 2) := by
    have hw2 : ((w' : Site 2) + ![(2 * r : ℤ), (0 : ℤ)] : Site 2) = (t₂ : Site 2) :=
      congrArg Subtype.val hwv'
    rw [hw2]
    exact hut₂
  -- Step 5: the three subwalks
  obtain ⟨A, hAs⟩ := exists_subwalk TB₁ TB₁.start_mem_support ht₁
  obtain ⟨B, hBs⟩ := exists_subwalk p₁ hs₁ hs₁'
  obtain ⟨C, hCs⟩ := exists_subwalk TB₂ ht₂ TB₂.start_mem_support
  -- Step 6: the three subwalks
  obtain ⟨A, hAs⟩ := exists_subwalk TB₁ TB₁.start_mem_support ht₁
  obtain ⟨B, hBs⟩ := exists_subwalk p₁ hs₁ hs₁'
  obtain ⟨C, hCs⟩ := exists_subwalk TB₂ ht₂ TB₂.start_mem_support
  -- Step 7: map to the absolute lattice
  have hA : ∀ u ∈ (A.map (rectAbsHom r z (2 * r) (2 * r))).support, ℓ ≤ F u := by
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact hTB₁ v (hAs v hv)
  have hB : ∀ u ∈ (B.map (rectAbsHom r z (2 * r + 2 * r) (2 * r))).support, ℓ ≤ F u := by
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact hp₁ v (hBs v hv)
  have hC : ∀ u ∈ (C.map (rectAbsHom r (z + ![(1 : ℤ), (0 : ℤ)]) (2 * r) (2 * r))).support,
      ℓ ≤ F u := by
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact hTB₂ v (hCs v hv)
  -- Step 8: endpoint matching
  have e1 : blockShift r z (w : Site 2) = blockShift r z (s₁ : Site 2) := by rw [hutw]
  have e2 : blockShift r z (s₁' : Site 2)
      = blockShift r (z + ![(1 : ℤ), (0 : ℤ)]) (w' : Site 2) := by
    have : blockShift r z ((w' : Site 2) + ![(2 * r : ℤ), (0 : ℤ)])
        = blockShift r (z + ![(1 : ℤ), (0 : ℤ)]) (w' : Site 2) := by
      funext i
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;>
        simp only [blockShift, Pi.add_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;> ring
    rw [← hutw']
    exact this
  -- Step 9: concatenate
  refine ⟨blockShift r z (c₁ : Site 2),
    blockShift r (z + ![(1 : ℤ), (0 : ℤ)]) (c₂ : Site 2),
    SimpleGraph.Walk.append
      (SimpleGraph.Walk.copy (SimpleGraph.Walk.map (rectAbsHom r z (2 * r) (2 * r)) A) rfl e1)
      (SimpleGraph.Walk.append
        (SimpleGraph.Walk.copy
          (SimpleGraph.Walk.map (rectAbsHom r z (2 * r + 2 * r) (2 * r)) B) rfl e2)
        (SimpleGraph.Walk.map (rectAbsHom r (z + ![(1 : ℤ), (0 : ℤ)]) (2 * r) (2 * r)) C)),
    rfl, rfl, ?_⟩
  intro u hu
  rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy] at hu
  rw [List.mem_append] at hu
  rcases hu with hu | hu
  · exact hA u hu
  · have hu' := List.mem_of_mem_tail hu
    rw [List.mem_append] at hu'
    rcases hu' with hu' | hu'
    · exact hB u hu'
    · exact hC u (List.mem_of_mem_tail hu')

/-- For vertically adjacent good blocks at `z` and `z + e₁`, any two left-right crossing walks
`LR₁`, `LR₂` of the respective squares (with field values at least `ℓ`) have their starts joined
by a lattice walk of field values at least `ℓ`, routed through the tall bottom-top crossing of the
block at `z`. -/
theorem block_route_adj_e1 {r : ℕ} (hr : 1 ≤ r) (F : Site 2 → ℝ) (ℓ : ℝ) (z : Site 2)
    (h1 : BlockGood r F ℓ z)
    (c₁ d₁ : planeRectangle (2 * r) (2 * r))
    (LR₁ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₁ d₁)
    (hc₁ : (c₁ : Site 2) 0 = 0) (hd₁ : (d₁ : Site 2) 0 = ↑(2 * r))
    (hLR₁ : ∀ u ∈ LR₁.support, ℓ ≤ F (blockShift r z u))
    (c₂ d₂ : planeRectangle (2 * r) (2 * r))
    (LR₂ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₂ d₂)
    (hc₂ : (c₂ : Site 2) 0 = 0) (hd₂ : (d₂ : Site 2) 0 = ↑(2 * r))
    (hLR₂ : ∀ u ∈ LR₂.support, ℓ ≤ F (blockShift r (z + ![(0 : ℤ), (1 : ℤ)]) u)) :
    ∃ a b : Site 2, ∃ p : (lattice 2).Walk a b,
      a = blockShift r z (c₁ : Site 2) ∧ b = blockShift r (z + ![(0 : ℤ), (1 : ℤ)]) (c₂ : Site 2) ∧
      (∀ u ∈ p.support, ℓ ≤ F u) := by
  -- Step 1: the tall bottom-top crossing of the block at z
  simp only [BlockGood] at h1
  rw [show 4 * r = 2 * r + 2 * r from by omega] at h1
  obtain ⟨a₁, b₁, p₁, ha₁, hb₁, hp₁⟩ :=
    exists_tb_walk_of_le_verticalCrossingValue
      (fun w : planeRectangle (2 * r) (2 * r + 2 * r) => F (blockShift r z w)) h1.2.2.2
  -- Step 2: LR₁ and LR₂ as left-right walks of the tall rectangle
  have hLR₁' : ∀ w ∈ (LR₁.map (rectangleInclVert (show 2 * r ≤ 2 * r + 2 * r by omega))).support,
      ℓ ≤ F (blockShift r z w) := by
    intro w hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact hLR₁ v hv
  have hLR₂' : ∀ w ∈ (LR₂.map (rectTranslateHom (2 * r) (2 * r) 0 (2 * r))).support,
      ℓ ≤ F (blockShift r z w) := by
    intro w hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    have hv' : ((rectTranslateHom (2 * r) (2 * r) 0 (2 * r)) v : Site 2)
        = (v : Site 2) + ![(0 : ℤ), (2 * r : ℤ)] := rfl
    have hid : blockShift r (z + ![(0 : ℤ), (1 : ℤ)]) (v : Site 2)
        = blockShift r z ((v : Site 2) + ![(0 : ℤ), (2 * r : ℤ)]) := by
      funext i
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;>
        simp only [blockShift, Pi.add_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;> ring
    rw [hv', ← hid]
    exact hLR₂ v hv
  -- Step 3: the two intersection sites
  obtain ⟨u, hu₁, hu₁'⟩ := nn_lr_tb_intersect
    (LR₁.map (rectangleInclVert (show 2 * r ≤ 2 * r + 2 * r by omega))) p₁
    (show (rectangleInclVert (show 2 * r ≤ 2 * r + 2 * r by omega)) c₁
        ∈ rectangleLeft (planeRectangle (2 * r) (2 * r + 2 * r)) by
      exact (mem_rectangleLeft_planeRectangle _).mpr hc₁)
    (show (rectangleInclVert (show 2 * r ≤ 2 * r + 2 * r by omega)) d₁
        ∈ rectangleRight (planeRectangle (2 * r) (2 * r + 2 * r)) by
      exact (mem_rectangleRight_planeRectangle _).mpr hd₁)
    ha₁ hb₁
  obtain ⟨u', hu'₁, hu'₂⟩ := nn_lr_tb_intersect
    (LR₂.map (rectTranslateHom (2 * r) (2 * r) 0 (2 * r))) p₁
    (show (rectTranslateHom (2 * r) (2 * r) 0 (2 * r)) c₂
        ∈ rectangleLeft (planeRectangle (2 * r) (2 * r + 2 * r)) by
      have : ((rectTranslateHom (2 * r) (2 * r) 0 (2 * r)) c₂ : Site 2) 0 = 0 := by
        simpa [rectTranslateHom, Pi.add_apply, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.vecTail, Matrix.vecHead] using hc₂
      exact (mem_rectangleLeft_planeRectangle _).mpr this)
    (show (rectTranslateHom (2 * r) (2 * r) 0 (2 * r)) d₂
        ∈ rectangleRight (planeRectangle (2 * r) (2 * r + 2 * r)) by
      have : ((rectTranslateHom (2 * r) (2 * r) 0 (2 * r)) d₂ : Site 2) 0 = ↑(2 * r) := by
        simpa [rectTranslateHom, Pi.add_apply, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.vecTail, Matrix.vecHead] using hd₂
      exact (mem_rectangleRight_planeRectangle _).mpr this)
    ha₁ hb₁
  -- Step 4: unwrap the intersection sites to elements of the square walks
  rw [List.mem_map] at hu₁
  obtain ⟨s₁, hs₁, rfl⟩ := hu₁
  rw [SimpleGraph.Walk.support_map] at hs₁
  obtain ⟨v₁, hv₁, hvv⟩ := List.mem_map.mp hs₁
  obtain ⟨t₁, ht₁, hut₁⟩ := List.mem_map.mp hu₁'
  have hutw : (v₁ : Site 2) = (t₁ : Site 2) := by
    have h1' : (v₁ : Site 2) =
        ((rectangleInclVert (show 2 * r ≤ 2 * r + 2 * r by omega)) v₁ : Site 2) := rfl
    have h2' : ((rectangleInclVert (show 2 * r ≤ 2 * r + 2 * r by omega)) v₁ : Site 2) =
        (s₁ : Site 2) :=
      congrArg Subtype.val hvv
    rw [h1', h2']
    exact hut₁.symm
  rw [List.mem_map] at hu'₁
  obtain ⟨s₁', hs₁', rfl⟩ := hu'₁
  rw [SimpleGraph.Walk.support_map] at hs₁'
  obtain ⟨w', hw', hwv'⟩ := List.mem_map.mp hs₁'
  obtain ⟨t₂, ht₂, hut₂⟩ := List.mem_map.mp hu'₂
  have hutw' : ((w' : Site 2) + ![(0 : ℤ), (2 * r : ℤ)] : Site 2) = (t₂ : Site 2) := by
    have hw2 : ((w' : Site 2) + ![(0 : ℤ), (2 * r : ℤ)] : Site 2)
        = ((rectTranslateHom (2 * r) (2 * r) 0 (2 * r)) w' : Site 2) := rfl
    rw [hw2]
    exact (congrArg Subtype.val hwv').trans hut₂.symm
  -- Step 5: the three subwalks
  obtain ⟨A, hAs⟩ := exists_subwalk LR₁ LR₁.start_mem_support hv₁
  obtain ⟨B, hBs⟩ := exists_subwalk p₁ ht₁ ht₂
  obtain ⟨C, hCs⟩ := exists_subwalk LR₂ hw' LR₂.start_mem_support
  -- Step 6: map to the absolute lattice
  have hA : ∀ u ∈ (A.map (rectAbsHom r z (2 * r) (2 * r))).support, ℓ ≤ F u := by
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact hLR₁ v (hAs v hv)
  have hB : ∀ u ∈ (B.map (rectAbsHom r z (2 * r) (2 * r + 2 * r))).support, ℓ ≤ F u := by
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact hp₁ v (hBs v hv)
  have hC : ∀ u ∈ (C.map (rectAbsHom r (z + ![(0 : ℤ), (1 : ℤ)]) (2 * r) (2 * r))).support,
      ℓ ≤ F u := by
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact hLR₂ v (hCs v hv)
  -- Step 7: endpoint matching
  have e1 : blockShift r z (v₁ : Site 2) = blockShift r z (t₁ : Site 2) := by rw [hutw]
  have e2 : blockShift r z (t₂ : Site 2)
      = blockShift r (z + ![(0 : ℤ), (1 : ℤ)]) (w' : Site 2) := by
    have : blockShift r z ((w' : Site 2) + ![(0 : ℤ), (2 * r : ℤ)])
        = blockShift r (z + ![(0 : ℤ), (1 : ℤ)]) (w' : Site 2) := by
      funext i
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;>
        simp only [blockShift, Pi.add_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;> ring
    rw [← hutw']
    exact this
  -- Step 8: concatenate
  refine ⟨blockShift r z (c₁ : Site 2),
    blockShift r (z + ![(0 : ℤ), (1 : ℤ)]) (c₂ : Site 2),
    SimpleGraph.Walk.append
      (SimpleGraph.Walk.copy (SimpleGraph.Walk.map (rectAbsHom r z (2 * r) (2 * r)) A) rfl e1)
      (SimpleGraph.Walk.append
        (SimpleGraph.Walk.copy
          (SimpleGraph.Walk.map (rectAbsHom r z (2 * r) (2 * r + 2 * r)) B) rfl e2)
        (SimpleGraph.Walk.map (rectAbsHom r (z + ![(0 : ℤ), (1 : ℤ)]) (2 * r) (2 * r)) C)),
    rfl, rfl, ?_⟩
  intro u hu
  rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy] at hu
  rw [List.mem_append] at hu
  rcases hu with hu | hu
  · exact hA u hu
  · have hu' := List.mem_of_mem_tail hu
    rw [List.mem_append] at hu'
    rcases hu' with hu' | hu'
    · exact hB u hu'
    · exact hC u (List.mem_of_mem_tail hu')
end Sandpile