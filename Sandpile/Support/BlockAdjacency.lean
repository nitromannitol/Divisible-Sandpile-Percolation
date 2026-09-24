/-
Adjacency of good coarse blocks: if two neighbouring coarse sites of the
`(2r)`-lattice are both good for the field `F` at level `ℓ`, then the
level-`ℓ` superlevel set of `F` contains a nearest-neighbour walk joining a
site of the first block's square to a site of the second block's square.
This is the deterministic overlap step of `sandpile.tex:3979-3986`: the
wide rectangle's left-right crossing meets the top-bottom crossings of both
squares, because a bottom-top walk of the square is also a bottom-top walk
of the wide rectangle, and opposite crossings of one rectangle intersect.
-/
import Sandpile.Support.BlockVerticalWalk
import Sandpile.Support.PercSquareToWide
import Sandpile.Support.PercAbsHom
import Sandpile.Support.BlockSubwalk

open scoped NNReal
noncomputable section
namespace Sandpile

/-- If two horizontally adjacent coarse sites are both good, the superlevel
set contains a nearest-neighbour walk from the block at `z` to the block at
`z + e₀`. -/
theorem blockGood_adj_e0 {r : ℕ} (hr : 1 ≤ r) (F : Site 2 → ℝ) (ℓ : ℝ) (z : Site 2)
    (h1 : BlockGood r F ℓ z) (h2 : BlockGood r F ℓ (z + ![(1 : ℤ), (0 : ℤ)])) :
    ∃ a b : Site 2, ∃ p : (lattice 2).Walk a b,
      (∀ u ∈ p.support, ℓ ≤ F u) ∧
      (∃ u ∈ p.support, ∀ i : Fin 2, |u i - 2 * r * z i| ≤ 2 * r) ∧
      (∃ u ∈ p.support, ∀ i : Fin 2, |u i - 2 * r * (z + ![(1 : ℤ), (0 : ℤ)]) i| ≤ 2 * r) := by
  -- Step 1: LR walk of the wide rectangle at z
  simp only [BlockGood] at h1
  rw [show 4 * r = 2 * r + 2 * r from by omega] at h1
  obtain ⟨a₁, b₁, p₁, ha₁, hb₁, hp₁⟩ :=
    exists_lr_walk_of_le_crossingValue
      (fun w : planeRectangle (2 * r + 2 * r) (2 * r) => F (blockShift r z w)) h1.2.2.1
  -- Step 2: TB walk of the square at z+e₀, translated into the wide rectangle
  obtain ⟨c, d, q, hc, hd, hq, hqhalf⟩ := tb_square_to_wide hr F ℓ z h2
  -- Step 4: intersection
  obtain ⟨s₀, hs₀p, hs₀q⟩ := nn_lr_tb_intersect p₁ q ha₁ hb₁ hc hd
  -- Step 5: the shared site as a rectangle element
  rw [List.mem_map] at hs₀p
  obtain ⟨s, hs, rfl⟩ := hs₀p
  -- Step 6: subwalk of p₁ from a₁ to s
  obtain ⟨p', hp's⟩ := exists_subwalk p₁ p₁.start_mem_support hs
  -- Step 7: absolute walk
  refine ⟨blockShift r z (a₁ : Site 2), blockShift r z (s : Site 2),
    p'.map (rectAbsHom r z (2 * r + 2 * r) (2 * r)), ?_, ?_, ?_⟩
  · exact walk_abs_support z p' F ℓ (fun u hu => hp₁ u (hp's u hu))
  · refine ⟨blockShift r z (a₁ : Site 2),
      (p'.map (rectAbsHom r z (2 * r + 2 * r) (2 * r))).start_mem_support, ?_⟩
    have hz0 : (a₁ : Site 2) 0 = 0 := by
      simp only [rectangleLeft, Finset.mem_filter, Finset.mem_univ, true_and] at ha₁
      have e0 : (![0, 0] : Site 2) 0 = 0 := rfl
      have e1 : (![0, 0] : Site 2) 1 = 0 := rfl
      have hmem0 : (![0, 0] : Site 2) ∈ planeRectangle (2 * r + 2 * r) (2 * r) := by
        rw [mem_planeRectangle, e0, e1]
        omega
      have hle := ha₁ ![0, 0] hmem0
      have hge : 0 ≤ (a₁ : Site 2) 0 := ((mem_planeRectangle _ _ (a₁ : Site 2)).mp a₁.property).1
      exact le_antisymm hle hge
    have hmem := (mem_planeRectangle _ _ (a₁ : Site 2)).mp a₁.property
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · set_option linter.unusedSimpArgs false in
      simp only [blockShift, Pi.add_apply, Matrix.cons_val_zero, sub_self]
      rw [hz0, abs_le]
      constructor <;> nlinarith [hmem.1, hmem.2.2.1]
    · simp only [blockShift, Pi.add_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [abs_le]
      constructor
      · nlinarith [hmem.1]
      · have : (a₁ : Site 2) 1 + 2 * (r:ℤ) * z 1 - 2 * (r:ℤ) * z 1 = (a₁ : Site 2) 1 := by ring
        rw [this]
        have h2 : (a₁ : Site 2) 1 ≤ 2 * (r:ℤ) := by simpa using hmem.2.2.2
        linarith
  · -- the shared site lies in the right half, hence in the square of z + e₀
    have hsq : s ∈ q.support := by
      have hmem : (s : Site 2) ∈ List.map
          (fun x : planeRectangle (2 * r + 2 * r) (2 * r) => (x : Site 2)) q.support := hs₀q
      rw [List.mem_map] at hmem
      obtain ⟨t, ht, htval⟩ := hmem
      have hts : t = s := Subtype.ext htval
      exact hts ▸ ht
    have hsright : 2 * r ≤ (s : Site 2) 0 := hqhalf s hsq
    have hsmem := (mem_planeRectangle _ _ (s : Site 2)).mp s.property
    refine ⟨blockShift r z (s : Site 2), ?_, ?_⟩
    · exact (p'.map (rectAbsHom r z (2 * r + 2 * r) (2 * r))).end_mem_support
    have hz1 : (z + ![(1 : ℤ), (0 : ℤ)] : Site 2) = ![z 0 + 1, z 1] := by
      funext i
      fin_cases i <;> simp
    have hs0 : 2 * (r:ℤ) ≤ (s : Site 2) 0 := by simpa using hsright
    have hs0' : (s : Site 2) 0 ≤ 2 * (r:ℤ) + 2 * (r:ℤ) := by simpa using hsmem.2.1
    have hs1 : (s : Site 2) 1 ≤ 2 * (r:ℤ) := by simpa using hsmem.2.2.2
    have hs1' : 0 ≤ (s : Site 2) 1 := hsmem.2.2.1
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · set_option linter.unusedSimpArgs false in
      simp only [blockShift, Pi.add_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, hz1]
      rw [abs_le]
      constructor <;> nlinarith [hs0, hs0']
    · set_option linter.unusedSimpArgs false in
      simp only [blockShift, Pi.add_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, hz1, add_zero]
      rw [abs_le]
      constructor <;> nlinarith [hs1, hs1']
