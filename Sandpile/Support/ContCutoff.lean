/-
The continuous time cutoff that removes the small times from the double time sum
of `prop:weighted-membrane-limit` (`sandpile.tex:4724-4729`).

The double time sum runs over every pair of times below the horizon, and the
local central limit theorem covers only the times at least `δR²`.  Multiplying
the weight by a continuous function which vanishes below `δ` and is one above
`2δ` removes the small times without breaking the continuity the Riemann-sum
theorems need, and the pairs of times it changes number at most `4δT R⁴`, so the
change it makes to the sum is `O(δ)` uniformly in the scale.
-/
import Sandpile.Support.ContBMKernel

open Filter Topology

namespace Sandpile.Support

/-- The continuous cutoff: zero below `δ`, one above `2δ`, and values in `[0,1]`. -/
noncomputable def cutoffFn (δ r : ℝ) : ℝ := max 0 (min 1 (r / δ - 1))

theorem continuous_cutoffFn (δ : ℝ) : Continuous (cutoffFn δ) := by
  unfold cutoffFn
  exact continuous_const.max
    (continuous_const.min ((continuous_id.div_const δ).sub continuous_const))

theorem cutoffFn_nonneg (δ r : ℝ) : 0 ≤ cutoffFn δ r := le_max_left _ _

theorem cutoffFn_le_one (δ r : ℝ) : cutoffFn δ r ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem abs_cutoffFn_le_one (δ r : ℝ) : |cutoffFn δ r| ≤ 1 := by
  rw [abs_of_nonneg (cutoffFn_nonneg δ r)]
  exact cutoffFn_le_one δ r

/-- The cutoff vanishes below `δ`. -/
theorem cutoffFn_eq_zero {δ r : ℝ} (hδ : 0 < δ) (h : r ≤ δ) : cutoffFn δ r = 0 := by
  have hle : r / δ ≤ 1 := by
    rw [div_le_one hδ]
    exact h
  have hmin : min 1 (r / δ - 1) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
  exact max_eq_left hmin

/-- The cutoff is one above `2δ`. -/
theorem cutoffFn_eq_one {δ r : ℝ} (hδ : 0 < δ) (h : 2 * δ ≤ r) : cutoffFn δ r = 1 := by
  have hge : 2 ≤ r / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  have hmin : min 1 (r / δ - 1) = 1 := min_eq_left (by linarith)
  unfold cutoffFn
  rw [hmin]
  exact max_eq_right zero_le_one

/-! ### The cut weight

The weight of `prop:weighted-membrane-limit` is continuous on `[0,T]` only, so it
is first extended to a globally continuous function and then multiplied by the
cutoff, which makes it vanish below `δ` without changing it above `2δ` and
without changing its bound. -/

/-- The cut weight is bounded by the bound on the weight. -/
theorem abs_mul_cutoffFn_le {δ r Q : ℝ} {q : ℝ → ℝ} (hQ0 : 0 ≤ Q) (hQ : ∀ s, |q s| ≤ Q) :
    |q r * cutoffFn δ r| ≤ Q := by
  rw [abs_mul]
  calc |q r| * |cutoffFn δ r| ≤ Q * 1 :=
        mul_le_mul (hQ r) (abs_cutoffFn_le_one δ r) (abs_nonneg _) hQ0
    _ = Q := mul_one Q

theorem mul_cutoffFn_eq_of_ge {δ r : ℝ} (hδ : 0 < δ) (h : 2 * δ ≤ r) (q : ℝ → ℝ) :
    q r * cutoffFn δ r = q r := by
  rw [cutoffFn_eq_one hδ h, mul_one]

theorem mul_cutoffFn_eq_zero {δ r : ℝ} (hδ : 0 < δ) (h : r ≤ δ) (q : ℝ → ℝ) :
    q r * cutoffFn δ r = 0 := by
  rw [cutoffFn_eq_zero hδ h, mul_zero]

theorem exists_bound_of_continuousOn_Icc {T : ℝ} (hT : (0:ℝ) ≤ T) (q : ℝ → ℝ)
    (hq : ContinuousOn q (Set.Icc 0 T)) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ r ∈ Set.Icc (0:ℝ) T, |q r| ≤ Q := by
  have hne : (Set.Icc (0:ℝ) T).Nonempty := ⟨0, by constructor <;> simp [hT]⟩
  have hcpt : IsCompact (Set.Icc (0:ℝ) T) := isCompact_Icc
  obtain ⟨x, hx, hmax⟩ := hcpt.exists_isMaxOn hne hq.abs
  exact ⟨|q x|, abs_nonneg _, fun r hr => hmax hr⟩

theorem card_edge_block_le (N M : ℕ) :
    (((Finset.range N) ×ˢ (Finset.range N)).filter
      (fun p : ℕ × ℕ => p.1 < M ∨ p.2 < M)).card ≤ 2 * (M * N) := by
  classical
  have hsub : (((Finset.range N) ×ˢ (Finset.range N)).filter
      (fun p : ℕ × ℕ => p.1 < M ∨ p.2 < M))
      ⊆ ((Finset.range M) ×ˢ (Finset.range N)) ∪ ((Finset.range N) ×ˢ (Finset.range M)) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    rw [Finset.mem_union, Finset.mem_product, Finset.mem_product, Finset.mem_range,
      Finset.mem_range, Finset.mem_range, Finset.mem_range]
    omega
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  simp only [Finset.card_product, Finset.card_range]
  rw [Nat.mul_comm N M]
  omega

theorem exists_continuous_extension {T : ℝ} (hT : (0:ℝ) ≤ T) (q : ℝ → ℝ)
    (hq : ContinuousOn q (Set.Icc 0 T)) :
    ∃ q' : ℝ → ℝ, Continuous q' ∧ (∀ r ∈ Set.Icc (0:ℝ) T, q' r = q r) := by
  refine ⟨Set.IccExtend hT ((Set.Icc (0:ℝ) T).restrict q), ?_, ?_⟩
  · exact hq.restrict.Icc_extend'
  · intro r hr
    rw [Set.IccExtend_of_mem hT _ hr]
    rfl

end Sandpile.Support
