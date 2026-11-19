import Sandpile.External.Stopping.WalkInterval

/-!
# A grid cover for path oscillations

A large oscillation on a bounded time interval over a short lag forces a large
excursion from one of finitely many deterministic grid points. This is the
covering step in the modulus-of-continuity estimate for rescaled walks.
-/

open MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace Sandpile.External.Stopping

/-- A pair of nearby times with large separation in a metric space gives a
large excursion from a grid point within two mesh widths. -/
theorem exists_grid_excursion_of_large_dist {E : Type*} [MetricSpace E]
    (f : ℝ≥0 → E) (L ε : ℝ) (δ : ℝ≥0) (hδ : 0 < δ)
    (s t : ℝ≥0) (hs : (s : ℝ) ≤ L)
    (hst : |(s : ℝ) - t| ≤ δ) (hlarge : ε < dist (f s) (f t)) :
    ∃ (k : ℕ) (u : ℝ≥0), k ≤ ⌊L / (δ : ℝ)⌋₊ ∧
      (k : ℝ≥0) * δ ≤ u ∧ (u : ℝ) ≤ (k : ℝ) * δ + 2 * δ ∧
      ε / 2 < dist (f u) (f ((k : ℝ≥0) * δ)) := by
  let m : ℝ≥0 := min s t
  let k : ℕ := ⌊(m : ℝ) / (δ : ℝ)⌋₊
  have hd : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hmL : (m : ℝ) ≤ L := by
    exact le_trans (by exact_mod_cast min_le_left s t) hs
  have hkle : k ≤ ⌊L / (δ : ℝ)⌋₊ := by
    apply Nat.floor_mono
    exact div_le_div_of_nonneg_right hmL hd.le
  have hfloor : (k : ℝ) ≤ (m : ℝ) / δ := Nat.floor_le (div_nonneg m.property hd.le)
  have hnext : (m : ℝ) / δ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hleft : (k : ℝ) * δ ≤ m := (le_div_iff₀ hd).mp hfloor
  have hright : (m : ℝ) < ((k : ℝ) + 1) * δ := (div_lt_iff₀ hd).mp hnext
  have hms : (m : ℝ) ≤ s := by exact_mod_cast min_le_left s t
  have hmt : (m : ℝ) ≤ t := by exact_mod_cast min_le_right s t
  have hst' : (s : ℝ) ≤ (t : ℝ) + δ := by
    have := le_abs_self ((s : ℝ) - t)
    linarith
  have hts' : (t : ℝ) ≤ (s : ℝ) + δ := by
    have := neg_le_of_abs_le hst
    linarith
  have hsm : (s : ℝ) ≤ (m : ℝ) + δ := by
    dsimp [m]
    rw [NNReal.coe_min]
    by_cases h : (s : ℝ) ≤ t
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right (le_of_not_ge h)]
      linarith
  have htm : (t : ℝ) ≤ (m : ℝ) + δ := by
    dsimp [m]
    rw [NNReal.coe_min]
    by_cases h : (s : ℝ) ≤ t
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right (le_of_not_ge h)]
      linarith
  have htri := dist_triangle (f s) (f ((k : ℝ≥0) * δ)) (f t)
  rw [dist_comm (f ((k : ℝ≥0) * δ)) (f t)] at htri
  by_cases h : ε / 2 < dist (f s) (f ((k : ℝ≥0) * δ))
  · refine ⟨k, s, hkle, ?_, ?_, h⟩
    · exact_mod_cast hleft.trans hms
    · linarith
  · refine ⟨k, t, hkle, ?_, ?_, ?_⟩
    · exact_mod_cast hleft.trans hmt
    · linarith
    · linarith [not_lt.mp h]

/-- The probability of a large short-lag oscillation is bounded by the sum
of the probabilities of excursions from the deterministic grid points. -/
theorem measure_modulus_le_sum_grid_excursions {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] (μ : Measure Ω) (f : Ω → ℝ≥0 → E) (L ε : ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    μ {ω | ∃ s t : ℝ≥0, (s : ℝ) ≤ L ∧ (t : ℝ) ≤ L ∧
      |(s : ℝ) - t| ≤ δ ∧ ε < dist (f ω s) (f ω t)} ≤
    ∑ k ∈ Finset.range (⌊L / (δ : ℝ)⌋₊ + 1),
      μ {ω | ∃ u : ℝ≥0, (k : ℝ≥0) * δ ≤ u ∧
        (u : ℝ) ≤ (k : ℝ) * δ + 2 * δ ∧
        ε / 2 < dist (f ω u) (f ω ((k : ℝ≥0) * δ))} := by
  let A : ℕ → Set Ω := fun k => {ω | ∃ u : ℝ≥0, (k : ℝ≥0) * δ ≤ u ∧
    (u : ℝ) ≤ (k : ℝ) * δ + 2 * δ ∧
    ε / 2 < dist (f ω u) (f ω ((k : ℝ≥0) * δ))}
  have hsub : {ω | ∃ s t : ℝ≥0, (s : ℝ) ≤ L ∧ (t : ℝ) ≤ L ∧
      |(s : ℝ) - t| ≤ δ ∧ ε < dist (f ω s) (f ω t)} ⊆
      ⋃ k ∈ Finset.range (⌊L / (δ : ℝ)⌋₊ + 1), A k := by
    intro ω hω
    obtain ⟨s, t, hs, ht, hst, hlarge⟩ := hω
    obtain ⟨k, u, hk, hu, hu', hdist⟩ :=
      exists_grid_excursion_of_large_dist (f ω) L ε δ hδ s t hs hst hlarge
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), ⟨u, hu, hu', hdist⟩⟩⟩
  exact (measure_mono hsub).trans (measure_biUnion_finset_le _ _)

end Sandpile.External.Stopping
