/-
Bounds for the interpolated odometer over a bounded interval of scales. Only
finitely many times and lattice sites are involved, and a bound for their values
bounds both the interpolants and their Lipschitz constants.
-/
import Sandpile.Support.MainExplInterpRegularity
import Sandpile.Support.MainExplInterp
import Sandpile.Support.Kernel

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal
open Sandpile.Continuum

namespace Sandpile.Support

/-- A finite collection of odometer values is bounded outside an event of any
prescribed positive probability. -/
theorem exists_finite_odometer_bound (d : ℕ) (P : Measure (Site d → ℝ)) [IsProbabilityMeasure P]
    (N J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (M : ℝ) (G : Set (Site d → ℝ)), 0 < M ∧ P Gᶜ ≤ ENNReal.ofReal ε ∧
      ∀ σ ∈ G, ∀ n ≤ N, ∀ y ∈ boxFinset (0 : Site d) J, |odometer σ n y| ≤ M := by
  classical
  let A : (Site d → ℝ) → ℝ := fun σ =>
    ∑ n ∈ Finset.range (N + 1), ∑ y ∈ boxFinset (0 : Site d) J, |odometer σ n y|
  have hAm : Measurable A := by
    exact Finset.measurable_sum _ fun n _ => Finset.measurable_sum _ fun y _ =>
      (measurable_odometer n y).abs
  let E : ℕ → Set (Site d → ℝ) := fun m => {σ | (m : ℝ) < A σ}
  have hEm : ∀ m, MeasurableSet (E m) := fun m => measurableSet_lt measurable_const hAm
  have hEanti : Antitone E := by
    intro m n hmn σ hσ
    exact lt_of_le_of_lt (Nat.cast_le.mpr hmn : (m : ℝ) ≤ n) hσ
  have hEempty : (⋂ m, E m) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro σ hσ
    obtain ⟨m, hm⟩ := exists_nat_gt (A σ)
    exact (not_lt_of_ge hm.le) (Set.mem_iInter.mp hσ m)
  have ht := tendsto_measure_iInter_atTop (fun m => (hEm m).nullMeasurableSet) hEanti
    ⟨0, measure_ne_top P _⟩
  rw [hEempty, measure_empty] at ht
  obtain ⟨m, hm⟩ := (ht.eventually_lt_const (ENNReal.ofReal_pos.mpr hε)).exists
  refine ⟨(m : ℝ) + 1, {σ | A σ ≤ (m : ℝ)}, by positivity, ?_, ?_⟩
  · simpa only [Set.compl_setOf, not_le, Function.comp_apply, E] using hm.le
  · intro σ hσ n hn y hy
    have h₁ : |odometer σ n y| ≤ ∑ z ∈ boxFinset (0 : Site d) J, |odometer σ n z| :=
      Finset.single_le_sum (fun z _ => abs_nonneg (odometer σ n z)) hy
    have h₂ : (∑ z ∈ boxFinset (0 : Site d) J, |odometer σ n z|) ≤ A σ :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun z _ => abs_nonneg (odometer σ k z))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    exact (h₁.trans (h₂.trans hσ)).trans (by linarith)

/-- Bounds on a compact set and on the scale place every interpolation corner
in one fixed finite lattice box. -/
theorem interpolation_corner_mem_box {d : ℕ} (L ρ : ℝ) (_hL : 1 ≤ L) (hρ : 0 ≤ ρ)
    (R : ℝ) (hR : 1 ≤ R) (hRL : R ≤ L) (z : Space d) (hz : ‖z‖ ≤ ρ)
    (e : Fin d → Bool) :
    (fun i => ⌊R * z i⌋ + if e i then 1 else 0) ∈
      boxFinset (0 : Site d) ⌈L * ρ + 2⌉₊ := by
  apply mem_boxFinset
  apply Finset.sup_le
  intro i _
  have hzi := abs_le.mp ((abs_coord_le_norm z i).trans hz)
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hl := mul_le_mul_of_nonneg_left hzi.1 hR0
  have hu := mul_le_mul_of_nonneg_left hzi.2 hR0
  have hLR := mul_le_mul_of_nonneg_right hRL hρ
  have hfl := Int.floor_le (R * z i)
  have hfl' := Int.lt_floor_add_one (R * z i)
  have hceil := Nat.le_ceil (L * ρ + 2)
  have habs : |((⌊R * z i⌋ : ℤ) : ℝ) + (if e i then 1 else 0)| ≤ (⌈L * ρ + 2⌉₊ : ℝ) := by
    cases e i <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;>
      rw [abs_le] <;> constructor <;> linarith
  have hcast : (((0 : Site d) i - (⌊R * z i⌋ + if e i then 1 else 0)).natAbs : ℝ) =
      |((⌊R * z i⌋ : ℤ) : ℝ) + (if e i then 1 else 0)| := by
    simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg, Nat.cast_natAbs]
    cases e i <;> norm_num
  exact_mod_cast (hcast ▸ habs)

/-- Over a bounded scale interval, the interpolated odometer has uniformly
bounded values and Lipschitz constants with arbitrarily high probability. -/
theorem exists_bounded_scale_interpolation_bound
    (d : ℕ) (hd3 : d ≤ 3) (P : Measure (Site d → ℝ)) [IsProbabilityMeasure P]
    (T L : ℝ) (hT : 0 < T) (hL : 1 ≤ L)
    (K : Set (Space d)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ (M C : ℝ) (G : Set (Site d → ℝ)), 0 < M ∧ 0 ≤ C ∧ P Gᶜ ≤ ENNReal.ofReal ε ∧
      ∀ σ ∈ G, ∀ R : ℝ, 1 ≤ R → R ≤ L →
        (∀ z ∈ K, |multilinearInterp R
          (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z| ≤ M) ∧
        (∀ z ∈ K, ∀ z' ∈ K,
          |multilinearInterp R
            (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z -
            multilinearInterp R
            (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z'|
            ≤ C * dist z z') := by
  classical
  obtain ⟨ρ, hρ, hKρ⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : Space d)
  obtain ⟨M, G, hM, hG, hbound⟩ := exists_finite_odometer_bound d P ⌊T * L ^ 2⌋₊
    ⌈L * ρ + 2⌉₊ ε hε
  refine ⟨M, 2 * M * (d : ℝ) * L, G, hM, by positivity, hG, ?_⟩
  intro σ hσ R hR hRL
  have hRp : 0 < R := lt_of_lt_of_le one_pos hR
  have htime : ⌊T * R ^ 2⌋₊ ≤ ⌊T * L ^ 2⌋₊ := by
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left (sq_le_sq₀ hRp.le (by linarith) |>.mpr hRL) hT.le
  have hp0 : 0 ≤ R ^ (-(2 - (d : ℝ) / 2)) := Real.rpow_nonneg hRp.le _
  have hp1 : R ^ (-(2 - (d : ℝ) / 2)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hR
    have hd : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
    linarith
  let f : Site d → ℝ := fun y => if y ∈ boxFinset (0 : Site d) ⌈L * ρ + 2⌉₊ then
    R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y else 0
  have hf : ∀ y, |f y| ≤ M := by
    intro y
    by_cases hy : y ∈ boxFinset (0 : Site d) ⌈L * ρ + 2⌉₊
    · simp only [f, if_pos hy, abs_mul, abs_of_nonneg hp0]
      calc _ ≤ 1 * M := mul_le_mul hp1 (hbound σ hσ _ htime y hy) (abs_nonneg _) zero_le_one
        _ = M := one_mul _
    · simpa only [f, if_neg hy, abs_zero] using hM.le
  have heq : ∀ z ∈ K, multilinearInterp R
      (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z =
      multilinearInterp R f z := by
    intro z hz
    have hzn : ‖z‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hKρ hz
    unfold multilinearInterp
    apply Finset.sum_congr rfl
    intro e _
    rw [show f (fun i => ⌊R * z i⌋ + if e i then 1 else 0) = _ from
      if_pos (interpolation_corner_mem_box L ρ hL hρ.le R hR hRL z hzn e)]
  constructor
  · intro z hz
    rw [heq z hz]
    exact abs_multilinearInterp_le R f z M hf
  · intro z hz z' hz'
    rw [heq z hz, heq z' hz']
    calc _ ≤ 2 * M * (d : ℝ) * |R| * dist z z' := abs_multilinearInterp_sub_le R f M hf z z'
      _ ≤ (2 * M * (d : ℝ) * L) * dist z z' := by
        rw [abs_of_pos hRp]
        gcongr

end Sandpile.Support
