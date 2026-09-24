/-
The polynomial moment of the compact-time Brownian maximum, with a constant that
does not depend on the starting point, the horizon or the motion.

`lem:brownian-ball-localization` (`sandpile.tex:1647-1658`) needs the moment bound
uniformly in the starting point, because the supremum over the points of `K` is
taken after the probability.  The tail of `brownian_pathRadius_tail` is uniform in
the starting point and the horizon, so the sum of the tail bounds is a constant.
-/
import Sandpile.Support.ExplBrownianEnvelope

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum
open Sandpile.Support

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem exists_uniform_pathRadius_moment (d : ℕ) (T : ℝ≥0) (p : ℕ) :
    ∃ M : ℝ, ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
      ∀ (x : Space d) (B : ℝ≥0 → Ω → Space d), IsBrownian d x B P →
      (∀ s, Measurable (B s)) → (∀ ω, Continuous fun s => B s ω) →
      ∫ ω, (1 + brownianPathRadius B x T ω) ^ p ∂P ≤ M := by
  obtain ⟨C, c, hC, hc, htail⟩ := brownian_pathRadius_tail d
  refine ⟨max C 1 * ∑' n : ℕ, ((n : ℝ) + 2) ^ p * Real.exp (-(c / (4 * ((T : ℝ) + 1)) * (n : ℝ) ^ 2)), ?_⟩
  intro Ω _ P hP x B hB hm hBc
  let R := brownianPathRadius B x T
  have hR (ω : Ω) : 0 ≤ R ω := (norm_nonneg (B 0 ω - x)).trans
    (norm_le_pathRadius B hBc x T ω (s := 0) zero_le)
  let S : ℕ → Set Ω := fun n => {ω | (n : ℝ) ≤ R ω ∧ R ω < (n : ℝ) + 1}
  have hSm : Measurable (fun ω => R ω) := measurable_pathRadius B hm hBc x T
  have hS (n : ℕ) : MeasurableSet (S n) :=
    (measurableSet_le measurable_const hSm).inter (measurableSet_lt hSm measurable_const)
  have hb (n : ℕ) : ∀ᵐ ω ∂P.restrict (S n), ‖(1 + R ω) ^ p‖ ≤ ((n : ℝ) + 2) ^ p := by
    filter_upwards [ae_restrict_mem (hS n)] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith [hR ω]) p)]
    exact pow_le_pow_left₀ (by linarith [hR ω]) (by dsimp [S] at hω; linarith [hω.2]) p
  have hi (n : ℕ) : IntegrableOn (fun ω => (1 + R ω) ^ p) (S n) P :=
    (integrable_const (((n : ℝ) + 2) ^ p)).mono'
      ((measurable_const.add hSm).pow_const p).aestronglyMeasurable (hb n)
  have hu : (⋃ n, S n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    exact Set.mem_iUnion.mpr ⟨⌊R ω⌋₊, Nat.floor_le (hR ω), Nat.lt_floor_add_one (R ω)⟩
  have htail' (n : ℕ) : P.real {ω | (n : ℝ) ≤ R ω} ≤
      max C 1 * Real.exp (-(c / (4 * ((T : ℝ) + 1)) * (n : ℝ) ^ 2)) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hset : {ω | ((0 : ℕ) : ℝ) ≤ R ω} = Set.univ := by
        ext ω; simp [hR ω]
      rw [hset, Measure.real, measure_univ, ENNReal.toReal_one]
      have he : Real.exp (-(c / (4 * ((T : ℝ) + 1)) * ((0 : ℕ) : ℝ) ^ 2)) = 1 := by
        simp
      rw [he, mul_one]
      exact le_max_right _ _
    · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
      have hsub : {ω | (n : ℝ) ≤ R ω} ⊆ {ω | (n : ℝ) / 2 < R ω} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        have : (n : ℝ) / 2 < (n : ℝ) := by linarith
        linarith
      have hhalf : 0 < (n : ℝ) / 2 := by linarith
      have ht := (measure_mono hsub).trans (htail Ω P hP x B hB hBc T ((n : ℝ) / 2) hhalf)
      have he : -(c * ((n : ℝ) / 2) ^ 2 / ((T : ℝ) + 1)) =
          -(c / (4 * ((T : ℝ) + 1)) * (n : ℝ) ^ 2) := by
        field_simp; ring
      rw [he] at ht
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
      have h1 : P.real {ω | (n : ℝ) ≤ R ω} ≤ C * Real.exp (-(c / (4 * ((T : ℝ) + 1)) * (n : ℝ) ^ 2)) := by
        simpa only [Measure.real, ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.exp_nonneg _))] using hh
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
  have hbound (n : ℕ) : ∫ ω in S n, ‖(1 + R ω) ^ p‖ ∂P ≤
      max C 1 * (((n : ℝ) + 2) ^ p * Real.exp (-(c / (4 * ((T : ℝ) + 1)) * (n : ℝ) ^ 2))) := by
    have hTnn : (0 : ℝ) ≤ (T : ℝ) := T.2
    calc (∫ ω in S n, ‖(1 + R ω) ^ p‖ ∂P)
        ≤ ∫ _ in S n, ((n : ℝ) + 2) ^ p ∂P := integral_mono_ae (hi n).norm (integrable_const _) (hb n)
      _ = ((n : ℝ) + 2) ^ p * P.real (S n) := by
          rw [integral_const, smul_eq_mul, mul_comm, Measure.real, Measure.restrict_apply_univ]
          rfl
      _ ≤ ((n : ℝ) + 2) ^ p * P.real {ω | (n : ℝ) ≤ R ω} := by
          apply mul_le_mul_of_nonneg_left (measureReal_mono (fun ω hω => hω.1)); positivity
      _ ≤ ((n : ℝ) + 2) ^ p * (max C 1 * Real.exp (-(c / (4 * ((T : ℝ) + 1)) * (n : ℝ) ^ 2))) := by
          apply mul_le_mul_of_nonneg_left (htail' n); positivity
      _ = max C 1 * (((n : ℝ) + 2) ^ p * Real.exp (-(c / (4 * ((T : ℝ) + 1)) * (n : ℝ) ^ 2))) := by ring
  have hle (n : ℕ) : ∫ ω in S n, (1 + R ω) ^ p ∂P ≤
      max C 1 * (((n : ℝ) + 2) ^ p * Real.exp (-(c / (4 * ((T : ℝ) + 1)) * (n : ℝ) ^ 2))) := by
    refine (integral_mono_ae (hi n) (hi n).norm (Filter.Eventually.of_forall fun ω => le_abs_self _)).trans ?_
    exact hbound n
  have hsum : Summable (fun n : ℕ => ∫ ω in S n, (1 + R ω) ^ p ∂P) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg fun ω => pow_nonneg (by linarith [hR ω] : (0:ℝ) ≤ 1 + R ω) _) _
      ((summable_polynomial_mul_gaussian p (a := c / (4 * ((T : ℝ) + 1))) (div_pos hc (by positivity))).mul_left (max C 1))
    intro n
    exact hle n
  have hsum' : Summable (fun n : ℕ => ∫ ω in S n, ‖(1 + R ω) ^ p‖ ∂P) := by
    apply hsum.congr
    intro n
    rw [show (fun ω => ‖(1 + R ω) ^ p‖) = fun ω => (1 + R ω) ^ p from funext fun ω =>
      Real.norm_of_nonneg (pow_nonneg (by linarith [hR ω] : (0:ℝ) ≤ 1 + R ω) _)]
  have hh := integrableOn_iUnion_of_summable_integral_norm hi hsum'
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h3
    simp only [S, Set.mem_setOf_eq] at h1 h3
    have hmn1 : m ≤ n := by
      have : (m : ℝ) < (n : ℝ) + 1 := by linarith [h1.1, h3.2]
      have : m < n + 1 := by exact_mod_cast this
      omega
    have hmn2 : n ≤ m := by
      have : (n : ℝ) < (m : ℝ) + 1 := by linarith [h3.1, h1.2]
      have : n < m + 1 := by exact_mod_cast this
      omega
    exact hmn (le_antisymm hmn1 hmn2)
  have hint : ∫ ω, (1 + R ω) ^ p ∂P = ∑' n : ℕ, ∫ ω in S n, (1 + R ω) ^ p ∂P := by
    have h := integral_iUnion hS hdisj hh
    rw [hu] at h
    simpa only [Measure.restrict_univ] using h
  rw [hint]
  calc ∑' n : ℕ, ∫ ω in S n, (1 + R ω) ^ p ∂P
      ≤ ∑' n : ℕ, max C 1 * (((n : ℝ) + 2) ^ p * Real.exp (-(c / (4 * ((T : ℝ) + 1)) * (n : ℝ) ^ 2))) :=
        Summable.tsum_le_tsum hle hsum ((summable_polynomial_mul_gaussian p (a := c / (4 * ((T : ℝ) + 1))) (div_pos hc (by positivity))).mul_left (max C 1))
    _ = max C 1 * ∑' n : ℕ, ((n : ℝ) + 2) ^ p * Real.exp (-(c / (4 * ((T : ℝ) + 1)) * (n : ℝ) ^ 2)) :=
        tsum_mul_left

end Sandpile.Continuum
