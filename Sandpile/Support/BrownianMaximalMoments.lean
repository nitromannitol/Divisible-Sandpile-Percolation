import Sandpile.Support.TailMoment
import LatticeProb.Prob.BrownianLevyReflection
import LatticeProb.Prob.BrownianAbsMoments
import LatticeProb.Prob.GaussSupTailField

/-!
# Brownian maximal moments

The reflection inequality and Gaussian moments control positive integer moments
of a measurable maximum of the Brownian increments.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

/-- A measurable nonnegative random variable whose positive thresholds are
reached by Brownian increments has finite positive integer moments. -/
theorem Sandpile.Support.integrable_pow_of_brownian_max_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (T : ℝ≥0) (M : Ω → ℝ) (hMm : Measurable M) (hM0 : ∀ ω, 0 ≤ M ω)
    (hMlt : ∀ ω (t : ℝ), 0 < t → t < M ω →
      ∃ s ≤ T, t < |B s ω - B 0 ω|)
    (n : ℕ) (hn : 0 < n) : Integrable (fun ω => M ω ^ n) P := by
  apply Sandpile.Support.integrable_pow_of_tail_le P M (fun ω => |B T ω|)
    hMm ((hBm T).abs) hM0 (fun ω => abs_nonneg _) 4 (by norm_num) ?_ n hn
    (LatticeProb.brownian_integrable_abs_pow hB.toIsPreBrownianReal T n)
  intro t ht
  let E : Set Ω := {ω | ∃ s ≤ T, t < B s ω - B 0 ω}
  let F : Set Ω := {ω | ∃ s ≤ T, t < (-B) s ω - (-B) 0 ω}
  have hsub : {ω | t < M ω} ⊆ E ∪ F := by
    intro ω hω
    obtain ⟨s, hs, hlt⟩ := hMlt ω t ht hω
    rcases (lt_abs.mp hlt) with h | h
    · exact Or.inl ⟨s, hs, h⟩
    · exact Or.inr ⟨s, hs, by simp only [Pi.neg_apply]; linarith⟩
  have hE := LatticeProb.measure_exists_lt_le_two_mul hB hBm T t
  have hF := LatticeProb.measure_exists_lt_le_two_mul hB.neg (fun s => (hBm s).neg) T t
  have he1 : P {ω | t ≤ B T ω - B 0 ω} ≤ P {ω | t ≤ |B T ω|} := by
    apply measure_mono_ae
    filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω h
    simp only [hω, sub_zero] at h
    exact h.trans (le_abs_self _)
  have he2 : P {ω | t ≤ (-B) T ω - (-B) 0 ω} ≤ P {ω | t ≤ |B T ω|} := by
    apply measure_mono_ae
    filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω h
    simp only [Pi.neg_apply, hω, neg_zero, sub_zero] at h
    exact h.trans (neg_le_abs _)
  calc
    P {ω | t < M ω} ≤ P (E ∪ F) := measure_mono hsub
    _ ≤ P E + P F := measure_union_le _ _
    _ ≤ 2 * P {ω | t ≤ |B T ω|} + 2 * P {ω | t ≤ |B T ω|} :=
      add_le_add (hE.trans (mul_le_mul' le_rfl he1)) (hF.trans (mul_le_mul' le_rfl he2))
    _ = 4 * P {ω | t ≤ |B T ω|} := by ring

/-- The increments of a continuous real Brownian path up to a finite horizon
have a measurable bound with finite moments of every nonnegative integer order. -/
theorem Sandpile.Support.exists_brownian_increment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0) :
    ∃ M : Ω → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
      (∀ ω t, t ≤ T → |B t ω - B 0 ω| ≤ M ω) ∧
      ∀ n : ℕ, Integrable (fun ω => M ω ^ n) P := by
  let I := Set.Icc (0 : ℝ≥0) T
  have : Nonempty I := ⟨⟨0, ⟨le_rfl, zero_le⟩⟩⟩
  let X : I → Ω → ℝ := fun t ω => |B t ω - B 0 ω|
  have hXc : ∀ ω, Continuous fun t => X t ω := by
    intro ω
    exact (((hBc ω).comp continuous_subtype_val).sub continuous_const).abs
  have hXbdd : ∀ ω, BddAbove (Set.range fun t => X t ω) := by
    intro ω
    let : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
    exact (isCompact_range (hXc ω)).bddAbove
  let M : Ω → ℝ := fun ω => ⨆ t : I, X t ω
  have hMm : Measurable M := by
    have heq : M = fun ω => ⨆ n, X (TopologicalSpace.denseSeq I n) ω := by
      funext ω
      exact LatticeProb.GaussConc.SupTail.iSup_eq_iSup_denseSeq (hXc ω)
        (TopologicalSpace.denseRange_denseSeq I) (hXbdd ω)
    rw [heq]
    exact Measurable.iSup fun n => ((hBm _).sub (hBm 0)).abs
  have hM0 : ∀ ω, 0 ≤ M ω := by
    intro ω
    exact (abs_nonneg _).trans (le_ciSup (hXbdd ω) (Classical.choice inferInstance))
  have hMbound : ∀ ω t, t ≤ T → |B t ω - B 0 ω| ≤ M ω := by
    intro ω t ht
    exact le_ciSup (hXbdd ω) (⟨t, zero_le, ht⟩ : I)
  refine ⟨M, hMm, hM0, hMbound, ?_⟩
  intro n
  by_cases hn : 0 < n
  · apply Sandpile.Support.integrable_pow_of_brownian_max_tail P B hB hBm T M hMm hM0 ?_ n hn
    intro ω t ht hlt
    obtain ⟨s, hs⟩ := exists_lt_of_lt_ciSup hlt
    exact ⟨s, s.property.2, hs⟩
  · have : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simpa only [pow_zero] using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P)
