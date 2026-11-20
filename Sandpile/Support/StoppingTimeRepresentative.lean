import Sandpile.Support.DelayedStopping
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Representatives of stopping times

Threshold events with representatives in a filtration determine a bounded
stopping time of its right-continuation.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- Countable dense threshold representatives determine an almost-everywhere equal
bounded stopping time in the right-continuation filtration. -/
theorem Sandpile.Support.exists_stoppingTime_rightCont_of_threshold_representatives
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (D : ℕ → ℝ≥0)
    (hD : ∀ a b : ℝ≥0, a < b → ∃ n, a < D n ∧ D n < b)
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet[𝓕 (D n)] (A n))
    (hAE : ∀ n, ∀ᵐ ω ∂P, ω ∈ A n ↔ τ ω < D n) :
    ∃ θ : Ω → ℝ≥0,
      IsStoppingTime 𝓕.rightCont (fun ω => (θ ω : ℝ≥0∞)) ∧
      (∀ ω, θ ω ≤ T) ∧ θ =ᵐ[P] τ := by
  classical
  let ρ : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if ω ∈ A n ∧ D n ≤ T then (D n : ℝ≥0∞) else (T : ℝ≥0∞)
  have hρ_stop : ∀ n, IsStoppingTime 𝓕.rightCont (ρ n) := by
    intro n
    by_cases hn : D n ≤ T
    · have hm : MeasurableSet[𝓕.rightCont (D n)] (A n) :=
        𝓕.le_rightCont (D n) _ (hA n)
      have hh := isStoppingTime_piecewise_const (𝒢 := 𝓕.rightCont) hn hm
      have he : ρ n = (A n).piecewise (fun _ => (D n : ℝ≥0∞)) (fun _ => (T : ℝ≥0∞)) := by
        funext ω
        simp only [ρ, hn, and_true, Set.piecewise]
      rw [he]
      exact hh
    · have hh := isStoppingTime_const 𝓕.rightCont T
      have he : ρ n = fun _ => (T : ℝ≥0∞) := by
        funext ω
        simp only [ρ, hn, and_false, ↓reduceIte]
      rw [he]
      exact hh
  let ξ : Ω → ℝ≥0∞ := fun ω => ⨅ n, ρ n ω
  have hξ_stop : IsStoppingTime 𝓕.rightCont ξ := IsStoppingTime.iInf hρ_stop
  have hξ_le : ∀ ω, ξ ω ≤ (T : ℝ≥0∞) := by
    intro ω
    apply le_trans (iInf_le (fun n => ρ n ω) 0)
    dsimp [ρ]
    split_ifs with h
    · exact_mod_cast h.2
    · rfl
  let θ : Ω → ℝ≥0 := fun ω => (ξ ω).toNNReal
  have hθ : ∀ ω, (θ ω : ℝ≥0∞) = ξ ω := fun ω =>
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (hξ_le ω))
  refine ⟨θ, ?_, ?_, ?_⟩
  · simpa only [hθ] using hξ_stop
  · intro ω
    exact ENNReal.coe_le_coe.mp ((hθ ω).le.trans (hξ_le ω))
  · filter_upwards [ae_all_iff.mpr hAE] with ω hω
    apply le_antisymm
    · by_contra hnot
      have hlt : τ ω < θ ω := lt_of_not_ge hnot
      have hτlt : τ ω < T := lt_of_lt_of_le hlt (ENNReal.coe_le_coe.mp ((hθ ω).le.trans (hξ_le ω)))
      obtain ⟨n, han, hnb⟩ := hD (τ ω) (min (θ ω) T) (lt_min hlt hτlt)
      have hnT : D n ≤ T := (lt_of_lt_of_le hnb (min_le_right _ _)).le
      have hnθ : D n < θ ω := lt_of_lt_of_le hnb (min_le_left _ _)
      have hmem : ω ∈ A n := (hω n).2 han
      have hle : ξ ω ≤ (D n : ℝ≥0∞) := by
        calc
          ξ ω ≤ ρ n ω := iInf_le _ n
          _ = (D n : ℝ≥0∞) := by simp only [ρ, hmem, hnT, and_self, ↓reduceIte]
      have : θ ω ≤ D n := ENNReal.coe_le_coe.mp ((hθ ω).le.trans hle)
      exact (not_le_of_gt hnθ) this
    · have hle : (τ ω : ℝ≥0∞) ≤ ξ ω := by
        apply le_iInf
        intro n
        dsimp [ρ]
        split_ifs with hn
        · exact_mod_cast (hω n).1 hn.1 |>.le
        · exact_mod_cast hτT ω
      exact ENNReal.coe_le_coe.mp (hle.trans (hθ ω).ge)

/-- If every strict threshold event has a representative at that time, the
bounded time has an almost-everywhere equal right-continuation stopping time. -/
theorem Sandpile.Support.exists_stoppingTime_rightCont_of_thresholds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hrep : ∀ t, ∃ A : Set Ω, MeasurableSet[𝓕 t] A ∧
      ∀ᵐ ω ∂P, ω ∈ A ↔ τ ω < t) :
    ∃ θ : Ω → ℝ≥0,
      IsStoppingTime 𝓕.rightCont (fun ω => (θ ω : ℝ≥0∞)) ∧
      (∀ ω, θ ω ≤ T) ∧ θ =ᵐ[P] τ := by
  classical
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  have hdense : ∀ a b : ℝ≥0, a < b → ∃ n, a < D n ∧ D n < b := by
    intro a b hab
    obtain ⟨x, hx⟩ := exists_between hab
    obtain ⟨n, hn⟩ := hD.exists_mem_open isOpen_Ioo ⟨x, hx⟩
    exact ⟨n, hn.1, hn.2⟩
  choose A hA hAE using fun n => hrep (D n)
  exact Sandpile.Support.exists_stoppingTime_rightCont_of_threshold_representatives
    P 𝓕 τ T hτT D hdense A hA hAE

/-- Threshold representatives give bounded stopping times of the original
filtration that converge almost surely to the given bounded time. -/
theorem Sandpile.Support.exists_stoppingTime_seq_tendsto_of_thresholds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hrep : ∀ t, ∃ A : Set Ω, MeasurableSet[𝓕 t] A ∧
      ∀ᵐ ω ∂P, ω ∈ A ↔ τ ω < t) :
    ∃ σ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime 𝓕 (fun ω => (σ n ω : ℝ≥0∞))) ∧
      (∀ n ω, σ n ω ≤ T) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω))) := by
  obtain ⟨θ, hθstop, hθT, hθeq⟩ :=
    Sandpile.Support.exists_stoppingTime_rightCont_of_thresholds P 𝓕 τ T hτT hrep
  obtain ⟨σ, hσstop, hσT, hσlim⟩ :=
    Sandpile.Support.exists_stoppingTime_seq_tendsto_of_rightCont 𝓕 θ hθstop T hθT
  refine ⟨σ, hσstop, hσT, ?_⟩
  filter_upwards [hθeq] with ω hω
  simpa only [← hω] using hσlim ω

/-- If each past stopping event has a representative in every later filtration
space, a bounded time is the almost-sure limit of bounded stopping times. -/
theorem Sandpile.Support.exists_stoppingTime_seq_tendsto_of_future_representatives
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hcomp : ∀ s t : ℝ≥0, s < t → ∃ A : Set Ω, MeasurableSet[𝓕 t] A ∧
      ∀ᵐ ω ∂P, ω ∈ A ↔ τ ω ≤ s) :
    ∃ σ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime 𝓕 (fun ω => (σ n ω : ℝ≥0∞))) ∧
      (∀ n ω, σ n ω ≤ T) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω))) := by
  classical
  apply Sandpile.Support.exists_stoppingTime_seq_tendsto_of_thresholds P 𝓕 τ T hτT
  intro t
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  let A : ℕ → Set Ω := fun n =>
    if hn : D n < t then Classical.choose (hcomp (D n) t hn) else ∅
  have hA : ∀ n, MeasurableSet[𝓕 t] (A n) := by
    intro n
    dsimp [A]
    split_ifs with hn
    · exact (Classical.choose_spec (hcomp (D n) t hn)).1
    · exact @MeasurableSet.empty Ω (𝓕 t)
  have hAe : ∀ n, ∀ᵐ ω ∂P, ω ∈ A n ↔ D n < t ∧ τ ω ≤ D n := by
    intro n
    by_cases hn : D n < t
    · simpa [A, hn] using
        (Classical.choose_spec (hcomp (D n) t hn)).2
    · filter_upwards [] with ω
      simp [A, hn]
  refine ⟨⋃ n, A n, MeasurableSet.iUnion hA, ?_⟩
  filter_upwards [ae_all_iff.mpr hAe] with ω hω
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨n, hn⟩
    exact lt_of_le_of_lt ((hω n).1 hn).2 ((hω n).1 hn).1
  · intro ht
    obtain ⟨x, hx⟩ := exists_between ht
    obtain ⟨n, hn⟩ := hD.exists_mem_open isOpen_Ioo ⟨x, hx⟩
    exact ⟨n, (hω n).2 ⟨hn.2, hn.1.le⟩⟩
