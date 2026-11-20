import Sandpile.Support.BrownianValueStoppedComparison
import Mathlib.Probability.Martingale.Basic

/-!
# Stopped Brownian value supermartingale

Stopping the continuous Brownian value process at a bounded raw stopping time
preserves its supermartingale property.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

/-- A continuous adapted Brownian value process stopped at a bounded raw stop
is a supermartingale. -/
theorem Sandpile.Support.brownian_value_stopped_supermartingale
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t))
    (x : Sandpile.Continuum.Space d) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (M : ℝ≥0 → Ω → ℝ) (hMm : ∀ s, Measurable (M s))
    (hMc : ∀ ω, Continuous fun s => M s ω)
    (hMad : StronglyAdapted (LatticeProb.natFiltration (B x) (hBm x)) M)
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (LatticeProb.natFiltration (B x) (hBm x))
      (fun ω => (τ ω : ℝ≥0∞))) (hτT : ∀ ω, τ ω ≤ T) :
    Supermartingale (fun s ω => M (min s (τ ω)) ω)
      (LatticeProb.natFiltration (B x) (hBm x)) P := by
  let 𝓕 := LatticeProb.natFiltration (B x) (hBm x)
  let N : ℝ≥0 → Ω → ℝ := fun s ω => M (min s (τ ω)) ω
  have hNad : StronglyAdapted 𝓕 N := by
    have hh := hMad.stoppedProcess hMc hτ
    have he : stoppedProcess M (fun ω => (τ ω : ℝ≥0∞)) = N := by
      funext s ω
      change M (min (s : ℝ≥0∞) (τ ω : ℝ≥0∞)).untopA ω = M (min s (τ ω)) ω
      rw [LatticeProb.untopA_eq_toNNReal ((min_le_left _ _).trans_lt ENNReal.coe_lt_top).ne,
        ← ENNReal.coe_min, ENNReal.toNNReal_coe]
    rwa [he] at hh
  have hτm : Measurable τ := LatticeProb.measurable_of_isStoppingTime hτ
  obtain ⟨_, _, _, hMint⟩ := Sandpile.Support.exists_integrable_brownian_value_process_bound
    P B hB hBc hBm x T G hG hgrow M hMm hMc hMval
  have hNi : ∀ s, Integrable (N s) P := fun s =>
    hMint (fun ω => min s (τ ω)) (measurable_const.min hτm)
      (fun ω => (min_le_right _ _).trans (hτT ω))
  have hneg : Submartingale (-N) 𝓕 P := by
    apply submartingale_of_setIntegral_le hNad.neg (fun s => (hNi s).neg)
    intro s t hst E hE
    let σ : Ω → ℝ≥0 := fun ω => min s (τ ω)
    let ρ : Ω → ℝ≥0 := fun ω => min t (τ ω)
    have hσ : IsStoppingTime 𝓕 (fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) := by
      have hh : IsStoppingTime 𝓕 (fun ω => min ((τ ω : ℝ≥0) : WithTop ℝ≥0)
          (s : WithTop ℝ≥0)) := hτ.min_const s
      rw [show (fun ω => min ((τ ω : ℝ≥0) : WithTop ℝ≥0) (s : WithTop ℝ≥0)) =
          (fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) from funext fun ω => by
        rw [← WithTop.coe_min, min_comm]] at hh
      exact hh
    have hρ : IsStoppingTime 𝓕 (fun ω => ((ρ ω : ℝ≥0) : WithTop ℝ≥0)) := by
      have hh : IsStoppingTime 𝓕 (fun ω => min ((τ ω : ℝ≥0) : WithTop ℝ≥0)
          (t : WithTop ℝ≥0)) := hτ.min_const t
      rw [show (fun ω => min ((τ ω : ℝ≥0) : WithTop ℝ≥0) (t : WithTop ℝ≥0)) =
          (fun ω => ((ρ ω : ℝ≥0) : WithTop ℝ≥0)) from funext fun ω => by
        rw [← WithTop.coe_min, min_comm]] at hh
      exact hh
    let A : Set Ω := E ∩ {ω | s ≤ τ ω}
    have hconst : IsStoppingTime 𝓕 (fun _ : Ω => (s : ℝ≥0∞)) := isStoppingTime_const 𝓕 s
    have hEconst : MeasurableSet[hconst.measurableSpace] E :=
      (hconst.le_measurableSpace_of_const_le (fun _ => le_rfl)) _ hE
    have hA : MeasurableSet[hσ.measurableSpace] A := by
      have hh := hconst.measurableSet_inter_le hτ E hEconst
      have hevent : A = E ∩ {ω | ((s : ℝ≥0) : WithTop ℝ≥0) ≤
          ((τ ω : ℝ≥0) : WithTop ℝ≥0)} := by
        ext ω
        simp only [A, Set.mem_inter_iff, Set.mem_ofPred_eq, WithTop.coe_le_coe]
      rw [IsStoppingTime.measurableSet] at hh ⊢
      constructor
      · rw [hevent]
        exact hh.1
      · intro i
        have hi : {ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)} =
            {ω | min ((s : ℝ≥0) : WithTop ℝ≥0) ((τ ω : ℝ≥0) : WithTop ℝ≥0) ≤
              (i : WithTop ℝ≥0)} := by
          ext ω
          change (((min s (τ ω) : ℝ≥0) : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)) ↔ _
          rw [WithTop.coe_min]
          rfl
        rw [hevent, hi]
        exact hh.2 i
    have hρT : ∀ ω, ρ ω ≤ T := fun ω => (min_le_right _ _).trans (hτT ω)
    have hσρ : ∀ ω ∈ A, σ ω ≤ ρ ω := fun ω _ => min_le_min_right _ hst
    have hh := Sandpile.Support.setIntegral_brownian_value_stopped_le
      P B hB hBc hBm x T G hG hgrow M hMval σ ρ hσ hρ hρT A hA hσρ
    have hEm : MeasurableSet E := 𝓕.le s _ hE
    have heq : (∫ ω in E, (M (ρ ω) ω - M (σ ω) ω) ∂P) =
        ∫ ω in A, (M (ρ ω) ω - M (σ ω) ω) ∂P := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hEm Set.inter_subset_left
      intro ω hω
      have hnot : ¬s ≤ τ ω := by
        intro hh'
        exact hω.2 ⟨hω.1, hh'⟩
      have hτs : τ ω ≤ s := (le_of_not_ge hnot)
      have hτt : τ ω ≤ t := hτs.trans hst
      simp only [σ, ρ, min_eq_right hτs, min_eq_right hτt, sub_self]
    have hle : (∫ ω in E, M (ρ ω) ω ∂P) ≤ ∫ ω in E, M (σ ω) ω ∂P := by
      have hh' : (∫ ω in E, (M (ρ ω) ω - M (σ ω) ω) ∂P) ≤ 0 := heq.trans_le hh
      rw [integral_sub (hNi t).integrableOn (hNi s).integrableOn] at hh'
      linarith
    change (∫ ω in E, -M (σ ω) ω ∂P) ≤ ∫ ω in E, -M (ρ ω) ω ∂P
    rw [integral_neg, integral_neg]
    linarith
  simpa only [N, neg_neg] using hneg.neg
