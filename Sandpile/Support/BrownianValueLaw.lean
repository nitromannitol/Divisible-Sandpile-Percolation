import Sandpile.Support.BrownianPolynomialReward
import Sandpile.Support.PathStoppingPayoffLaw
import LatticeProb.Prob.BrownianRestartLaw

/-!
# Stopping values and continuous path laws

Continuous processes with the same path law have the same finite-horizon
stopping value when the comparison process is Brownian and rewards have
polynomial growth.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The stopping value of a continuous process is bounded by that of a Brownian
process with the same continuous-path law. -/
theorem Sandpile.Support.snellValue_le_of_continuousPathLaw
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {d : ℕ}
    (x₂ : Sandpile.Continuum.Space d)
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (B₁ : ℝ≥0 → Ω₁ → Sandpile.Continuum.Space d)
    (B₂ : ℝ≥0 → Ω₂ → Sandpile.Continuum.Space d)
    (hB₂ : Sandpile.Continuum.IsBrownian d x₂ B₂ P₂)
    (hBm₁ : ∀ t, StronglyMeasurable (B₁ t)) (hBm₂ : ∀ t, StronglyMeasurable (B₂ t))
    (hBc₁ : ∀ ω, Continuous fun t => B₁ t ω) (hBc₂ : ∀ ω, Continuous fun t => B₂ t ω)
    (hlaw : P₁.map (fun ω => (⟨fun t => B₁ t ω, hBc₁ ω⟩ : C(ℝ≥0, Sandpile.Continuum.Space d))) =
      P₂.map (fun ω => (⟨fun t => B₂ t ω, hBc₂ ω⟩ : C(ℝ≥0, Sandpile.Continuum.Space d))))
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k) :
    Sandpile.External.Snell.snellValue B₁ P₁ G T ≤
      Sandpile.External.Snell.snellValue B₂ P₂ G T := by
  have hne : {a : ℝ | ∃ σ : Ω₁ → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B₁ σ ∧
      (∀ ω, (σ ω : ℝ) ≤ (T : ℝ)) ∧
      a = ∫ ω, G ((T : ℝ) - σ ω) (B₁ (σ ω) ω) ∂P₁}.Nonempty := by
    refine ⟨∫ ω, G T (B₁ 0 ω) ∂P₁, (fun _ => 0),
      Sandpile.Continuum.isBrownianStopping_const B₁ 0, ?_, ?_⟩
    · intro ω
      exact T.coe_nonneg
    · simp only [NNReal.coe_zero, sub_zero]
  change sSup {a : ℝ | ∃ σ : Ω₁ → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B₁ σ ∧
      (∀ ω, (σ ω : ℝ) ≤ (T : ℝ)) ∧
      a = ∫ ω, G ((T : ℝ) - σ ω) (B₁ (σ ω) ω) ∂P₁} ≤ _
  apply csSup_le hne
  rintro a ⟨τ, hτ, hτT, rfl⟩
  have hτT' : ∀ ω, τ ω ≤ T := fun ω => by exact_mod_cast hτT ω
  obtain ⟨θ, hθ, hθT, hθeq⟩ :=
    Sandpile.Support.exists_path_stoppingTime_of_brownianStopping P₁ B₁ hBm₁ τ hτ T hτT'
  have hθm : Measurable θ := measurable_coe_nnreal_ennreal_iff.1
    (hθ.measurable.mono hθ.measurableSpace_le le_rfl)
  let τ₂ : Ω₂ → ℝ≥0 := fun ω => θ (fun t => B₂ t ω)
  have hτ₂rc : IsStoppingTime (LatticeProb.natFiltration B₂ hBm₂).rightCont
      (fun ω => (τ₂ ω : ℝ≥0∞)) :=
    Sandpile.Support.isStoppingTime_path_comp_rightCont B₂ hBm₂ θ hθ
  have hτ₂aug : IsStoppingTime
      (Sandpile.Support.aeCompletedFiltration P₂ (LatticeProb.natFiltration B₂ hBm₂)).rightCont
      (fun ω => (τ₂ ω : ℝ≥0∞)) :=
    Sandpile.Support.isStoppingTime_usualAugmentation_of_rightCont P₂ _ τ₂ hτ₂rc
  have hI : (∫ ω, G ((T : ℝ) - τ ω) (B₁ (τ ω) ω) ∂P₁) =
      ∫ ω, G ((T : ℝ) - τ₂ ω) (B₂ (τ₂ ω) ω) ∂P₂ := by
    calc
      _ = ∫ ω, G ((T : ℝ) - (θ (fun t => B₁ t ω) : ℝ))
          (B₁ (θ (fun t => B₁ t ω)) ω) ∂P₁ := by
        apply integral_congr_ae
        filter_upwards [hθeq] with ω hω
        rw [hω]
      _ = _ := Sandpile.Support.integral_path_stopping_payoff_eq_of_law
        P₁ P₂ B₁ B₂ hBm₁ hBm₂ hBc₁ hBc₂ hlaw T G hG θ hθm hθT
  rw [hI, Sandpile.Support.snellValue_eq_sSup_usualAugmentation x₂ P₂ B₂ hB₂ hBm₂ hBc₂ T G hG hgrow]
  apply le_csSup (Sandpile.Support.bddAbove_augmented_brownian_payoffs x₂ P₂ B₂ hB₂ hBm₂ hBc₂ T G hG hgrow)
  exact ⟨τ₂, hτ₂aug, (fun ω => hθT (fun t => B₂ t ω)), rfl⟩

/-- Brownian motions with the same continuous-path law have the same stopping
value for a continuous reward of polynomial growth. -/
theorem Sandpile.Support.snellValue_eq_of_continuousPathLaw
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {d : ℕ}
    (x₁ x₂ : Sandpile.Continuum.Space d)
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (B₁ : ℝ≥0 → Ω₁ → Sandpile.Continuum.Space d)
    (B₂ : ℝ≥0 → Ω₂ → Sandpile.Continuum.Space d)
    (hB₁ : Sandpile.Continuum.IsBrownian d x₁ B₁ P₁)
    (hB₂ : Sandpile.Continuum.IsBrownian d x₂ B₂ P₂)
    (hBm₁ : ∀ t, StronglyMeasurable (B₁ t)) (hBm₂ : ∀ t, StronglyMeasurable (B₂ t))
    (hBc₁ : ∀ ω, Continuous fun t => B₁ t ω) (hBc₂ : ∀ ω, Continuous fun t => B₂ t ω)
    (hlaw : P₁.map (fun ω => (⟨fun t => B₁ t ω, hBc₁ ω⟩ : C(ℝ≥0, Sandpile.Continuum.Space d))) =
      P₂.map (fun ω => (⟨fun t => B₂ t ω, hBc₂ ω⟩ : C(ℝ≥0, Sandpile.Continuum.Space d))))
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k) :
    Sandpile.External.Snell.snellValue B₁ P₁ G T =
      Sandpile.External.Snell.snellValue B₂ P₂ G T := by
  apply le_antisymm
  · exact Sandpile.Support.snellValue_le_of_continuousPathLaw x₂ P₁ P₂ B₁ B₂ hB₂
      hBm₁ hBm₂ hBc₁ hBc₂ hlaw T G hG hgrow
  · exact Sandpile.Support.snellValue_le_of_continuousPathLaw x₁ P₂ P₁ B₂ B₁ hB₁
      hBm₂ hBm₁ hBc₂ hBc₁ hlaw.symm T G hG hgrow

/-- Continuous Brownian motions started at the same point have the same
continuous-path law. -/
theorem Sandpile.Support.brownian_continuousPathLaw_eq
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {d : ℕ}
    (x : Sandpile.Continuum.Space d)
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (B₁ : ℝ≥0 → Ω₁ → Sandpile.Continuum.Space d)
    (B₂ : ℝ≥0 → Ω₂ → Sandpile.Continuum.Space d)
    (hB₁ : Sandpile.Continuum.IsBrownian d x B₁ P₁)
    (hB₂ : Sandpile.Continuum.IsBrownian d x B₂ P₂)
    (hBm₁ : ∀ t, StronglyMeasurable (B₁ t)) (hBm₂ : ∀ t, StronglyMeasurable (B₂ t))
    (hBc₁ : ∀ ω, Continuous fun t => B₁ t ω) (hBc₂ : ∀ ω, Continuous fun t => B₂ t ω) :
    P₁.map (fun ω => (⟨fun t => B₁ t ω, hBc₁ ω⟩ : C(ℝ≥0, Sandpile.Continuum.Space d))) =
      P₂.map (fun ω => (⟨fun t => B₂ t ω, hBc₂ ω⟩ : C(ℝ≥0, Sandpile.Continuum.Space d))) := by
  let hL₁ : LatticeProb.IsBrownianSpace d x B₁ P₁ := ⟨hB₁.start, hB₁.coord, hB₁.indep⟩
  let hL₂ : LatticeProb.IsBrownianSpace d x B₂ P₂ := ⟨hB₂.start, hB₂.coord, hB₂.indep⟩
  let shift : LatticeProb.BrownianPath d → LatticeProb.BrownianPath d :=
    fun p => ContinuousMap.const _ x + p
  have hshift : Measurable shift := ContinuousMap.measurable_iff_eval.mpr fun t =>
    measurable_const.add (ContinuousMap.measurable_eval t)
  have hr₁ := LatticeProb.measurable_restartPath hBm₁ hBc₁ (τ := fun _ => 0) measurable_const
  have hr₂ := LatticeProb.measurable_restartPath hBm₂ hBc₂ (τ := fun _ => 0) measurable_const
  have hmap₁ : P₁.map (fun ω => (⟨fun t => B₁ t ω, hBc₁ ω⟩ : LatticeProb.BrownianPath d)) =
      (P₁.map (LatticeProb.restartPath B₁ hBc₁ fun _ => 0)).map shift := by
    rw [Measure.map_map hshift hr₁]
    apply Measure.map_congr
    filter_upwards [hB₁.start] with ω hω
    ext t : 1
    change B₁ t ω = x + (B₁ (0 + t) ω - B₁ 0 ω)
    rw [zero_add, hω]
    abel
  have hmap₂ : P₂.map (fun ω => (⟨fun t => B₂ t ω, hBc₂ ω⟩ : LatticeProb.BrownianPath d)) =
      (P₂.map (LatticeProb.restartPath B₂ hBc₂ fun _ => 0)).map shift := by
    rw [Measure.map_map hshift hr₂]
    apply Measure.map_congr
    filter_upwards [hB₂.start] with ω hω
    ext t : 1
    change B₂ t ω = x + (B₂ (0 + t) ω - B₂ 0 ω)
    rw [zero_add, hω]
    abel
  rw [hmap₁, hmap₂, hL₁.map_restartPath_zero_eq hL₂ hBc₁ hBc₂]

/-- The finite-horizon Brownian stopping value depends only on the starting
point and not on the chosen Brownian realization. -/
theorem Sandpile.Support.snellValue_eq_of_isBrownian
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {d : ℕ}
    (x : Sandpile.Continuum.Space d)
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (B₁ : ℝ≥0 → Ω₁ → Sandpile.Continuum.Space d)
    (B₂ : ℝ≥0 → Ω₂ → Sandpile.Continuum.Space d)
    (hB₁ : Sandpile.Continuum.IsBrownian d x B₁ P₁)
    (hB₂ : Sandpile.Continuum.IsBrownian d x B₂ P₂)
    (hBm₁ : ∀ t, StronglyMeasurable (B₁ t)) (hBm₂ : ∀ t, StronglyMeasurable (B₂ t))
    (hBc₁ : ∀ ω, Continuous fun t => B₁ t ω) (hBc₂ : ∀ ω, Continuous fun t => B₂ t ω)
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k) :
    Sandpile.External.Snell.snellValue B₁ P₁ G T =
      Sandpile.External.Snell.snellValue B₂ P₂ G T := by
  exact Sandpile.Support.snellValue_eq_of_continuousPathLaw x x P₁ P₂ B₁ B₂ hB₁ hB₂
    hBm₁ hBm₂ hBc₁ hBc₂
    (Sandpile.Support.brownian_continuousPathLaw_eq x P₁ P₂ B₁ B₂ hB₁ hB₂
      hBm₁ hBm₂ hBc₁ hBc₂) T G hG hgrow
