import Sandpile.Support.PathStoppingApproximation
import Sandpile.Support.StopMeasurable
import LatticeProb.Prob.BrownianRestartCanonical

/-!
# Measurable continuation payoffs

A bounded path stopping rule defines a measurable payoff as a function of the
starting point and the continuous future increment path.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- A stopped reward is jointly measurable in the starting point and the
continuous increment path. -/
theorem Sandpile.Support.measurable_continuation_payoff
    {d : ℕ} (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (y : Sandpile.Continuum.Space d)
    (θ : (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0)
    (hθ : IsStoppingTime (LatticeProb.natFiltration
      (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
      (fun t => (measurable_pi_apply t).stronglyMeasurable))
      (fun p => (θ p : ℝ≥0∞))) (hθT : ∀ p, θ p ≤ T) :
    Measurable (fun q : Sandpile.Continuum.Space d × LatticeProb.BrownianPath d =>
      G ((T : ℝ) - θ (fun t => y + q.2 t))
        (q.1 + q.2 (θ (fun t => y + q.2 t)))) := by
  let Z := Sandpile.Continuum.Space d × LatticeProb.BrownianPath d
  let ρ : Z → ℝ≥0 := fun q => θ (fun t => y + q.2 t)
  have hθm : Measurable θ := measurable_coe_nnreal_ennreal_iff.1
    (hθ.measurable.mono hθ.measurableSpace_le le_rfl)
  have hρm : Measurable ρ := hθm.comp (Measurable.of_eval fun t =>
    measurable_const.add ((ContinuousMap.measurable_eval t).comp measurable_snd))
  let X : ℝ≥0 → Z → Sandpile.Continuum.Space d := fun t q => q.1 + q.2 t
  have hXm : ∀ t, Measurable (X t) := fun t =>
    measurable_fst.add ((ContinuousMap.measurable_eval t).comp measurable_snd)
  have hXc : ∀ q, Continuous fun t => X t q := fun q => continuous_const.add q.2.continuous
  have hpos : Measurable (fun q => X (ρ q) q) :=
    Sandpile.Continuum.measurable_stopped_position hXm hXc hρm
  let Gext : ℝ × Sandpile.Continuum.Space d → ℝ :=
    fun q => G (max 0 (min (T : ℝ) q.1)) q.2
  have hGext : Continuous Gext := by
    change Continuous ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘
      fun p : ℝ × Sandpile.Continuum.Space d => (max 0 (min (T : ℝ) p.1), p.2))
    apply hG.comp_continuous
    · exact ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    · intro p
      exact ⟨⟨le_max_left _ _, max_le T.coe_nonneg (min_le_left _ _)⟩, Set.mem_univ _⟩
  have hF : Measurable (fun q : Z => Gext ((T : ℝ) - ρ q, X (ρ q) q)) :=
    hGext.measurable.comp ((measurable_const.sub (measurable_coe_nnreal_real.comp hρm)).prodMk hpos)
  have heq : (fun q : Z => Gext ((T : ℝ) - ρ q, X (ρ q) q)) =
      fun q => G ((T : ℝ) - ρ q) (X (ρ q) q) := by
    funext q
    have h0 : (0 : ℝ) ≤ (T : ℝ) - (ρ q : ℝ) := sub_nonneg.mpr (by exact_mod_cast hθT _)
    have hT : (T : ℝ) - (ρ q : ℝ) ≤ (T : ℝ) := sub_le_self _ (ρ q).coe_nonneg
    simp only [Gext, min_eq_right hT, max_eq_right h0]
  rw [heq] at hF
  exact hF
