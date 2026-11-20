import Sandpile.External.Stopping.CubeConstraintWeakLimit

/-!
# Translated cube constraints under weak convergence

Closed-cube constraints centered at any fixed point pass to weak limits of
continuous path-clock laws.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Continuous paths which remain in a cube about `a` strictly before the
marked time. -/
def translatedCubeConstrainedPaths {d : ℕ} (a : Continuum.Space d) (L : ℝ) :
    Set (C(ℝ≥0, Continuum.Space d) × ℝ≥0) :=
  {p | ∀ t < p.2, ∀ i, |p.1 t i - a i| ≤ L}

/-- The pre-stop constraint for a translated closed cube is closed. -/
theorem isClosed_translatedCubeConstrainedPaths {d : ℕ} (a : Continuum.Space d) (L : ℝ) :
    IsClosed (translatedCubeConstrainedPaths a L) := by
  have heq : translatedCubeConstrainedPaths a L =
      ⋂ t : ℝ≥0, ⋂ i : Fin d, {p : C(ℝ≥0, Continuum.Space d) × ℝ≥0 |
        p.2 ≤ t ∨ |p.1 t i - a i| ≤ L} := by
    ext p
    simp only [translatedCubeConstrainedPaths, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h t i
      by_cases ht : t < p.2
      · exact Or.inr (h t ht i)
      · exact Or.inl (le_of_not_gt ht)
    · intro h t ht i
      exact (h t i).resolve_left (not_le_of_gt ht)
  rw [heq]
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro i
  apply IsClosed.union
  · exact isClosed_le (NNReal.continuous_coe.comp continuous_snd) continuous_const
  · exact isClosed_le ((((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp
      ((continuous_eval_const t).comp continuous_fst)).sub continuous_const).abs) continuous_const

/-- Translated pre-stop cube constraints pass to weak limits when the excess
width tends to zero. -/
theorem ae_translated_cube_constraint_of_tendsto_probabilityMeasure
    {d : ℕ} (μn : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0))
    (μ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0))
    (hμ : Tendsto μn atTop (𝓝 μ)) (a : Continuum.Space d) (L : ℝ)
    (hfull : ∀ ε > 0, ∀ᶠ n in atTop, ∀ᵐ p ∂(μn n : Measure _),
      p ∈ translatedCubeConstrainedPaths a (L + ε)) :
    ∀ᵐ p ∂(μ : Measure _), p ∈ translatedCubeConstrainedPaths a L := by
  have hall : ∀ k : ℕ, ∀ᵐ p ∂(μ : Measure _),
      p ∈ translatedCubeConstrainedPaths a (L + 1 / ((k : ℝ) + 1)) := by
    intro k
    apply ae_mem_closed_of_tendsto_probabilityMeasure μn μ hμ _ (isClosed_translatedCubeConstrainedPaths _ _)
    exact hfull _ (by positivity)
  filter_upwards [ae_all_iff.mpr hall] with p hp
  intro t ht i
  have hlim : Tendsto (fun k : ℕ => L + 1 / ((k : ℝ) + 1)) atTop (𝓝 L) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := L)).add tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun k => hp k t ht i)

end Sandpile.External.Stopping
