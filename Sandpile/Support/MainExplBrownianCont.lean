import Sandpile.Continuum.BrownianExists
import LatticeProb.Prob.BrownianContAll

/-!
# Brownian motion on `ℝ^d` with every path continuous

Brownian motion on `ℝ^d`, started at every point of space at once on one probability space,
with EVERY path continuous and with strongly measurable values at each time.

`Sandpile.Continuum.exists_isBrownian` produces the family with the three clauses of
`Sandpile.Continuum.IsBrownian`, and `IsBrownian` gives continuity of the paths only almost
surely, through `IsBrownianReal.cont`. The Brownian half of `thm:main-explosion`(i)(b) needs
more: the reward is the Gaussian potential, which is unbounded on the strip, so the attainable
stopped payoffs are bounded above and integrable only through an envelope built from the maximal
displacement, whose measurability reads the path at every sample point. The same two facts are
what `lem:brownian-ball-localization` carries beside its `IsBrownian`.

They are not an extra assumption on the motion. The shared library proves Kolmogorov-Chentsov in
the form that makes every path continuous, and the construction of the family is the one
`exists_isBrownian` uses: `d` independent copies of a real motion with every path continuous,
each scaled by `1/√d` and translated by the starting point. Translating does not change the
space, so one space carries the whole family, and continuity and measurability pass through the
scaling and the translation coordinatewise.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- **Brownian motion on `ℝ^d` with every path continuous exists**, started at every
point of space at once on one probability space: the family has the three clauses of
`Sandpile.Continuum.IsBrownian` at each starting point, every one of its paths is
continuous, and its value at each time is strongly measurable. -/
theorem Sandpile.Continuum.exists_isBrownian_cont (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d),
      (∀ x : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d x (B x) P) ∧
      (∀ (y : Sandpile.Continuum.Space d) (ω : Ω), Continuous fun s => B y s ω) ∧
      (∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) := by
  obtain ⟨Ω₀, mΩ₀, P₀, C, hCm, hC, hCcont⟩ := LatticeProb.exists_isBrownianReal_cont
  haveI : IsProbabilityMeasure P₀ := hC.isGaussianProcess.isProbabilityMeasure
  refine ⟨Fin d → Ω₀, inferInstance, MeasureTheory.Measure.pi fun _ => P₀, inferInstance,
    fun x => LatticeProb.dimBrownian d C x, fun x => ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · have hzero : ∀ i : Fin d, ∀ᵐ ω ∂(MeasureTheory.Measure.pi fun _ : Fin d => P₀),
          C 0 (ω i) = 0 := fun i =>
        (MeasureTheory.measurePreserving_eval (fun _ : Fin d => P₀) i).quasiMeasurePreserving.ae
          hC.eval_zero_ae_eq_zero
      rw [← ae_all_iff] at hzero
      filter_upwards [hzero] with ω hω
      ext i
      simp [LatticeProb.dimBrownian, hω i]
    · intro i
      have hd : (0 : ℝ) < d := by
        have := i.pos
        exact_mod_cast this
      have hsq : Real.sqrt d * (Real.sqrt d)⁻¹ = 1 :=
        mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr hd)
      have hfun : (fun (t : ℝ≥0) (ω : Fin d → Ω₀) =>
          Real.sqrt d * (LatticeProb.dimBrownian d C x t ω i - x i)) = fun t ω => C t (ω i) := by
        funext t ω
        show Real.sqrt d * (x i + (Real.sqrt d)⁻¹ * C t (ω i) - x i) = C t (ω i)
        rw [add_sub_cancel_left, ← mul_assoc, hsq, one_mul]
      rw [hfun]
      exact LatticeProb.isBrownianReal_comp_eval hC i
    · have h : (fun (i : Fin d) (ω : Fin d → Ω₀) =>
          fun t : ℝ≥0 => LatticeProb.dimBrownian d C x t ω i)
          = fun (i : Fin d) (ω : Fin d → Ω₀) =>
            (fun ω₀ : Ω₀ => fun t : ℝ≥0 => x i + (Real.sqrt d)⁻¹ * C t ω₀) (ω i) := rfl
      rw [h]
      exact iIndepFun_pi fun i =>
        (measurable_pi_lambda _ fun t => (hCm t).const_mul _ |>.const_add _).aemeasurable
  · intro y ω
    rw [continuous_induced_rng]
    refine continuous_pi fun i => ?_
    exact ((hCcont (ω i)).const_mul _).const_add _
  · intro y t
    refine Measurable.stronglyMeasurable ?_
    refine ((EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable).comp ?_
    exact measurable_pi_lambda _ fun i =>
      ((hCm t).comp (measurable_pi_apply i)).const_mul _ |>.const_add _
