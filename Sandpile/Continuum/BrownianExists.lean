/-
Brownian motion on `ℝ^d` with generator `Δ/(2d)` exists, started at every point
of space at once on a single probability space.

Every statement of the paper that mentions Brownian motion is quantified over a
probability space carrying a family `B` indexed by the starting point, with
`Sandpile.Continuum.IsBrownian d y (B y) P` for every `y`.  Without a
construction those statements would be vacuous, so the construction is recorded
here as a theorem: `d` independent copies of a real Brownian motion, each scaled
by `1/√d` and translated by the starting point, have the three properties of the
predicate, and the translation does not change the space, so one space carries
the whole family.  This is the same discharge that
`Sandpile.Continuum.exists_isWhiteNoise` performs for white noise.
-/
import Sandpile.Continuum.Stopping
import LatticeProb.Gauss.BrownianCont

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- **Brownian motion on `ℝ^d` with generator `Δ/(2d)` exists.**  There is a
probability space carrying, for every starting point `x`, a process which starts
at `x`, whose coordinates centred at `x` and scaled by `√d` are real Brownian
motions, and whose coordinate processes are independent. -/
theorem Sandpile.Continuum.exists_isBrownian (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d),
      ∀ x : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d x (B x) P
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨Ω₀, mΩ₀, P₀, C, hCm, hC⟩ := LatticeProb.exists_isBrownianReal
  haveI : IsProbabilityMeasure P₀ := hC.isGaussianProcess.isProbabilityMeasure
  refine ⟨Fin d → Ω₀, inferInstance, MeasureTheory.Measure.pi fun _ => P₀, inferInstance,
    fun x => LatticeProb.dimBrownian d C x, fun x => ?_⟩
  refine ⟨?_, ?_, ?_⟩
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
