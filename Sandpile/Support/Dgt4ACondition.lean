/-
**The conditioning of Step 2 of case (a) as a deterministic shift**
(`sandpile.tex:5105-5126`).

The proof conditions the Gaussian scenery on the value of the single linear
functional `-V_\infty(0)` and says that "raising `b` to `b+s` shifts `\zeta(z)` by
`-s\Var(\zeta(0))G(0,z)/\Sigma^2`".  Here that is made a statement about measures and
not about conditional expectations.

Write `e=G(0,\cdot)/\|G(0,\cdot)\|` for the unit vector along the Green coefficients
at the origin, `\xi` for its isonormal image, and split each coordinate of the
standard Gaussian product as

  `\omega(z)=\xi(\omega)e(z)+\rho(\omega)(z)`,   `\rho(\omega)(z)=\omega(z)-\xi(\omega)e(z)`.

The residual coordinate `\rho(\cdot)(z)` is the isonormal image of
`\delta_z-e(z)e`, which is orthogonal to `e`, so `\xi` and the whole residual FIELD
`\rho` are independent as processes (`Support/Dgt4AGaussProcess.lean`).  Since
`\xi` is standard Gaussian, the law of the scenery is therefore the image of the
product of a standard Gaussian and the law of the residual field under the shift
`(s,r)\mapsto r+se`, which is `gaussLaw_eq_map_prod`.  Integrating against that
identity is the paper's conditioning, and the shift by `s` in the second
coordinate is the paper's shift of `\zeta(z)`.
-/
import Sandpile.Support.Dgt4AGaussProcess
import Sandpile.Support.LinGaussFactor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- `\|G(0,\cdot)\|^2=\sum_z G(0,z)^2`. -/
theorem norm_greenLp_sq (hd : 5 ≤ d) : ‖greenLp d hd (0 : Site d)‖ ^ 2 = greenSqSum d := by
  have h := inner_greenLp hd (0 : Site d) 0
  rw [real_inner_self_eq_norm_sq] at h
  rw [h, greenSqSum]
  exact tsum_congr fun z => by ring

/-- `\|G(0,\cdot)\|>0`, because `\sum_z G(0,z)^2\geq G(0,0)^2\geq1`. -/
theorem norm_greenLp_pos (hd : 5 ≤ d) : 0 < ‖greenLp d hd (0 : Site d)‖ := by
  have h1 : (1 : ℝ) ≤ greenSqSum d := one_le_greenSqSum hd
  have h2 := norm_greenLp_sq hd
  nlinarith [norm_nonneg (greenLp d hd (0 : Site d))]

/-- `e=G(0,\cdot)/\|G(0,\cdot)\|`, the direction the conditioning of Step 2 fixes. -/
noncomputable def greenUnit (d : ℕ) (hd : 5 ≤ d) : lp (fun _ : Site d => ℝ) 2 :=
  ‖greenLp d hd (0 : Site d)‖⁻¹ • greenLp d hd (0 : Site d)

theorem norm_greenUnit (hd : 5 ≤ d) : ‖greenUnit d hd‖ = 1 := by
  have hpos := norm_greenLp_pos hd
  rw [greenUnit, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos]
  field_simp

/-- The inner product with the unit coefficient family at a site evaluates at that site. -/
theorem inner_single_lp (f : lp (fun _ : Site d => ℝ) 2) (z : Site d) :
    (inner ℝ (lp.single 2 z (1 : ℝ)) f : ℝ) = (f : Site d → ℝ) z := by
  rw [lp.inner_eq_tsum, tsum_eq_single z]
  · simp
  · intro i hi
    simp [hi]

/-- `r_z=\delta_z-e(z)e`, the residual coefficient family at the site `z`. -/
noncomputable def residCoeff (d : ℕ) (hd : 5 ≤ d) (z : Site d) : lp (fun _ : Site d => ℝ) 2 :=
  lp.single 2 z (1 : ℝ) - ((greenUnit d hd : Site d → ℝ) z) • greenUnit d hd

/-- The residual coefficients are orthogonal to the conditioned direction. -/
theorem inner_residCoeff_greenUnit (hd : 5 ≤ d) (z : Site d) :
    (inner ℝ (residCoeff d hd z) (greenUnit d hd) : ℝ) = 0 := by
  rw [residCoeff, inner_sub_left, real_inner_smul_left, inner_single_lp,
    real_inner_self_eq_norm_sq, norm_greenUnit hd]
  ring

/-- `\xi`, the standard Gaussian in the conditioned direction: `V_\infty(0)=\Sigma\xi`. -/
noncomputable def condCoord (d : ℕ) (hd : 5 ≤ d) : (Site d → ℝ) → ℝ :=
  ⇑(LatticeProb.gaussIso (greenUnit d hd))

/-- `\rho`, the residual field: the standard Gaussian product with its component along the
conditioned direction removed. -/
noncomputable def residField (d : ℕ) (hd : 5 ≤ d) (ω : Site d → ℝ) : Site d → ℝ :=
  fun z => ω z - condCoord d hd ω * (greenUnit d hd : Site d → ℝ) z

theorem measurable_condCoord (hd : 5 ≤ d) : Measurable (condCoord d hd) :=
  (Lp.stronglyMeasurable (LatticeProb.gaussIso (greenUnit d hd))).measurable

theorem measurable_residField (hd : 5 ≤ d) : Measurable (residField d hd) :=
  measurable_pi_lambda _ fun z =>
    (measurable_pi_apply z).sub ((measurable_condCoord hd).mul measurable_const)

/-- Each coordinate of the residual field is the isonormal image of a residual
coefficient family. -/
theorem ae_coeFn_gaussIso_residCoeff (hd : 5 ≤ d) (z : Site d) :
    ⇑(LatticeProb.gaussIso (residCoeff d hd z)) =ᵐ[LatticeProb.gaussLaw (Site d)]
      fun ω => ω z - condCoord d hd ω * (greenUnit d hd : Site d → ℝ) z := by
  have hlin : LatticeProb.gaussIso (residCoeff d hd z)
      = LatticeProb.gaussIso (lp.single 2 z (1 : ℝ))
        - ((greenUnit d hd : Site d → ℝ) z) • LatticeProb.gaussIso (greenUnit d hd) := by
    rw [residCoeff, map_sub, map_smul]
  rw [hlin]
  filter_upwards [Lp.coeFn_sub (LatticeProb.gaussIso (lp.single 2 z (1 : ℝ)))
      (((greenUnit d hd : Site d → ℝ) z) • LatticeProb.gaussIso (greenUnit d hd)),
    Lp.coeFn_smul ((greenUnit d hd : Site d → ℝ) z) (LatticeProb.gaussIso (greenUnit d hd)),
    coeFn_gaussIso_single (ι := Site d) z] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3]
  simp only [smul_eq_mul, condCoord]
  ring

theorem ae_residField_eq (hd : 5 ≤ d) :
    (fun ω z => ⇑(LatticeProb.gaussIso (residCoeff d hd z)) ω)
      =ᵐ[LatticeProb.gaussLaw (Site d)] residField d hd := by
  have h : ∀ z : Site d, ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)),
      ⇑(LatticeProb.gaussIso (residCoeff d hd z)) ω = residField d hd ω z :=
    fun z => ae_coeFn_gaussIso_residCoeff hd z
  rw [← ae_all_iff] at h
  filter_upwards [h] with ω hω
  funext z
  exact hω z

/-- **The conditioned direction is independent of the residual field.** -/
theorem indepFun_condCoord_residField (hd : 5 ≤ d) :
    IndepFun (condCoord d hd) (residField d hd) (LatticeProb.gaussLaw (Site d)) := by
  have horth : ∀ (_ : Unit) (z : Site d),
      (inner ℝ (greenUnit d hd) (residCoeff d hd z) : ℝ) = 0 := by
    intro _ z
    rw [real_inner_comm]
    exact inner_residCoeff_greenUnit hd z
  have hproc := indepFun_gaussIso_process (ι := Site d)
      (fun _ : Unit => greenUnit d hd) (fun z : Site d => residCoeff d hd z) horth
  have h1 : IndepFun (condCoord d hd)
      (fun ω z => ⇑(LatticeProb.gaussIso (residCoeff d hd z)) ω)
      (LatticeProb.gaussLaw (Site d)) :=
    hproc.comp (measurable_pi_apply ()) measurable_id
  exact h1.congr (Filter.EventuallyEq.refl _ _) (ae_residField_eq hd)

/-- The conditioned direction is a standard Gaussian. -/
theorem map_condCoord (hd : 5 ≤ d) :
    (LatticeProb.gaussLaw (Site d)).map (condCoord d hd) = gaussianReal 0 1 := by
  rw [condCoord, LatticeProb.map_gaussIso, norm_greenUnit hd]
  norm_num

/-- **The conditioning of `sandpile.tex:5100-5104` as an identity of measures.**  The
standard Gaussian product is the image of a standard Gaussian times the law of the
residual field under the shift `(s,r)\mapsto r+se`.  Integrating a function of the
scenery against this identity is the paper's conditioning on `-V_\infty(0)`, and the
inner integral at the level `s` is the paper's conditional expectation. -/
theorem gaussLaw_eq_map_prod (hd : 5 ≤ d) :
    LatticeProb.gaussLaw (Site d)
      = Measure.map
          (fun p : ℝ × (Site d → ℝ) => fun z => p.2 z + p.1 * (greenUnit d hd : Site d → ℝ) z)
          ((gaussianReal 0 1).prod
            ((LatticeProb.gaussLaw (Site d)).map (residField d hd))) := by
  have hpair := (indepFun_condCoord_residField hd).map_prod_eq_prod_map_map
      (measurable_condCoord hd).aemeasurable (measurable_residField hd).aemeasurable
  rw [map_condCoord hd] at hpair
  have hPhi : Measurable
      (fun p : ℝ × (Site d → ℝ) => fun z => p.2 z + p.1 * (greenUnit d hd : Site d → ℝ) z) := by
    refine measurable_pi_lambda _ fun z => ?_
    exact ((measurable_pi_apply z).comp measurable_snd).add
      (measurable_fst.mul measurable_const)
  have hpm : Measurable (fun ω : Site d → ℝ => (condCoord d hd ω, residField d hd ω)) :=
    (measurable_condCoord hd).prodMk (measurable_residField hd)
  rw [← hpair, Measure.map_map hPhi hpm]
  have hid : ((fun p : ℝ × (Site d → ℝ) =>
        fun z => p.2 z + p.1 * (greenUnit d hd : Site d → ℝ) z)
      ∘ fun ω : Site d → ℝ => (condCoord d hd ω, residField d hd ω)) = id := by
    funext ω
    funext z
    simp only [Function.comp_apply, residField, id_eq]
    ring
  rw [hid, Measure.map_id]

/-- The shift map `(s,r)\mapsto r+se` of the conditioning is measurable. -/
theorem measurable_shiftPair (hd : 5 ≤ d) : Measurable
    (fun p : ℝ × (Site d → ℝ) => fun z => p.2 z + p.1 * (greenUnit d hd : Site d → ℝ) z) := by
  refine measurable_pi_lambda _ fun z => ?_
  exact ((measurable_pi_apply z).comp measurable_snd).add (measurable_fst.mul measurable_const)

/-- **The conditioning read on probabilities.**  The probability of an event of the
scenery is the average over the conditioned level `s` of its probability for the
residual field shifted by `se`. -/
theorem measure_gaussLaw_shift (hd : 5 ≤ d) {A : Set (Site d → ℝ)} (hA : MeasurableSet A) :
    LatticeProb.gaussLaw (Site d) A
      = ∫⁻ s, ((LatticeProb.gaussLaw (Site d)).map (residField d hd))
          {r | (fun z => r z + s * (greenUnit d hd : Site d → ℝ) z) ∈ A}
        ∂(gaussianReal 0 1) := by
  have hPhi := measurable_shiftPair hd
  conv_lhs => rw [gaussLaw_eq_map_prod hd]
  rw [Measure.map_apply hPhi hA, Measure.prod_apply (hPhi hA)]
  rfl

/-- **The conditioning read on integrals.**  The mean of a function of the scenery is
the average over the conditioned level `s` of its mean for the residual field shifted
by `se`.  The inner integral is the paper's conditional expectation given
`-V_\infty(0)`. -/
theorem integral_gaussLaw_shift (hd : 5 ≤ d) (F : (Site d → ℝ) → ℝ)
    (hF : Integrable F (LatticeProb.gaussLaw (Site d))) :
    (∫ ω, F ω ∂(LatticeProb.gaussLaw (Site d)))
      = ∫ s, (∫ r, F (fun z => r z + s * (greenUnit d hd : Site d → ℝ) z)
          ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd))) ∂(gaussianReal 0 1) := by
  classical
  have hPhi := measurable_shiftPair hd
  haveI : IsProbabilityMeasure ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) :=
    Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  have hmap := gaussLaw_eq_map_prod hd
  have hFm : AEStronglyMeasurable F
      (Measure.map (fun p : ℝ × (Site d → ℝ) =>
          fun z => p.2 z + p.1 * (greenUnit d hd : Site d → ℝ) z)
        ((gaussianReal 0 1).prod ((LatticeProb.gaussLaw (Site d)).map (residField d hd)))) := by
    rw [← hmap]; exact hF.1
  have hFi : Integrable (fun p : ℝ × (Site d → ℝ) =>
      F (fun z => p.2 z + p.1 * (greenUnit d hd : Site d → ℝ) z))
      ((gaussianReal 0 1).prod ((LatticeProb.gaussLaw (Site d)).map (residField d hd))) := by
    have hmm : Integrable F
        (Measure.map (fun p : ℝ × (Site d → ℝ) =>
            fun z => p.2 z + p.1 * (greenUnit d hd : Site d → ℝ) z)
          ((gaussianReal 0 1).prod
            ((LatticeProb.gaussLaw (Site d)).map (residField d hd)))) := by
      rw [← hmap]; exact hF
    exact (integrable_map_measure hFm hPhi.aemeasurable).mp hmm
  calc (∫ ω, F ω ∂(LatticeProb.gaussLaw (Site d)))
      = ∫ ω, F ω ∂(Measure.map (fun p : ℝ × (Site d → ℝ) =>
            fun z => p.2 z + p.1 * (greenUnit d hd : Site d → ℝ) z)
          ((gaussianReal 0 1).prod
            ((LatticeProb.gaussLaw (Site d)).map (residField d hd)))) := by rw [← hmap]
    _ = ∫ p : ℝ × (Site d → ℝ), F (fun z => p.2 z + p.1 * (greenUnit d hd : Site d → ℝ) z)
          ∂((gaussianReal 0 1).prod
            ((LatticeProb.gaussLaw (Site d)).map (residField d hd))) :=
        integral_map hPhi.aemeasurable hFm
    _ = ∫ s, (∫ r, F (fun z => r z + s * (greenUnit d hd : Site d → ℝ) z)
          ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd))) ∂(gaussianReal 0 1) :=
        integral_prod _ hFi

end Sandpile
