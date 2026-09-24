/-
The law of the infinite Green field of `eq:dgt4-infinite-green-field` in the Gaussian case
(a) of `prop:dgt4-contact-asymptotics`.

`sandpile.tex:4971-4972` says that for a Gaussian scenery `V_\infty(0)` is mean-zero
Gaussian and writes `\Sigma^2=\Var(V_\infty(0))>0`.  That variance is not the variance of
the scenery: the field is `V_\infty(0)=\sum_z G(0,z)\zeta(z)`, so
`\Sigma^2=\Var(\zeta(0))\sum_z G(0,z)^2`, which is `fieldVar` below.  It is nonzero because
`G(0,0)\geq1` makes the sum at least one.

The identification of the law is the isonormal representation of
`Support/LinGaussField.lean`: under the standard Gaussian product law the box limit of
`eq:dgt4-infinite-green-field` exists almost surely and equals the isonormal image of the
square-summable family `z\mapsto G(0,z)`, whose law is the centred Gaussian of variance the
square of its norm.  Transporting that along the scaling `\omega\mapsto\sqrt v\omega` and
along the scenery map gives the law under `centeredMassLaw`, and the symmetry of the centred
Gaussian turns the lower tail of the field into the upper tail `gaussianUpperTail`.

With this, the Gaussian branch of `prop:dgt4-contact-asymptotics` rests on the two estimates
`eq:dgt4-contact-mean-increment` and `eq:dgt4-contact-threshold-relative-error` of
`sandpile.tex:4977-4984`, which Steps 1-4 verify, and on nothing else.
-/
import Sandpile.Support.Dgt4CaseA
import Sandpile.Support.LinGaussBridge
import Sandpile.Support.LinGaussFactor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- `\Sigma^2=\Var(V_\infty(0))` of `sandpile.tex:4967`: the variance of the infinite
Green field under a centred Gaussian scenery of variance `v`. -/
noncomputable def fieldVar (d : ℕ) (v : ℝ≥0) : ℝ≥0 := ((v : ℝ) * greenSqSum d).toNNReal

/-- `\Sigma^2>0` (`sandpile.tex:4967`): the sum of the squares of the Green function at the
origin is at least one. -/
theorem fieldVar_ne_zero (hd : 5 ≤ d) {v : ℝ≥0} (hv : v ≠ 0) : fieldVar d v ≠ 0 := by
  have h1 : (1 : ℝ) ≤ greenSqSum d := one_le_greenSqSum hd
  have hvpos : (0 : ℝ) < (v : ℝ) := lt_of_le_of_ne v.coe_nonneg
    (fun h => hv (by exact_mod_cast h.symm))
  have hpos : (0 : ℝ) < (v : ℝ) * greenSqSum d := by nlinarith
  simp only [fieldVar, ne_eq, Real.toNNReal_eq_zero, not_le]
  exact hpos

/-- **The law of the infinite Green field at the origin.**  Under an i.i.d. centred Gaussian
scenery of variance `v` the box limit of `eq:dgt4-infinite-green-field` is the centred
Gaussian of variance `v\sum_z G(0,z)^2`. -/
theorem map_infiniteGreenField_iid (hd : 5 ≤ d) (v : ℝ≥0) :
    (LatticeProb.iidLaw d (gaussianReal 0 v)).map (fun ζ => infiniteGreenField ζ (0 : Site d))
      = gaussianReal 0 (fieldVar d v) := by
  classical
  have hS : Measurable (fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z) := by
    fun_prop
  have hA : AEMeasurable (fun ζ : Site d → ℝ => infiniteGreenField ζ (0 : Site d))
      (LatticeProb.iidLaw d (gaussianReal 0 v)) :=
    aemeasurable_infiniteGreenField_iid hd v 0
  rw [iidLaw_gaussianReal_eq_map d v] at hA ⊢
  rw [hA.map_map_of_aemeasurable hS.aemeasurable]
  have hae : (fun ω : Site d → ℝ =>
        infiniteGreenField (fun z => Real.sqrt (v : ℝ) * ω z) (0 : Site d))
      =ᵐ[LatticeProb.gaussLaw (Site d)]
        (fun ω => ⇑(LatticeProb.gaussIso (Real.sqrt (v : ℝ) • greenLp d hd 0)) ω) := by
    filter_upwards [ae_infiniteGreenField_eq hd (0 : Site d) (Real.sqrt (v : ℝ)),
      Lp.coeFn_smul (Real.sqrt (v : ℝ)) (LatticeProb.gaussIso (greenLp d hd 0))] with ω hω hsm
    rw [hω, map_smul, hsm]
    simp
  show ((LatticeProb.gaussLaw (Site d)).map
      ((fun ζ : Site d → ℝ => infiniteGreenField ζ (0 : Site d)) ∘
        (fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z))) = _
  rw [show ((fun ζ : Site d → ℝ => infiniteGreenField ζ (0 : Site d)) ∘
      (fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z))
      = (fun ω : Site d → ℝ => infiniteGreenField (fun z => Real.sqrt (v : ℝ) * ω z)
          (0 : Site d)) from rfl]
  rw [Measure.map_congr hae, LatticeProb.map_gaussIso]
  congr 1
  have hnorm : ‖Real.sqrt (v : ℝ) • greenLp d hd 0‖ ^ 2
      = (v : ℝ) * ∑' z : Site d, green d 0 z ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt v.coe_nonneg,
      ← real_inner_self_eq_norm_sq, inner_greenLp hd 0 0]
    exact congrArg _ (tsum_congr fun z => (sq (green d 0 z)).symm)
  rw [fieldVar, greenSqSum, hnorm]

/-- The exceedance probabilities of `-V_\infty(0)` from the law of `V_\infty(0)`, in the mass
normalization: the scenery map transports the law, and the centred Gaussian is symmetric. -/
theorem infiniteFieldGaussianTail_of_map (hd : 5 ≤ d) (v w : ℝ≥0)
    (hmap : (LatticeProb.iidLaw d (gaussianReal 0 v)).map
        (fun ζ => infiniteGreenField ζ (0 : Site d))
      = gaussianReal 0 w) :
    InfiniteFieldGaussianTail d (gaussianReal 0 v) w := by
  classical
  intro t
  have hd1 : 1 ≤ d := by omega
  set F : (Site d → ℝ) → ℝ :=
    fun σ => infiniteGreenField (scenery d σ) (0 : Site d) with hF
  have hAm : AEMeasurable F (centeredMassLaw d (gaussianReal 0 v)) :=
    aemeasurable_infiniteGreenField_mass hd v 0
  have hmapF : (centeredMassLaw d (gaussianReal 0 v)).map F = gaussianReal 0 w := by
    have h1 : (centeredMassLaw d (gaussianReal 0 v)).map (scenery d)
        = LatticeProb.iidLaw d (gaussianReal 0 v) :=
      map_scenery_centeredMassLaw d (gaussianReal 0 v) hd1
    have h2 : AEMeasurable
        (fun ζ : Site d → ℝ => infiniteGreenField ζ (0 : Site d))
        ((centeredMassLaw d (gaussianReal 0 v)).map (scenery d)) := by
      rw [h1]; exact aemeasurable_infiniteGreenField_iid hd v 0
    have h3 := h2.map_map_of_aemeasurable (measurable_scenery d).aemeasurable
    rw [h1, hmap] at h3
    exact h3.symm
  have hset : {σ : Site d → ℝ |
      t < -infiniteGreenField (scenery d σ) (0 : Site d)}
      = F ⁻¹' (Set.Iio (-t)) := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio, hF, lt_neg]
  have hval : (centeredMassLaw d (gaussianReal 0 v)) (F ⁻¹' (Set.Iio (-t)))
      = gaussianReal 0 w (Set.Iio (-t)) := by
    rw [← Measure.map_apply_of_aemeasurable hAm measurableSet_Iio, hmapF]
  have hsymm : gaussianReal 0 w (Set.Iio (-t)) = gaussianReal 0 w (Set.Ioi t) := by
    have hneg : (gaussianReal (0 : ℝ) w).map (fun x : ℝ => -x) = gaussianReal 0 w := by
      rw [gaussianReal_map_neg]; norm_num
    have hpre : (fun x : ℝ => -x) ⁻¹' (Set.Ioi t) = Set.Iio (-t) := by
      ext x; simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, lt_neg]
    calc gaussianReal 0 w (Set.Iio (-t))
        = (gaussianReal (0 : ℝ) w) ((fun x : ℝ => -x) ⁻¹' (Set.Ioi t)) := by rw [hpre]
      _ = ((gaussianReal (0 : ℝ) w).map (fun x : ℝ => -x)) (Set.Ioi t) := by
          rw [Measure.map_apply measurable_neg measurableSet_Ioi]
      _ = gaussianReal 0 w (Set.Ioi t) := by rw [hneg]
  show ((centeredMassLaw d (gaussianReal 0 v))
      {σ | t < -infiniteGreenField (scenery d σ) 0}).toReal = gaussianUpperTail w t
  rw [gaussianUpperTail, hset, hval, hsymm]

/-- `-V_\infty(0)` is the mean-zero Gaussian of variance `\Sigma^2` (`sandpile.tex:4966-4967`). -/
theorem infiniteFieldGaussianTail_gaussian (hd : 5 ≤ d) (v : ℝ≥0) :
    InfiniteFieldGaussianTail d (gaussianReal 0 v) (fieldVar d v) :=
  infiniteFieldGaussianTail_of_map hd v _ (map_infiniteGreenField_iid hd v)

/-- Case (a) with the hypotheses exactly as the two frozen statements supply them.  The law
of the field is no longer an input: it is `infiniteFieldGaussianTail_gaussian`, so the
Gaussian branch rests on `eq:dgt4-contact-mean-increment` and
`eq:dgt4-contact-threshold-relative-error` alone. -/
theorem caseThresholdField_gaussian_of_hcase (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hatom : ∀ z : ℝ, ν {z} = 0) (hvar : 0 < evariance (id : ℝ → ℝ) ν)
    (v : ℝ≥0) (hgauss : ν = gaussianReal 0 v)
    (hincr : GaussianMeanIncrement d ν (fieldVar d v))
    (hrel : ThresholdRelativeError d ν
      (fun σ x => -infiniteGreenField (scenery d σ) x)) :
    CaseThresholdField d ν 1 := by
  have hv : v ≠ 0 := gaussian_var_ne_zero hvar hgauss
  refine caseThresholdField_gaussian hd ν hint hmean hatom v hgauss (fieldVar d v)
    (fieldVar_ne_zero hd hv) ?_ hincr hrel
  rw [hgauss]
  exact infiniteFieldGaussianTail_gaussian hd v

end Sandpile
