import Sandpile.Continuum.WhiteNoise

/-!
# White noise as a linear isometry on `L²`

White-noise evaluation as a linear isometry from spatial L2 to random-variable L2.
Orthonormal test functions give independent Gaussian coordinates. A Hilbert basis
reconstructs every L2 evaluation, and basis measurability extends to all indices
through the closed subspace of almost-everywhere measurable L2 functions.
-/

open MeasureTheory ProbabilityTheory Filter InnerProductSpace
open Sandpile.Continuum
open scoped RealInnerProductSpace

/-- The covariance of two white-noise evaluations is the `L²` inner product of the test
functions: this follows from `IsWhiteNoise.cov` (the raw second moment) together with
`IsWhiteNoise.mean` (each evaluation is centred), via the covariance-mean identity. -/
theorem Sandpile.Support.covariance_whiteNoise {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (f g : Space d → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    cov[W f, W g; P] = ∫ y, f y * g y := by
  rw [ProbabilityTheory.covariance_eq_sub
    (hW.gaussian.hasGaussianLaw_eval f).memLp_two
    (hW.gaussian.hasGaussianLaw_eval g).memLp_two, hW.mean f hf, hW.mean g hg]
  simpa only [Pi.mul_apply, zero_mul, sub_zero] using hW.cov f g hf hg


/-- **White noise evaluated on an orthonormal family is an independent family of random
variables.** The evaluations form a Gaussian process (`IsGaussianProcess.comp_right`), so
by `IsGaussianProcess.iIndepFun_of_covariance_eq_zero` it suffices that distinct indices
have zero covariance, which is `covariance_whiteNoise` together with orthonormality of
`f`. -/
theorem Sandpile.Support.iIndepFun_whiteNoise_orthonormal {Ω ι : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (f : ι → Lp ℝ 2 (volume : Measure (Space d))) (hf : Orthonormal ℝ f) :
    iIndepFun (fun i => W (fun y => f i y)) P := by
  have hg : IsGaussianProcess
      (fun (p : (i : ι) × Unit) ω => W (fun y => f p.1 y) ω) P :=
    hW.gaussian.comp_right (fun p : (i : ι) × Unit => (fun y => f p.1 y))
  have hi : iIndepFun (fun i ω (_ : Unit) => W (fun y => f i y) ω) P := by
    refine IsGaussianProcess.iIndepFun_of_covariance_eq_zero hg
      (fun i _ => (hW.meas _ (Lp.memLp (f i))).aemeasurable) ?_
    intro i j hij _ _
    rw [Sandpile.Support.covariance_whiteNoise hW _ _ (Lp.memLp _) (Lp.memLp _)]
    simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm] using
      hf.inner_eq_zero hij
  exact hi.comp (fun _ x => x ()) (fun _ => measurable_pi_apply ())


/-- The white-noise evaluation `W f` of an `L²` test function `f`, viewed as an element of
`L²(P)` (using that a Gaussian evaluation has finite second moment, `memLp_two`). -/
noncomputable def Sandpile.Support.whiteNoiseL2 {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) (f : Lp ℝ 2 (volume : Measure (Space d))) : Lp ℝ 2 P :=
  (hW.gaussian.hasGaussianLaw_eval (fun y => f y)).memLp_two.toLp (W (fun y => f y))

/-- **`whiteNoiseL2` preserves inner products**: the `L²(P)` inner product of two white-noise
evaluations equals the spatial `L²` inner product of the test functions, by unfolding both
sides as integrals and applying `IsWhiteNoise.cov`. -/
theorem Sandpile.Support.inner_whiteNoiseL2 {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) (f g : Lp ℝ 2 (volume : Measure (Space d))) :
    ⟪Sandpile.Support.whiteNoiseL2 hW f, Sandpile.Support.whiteNoiseL2 hW g⟫_ℝ = ⟪f, g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  calc (∫ ω, Sandpile.Support.whiteNoiseL2 hW g ω * Sandpile.Support.whiteNoiseL2 hW f ω ∂P)
      = ∫ ω, W (fun y => g y) ω * W (fun y => f y) ω ∂P := by
        apply integral_congr_ae
        filter_upwards [(hW.gaussian.hasGaussianLaw_eval (fun y => f y)).memLp_two.coeFn_toLp,
          (hW.gaussian.hasGaussianLaw_eval (fun y => g y)).memLp_two.coeFn_toLp] with ω hf hg
        exact congrArg₂ (· * ·) hg hf
    _ = ∫ y, g y * f y := hW.cov _ _ (Lp.memLp g) (Lp.memLp f)


/-- `whiteNoiseL2` is additive: both sides have the same inner product with every
element of `L²(P)` (by `inner_whiteNoiseL2` and linearity of the spatial inner product),
so their difference has zero norm. -/
theorem Sandpile.Support.whiteNoiseL2_add {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) (f g : Lp ℝ 2 (volume : Measure (Space d))) :
    Sandpile.Support.whiteNoiseL2 hW (f + g)
      = Sandpile.Support.whiteNoiseL2 hW f + Sandpile.Support.whiteNoiseL2 hW g := by
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    Sandpile.Support.inner_whiteNoiseL2]
  ring


/-- `whiteNoiseL2` is homogeneous of degree one, by the same inner-product argument as
`whiteNoiseL2_add`. -/
theorem Sandpile.Support.whiteNoiseL2_smul {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) (c : ℝ) (f : Lp ℝ 2 (volume : Measure (Space d))) :
    Sandpile.Support.whiteNoiseL2 hW (c • f) = c • Sandpile.Support.whiteNoiseL2 hW f := by
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    Sandpile.Support.inner_whiteNoiseL2]
  ring


/-- **White-noise evaluation as a linear isometry** `L²(Space d) →ₗᵢ[ℝ] L²(P)`, assembled
from `whiteNoiseL2` together with its additivity, homogeneity and inner-product-preserving
properties. -/
noncomputable def Sandpile.Support.whiteNoiseLinearIsometry {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) :
    Lp ℝ 2 (volume : Measure (Space d)) →ₗᵢ[ℝ] Lp ℝ 2 P := by
  exact LinearMap.isometryOfInner
    { toFun := Sandpile.Support.whiteNoiseL2 hW
      map_add' := Sandpile.Support.whiteNoiseL2_add hW
      map_smul' := Sandpile.Support.whiteNoiseL2_smul hW }
    (Sandpile.Support.inner_whiteNoiseL2 hW)


/-- **A Hilbert basis reconstructs every white-noise evaluation**: expanding `f` in a
Hilbert basis `b` of `L²(Space d)` and applying the continuous linear map underlying
`whiteNoiseLinearIsometry` transports the basis expansion `HasSum` to `W f`. -/
theorem Sandpile.Support.hasSum_whiteNoise_hilbertBasis {Ω ι : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure (Space d))))
    (f : Lp ℝ 2 (volume : Measure (Space d))) :
    HasSum (fun i => b.repr f i • Sandpile.Support.whiteNoiseL2 hW (b i))
      (Sandpile.Support.whiteNoiseL2 hW f) := by
  have h := (b.hasSum_repr f).mapL
    (Sandpile.Support.whiteNoiseLinearIsometry hW).toContinuousLinearMap
  simp only [map_smul] at h
  convert! h using 1


/-- **Measurability of white noise at every index of a Hilbert basis extends to every `L²`
test function**: `lpMeas` (the functions `m`-strongly-measurable in the ambient `σ`-algebra)
is a closed subspace of `L²(P)`, so it contains the sum-limit `whiteNoiseL2 hW f` of the
Hilbert-basis expansion (`hasSum_whiteNoise_hilbertBasis`) once it contains every basis
term. -/
theorem Sandpile.Support.aestronglyMeasurable_whiteNoise_of_basis {Ω ι : Type*}
    [mΩ : MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure (Space d))))
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (hb : ∀ i, AEStronglyMeasurable[m] (W (fun y => b i y)) P)
    (f : Lp ℝ 2 (volume : Measure (Space d))) :
    AEStronglyMeasurable[m] (W (fun y => f y)) P := by
  letI : MeasurableSpace Ω := mΩ
  let F := Sandpile.Support.whiteNoiseL2 hW
  let WF : Lp ℝ 2 (volume : Measure (Space d)) → Ω → ℝ := fun f => F f
  have hb' : ∀ i, AEStronglyMeasurable[m] (WF (b i)) P := fun i =>
    (hb i).congr (hW.gaussian.hasGaussianLaw_eval (fun y => b i y)).memLp_two.coeFn_toLp.symm
  have hc := isClosed_aestronglyMeasurable (F := ℝ) (p := 2) (μ := P) hm
  have hf' : AEStronglyMeasurable[m] (WF f) P := by
    apply hc.mem_of_tendsto (Sandpile.Support.hasSum_whiteNoise_hilbertBasis hW b f)
    apply Filter.Eventually.of_forall
    intro s
    exact mem_lpMeas_iff_aestronglyMeasurable.mp
      ((lpMeas ℝ ℝ m 2 P).sum_mem (fun i _ =>
        (lpMeas ℝ ℝ m 2 P).smul_mem _ (mem_lpMeas_iff_aestronglyMeasurable.mpr (hb' i))))
  exact hf'.congr (hW.gaussian.hasGaussianLaw_eval (fun y => f y)).memLp_two.coeFn_toLp

