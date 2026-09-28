import Sandpile.Support.LimNoiseCoordinates

/-!
# Removing finitely many coordinates leaves white noise measurable in the rest

Removing finitely many Hilbert coordinates from white noise leaves a field measurable, up to
almost-everywhere equality, from the remaining coordinates. Linearity and reconstruction are used
in `L²` (`whiteNoise_residual_ae_eq`, `aestronglyMeasurable_whiteNoise_of_coefficients`,
`aestronglyMeasurable_whiteNoise_residual`, `whiteNoiseL2_integral`); raw versions are compared
only almost everywhere for each fixed spatial test function (`whiteNoise_ae_eq_of_ae_eq`,
`hilbertBasis_repr_toLp_eq_integral`). The explicit finite-coefficient form
`finiteNoiseRemainder` and its measurability (`aestronglyMeasurable_finiteNoiseRemainder`)
package the whole argument for a concrete choice of coefficients, and
`indepFun_whiteNoise_orthogonal` records the companion independence fact for orthogonal
coordinates, via the elementary orthogonal-projection identity `inner_sub_finite_projection`.
-/

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open Sandpile.Continuum Sandpile.Support
open scoped ENNReal NNReal RealInnerProductSpace

/-- If two square-integrable test functions `f` and `g` agree almost everywhere, then `W f` and
`W g` agree `P`-almost surely: their difference has zero variance and zero mean by
`IsWhiteNoise.cov`/`IsWhiteNoise.mean`, so `ae_eq_integral_of_variance_eq_zero` forces it to equal
its mean, namely `0`, almost surely. -/
theorem Sandpile.Support.whiteNoise_ae_eq_of_ae_eq {Ω : Type*}
    [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (f g : Space d → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (heq : f =ᵐ[volume] g) : W f =ᵐ[P] W g := by
  have hX := (hW.gaussian.hasGaussianLaw_eval f).memLp_two
  have hY := (hW.gaussian.hasGaussianLaw_eval g).memLp_two
  have hgg : (∫ y, g y * g y) = ∫ y, f y * f y := by
    apply integral_congr_ae
    filter_upwards [heq] with y hy
    rw [hy]
  have hfg : (∫ y, f y * g y) = ∫ y, f y * f y := by
    apply integral_congr_ae
    filter_upwards [heq] with y hy
    rw [hy]
  have hvar : Var[W f - W g; P] = 0 := by
    rw [variance_sub hX hY, ← covariance_self hX.aemeasurable,
      ← covariance_self hY.aemeasurable,
      Sandpile.Support.covariance_whiteNoise hW f f hf hf,
      Sandpile.Support.covariance_whiteNoise hW g g hg hg,
      Sandpile.Support.covariance_whiteNoise hW f g hf hg, hgg, hfg]
    ring
  have hmean : (∫ ω, (W f - W g) ω ∂P) = 0 := by
    simp only [Pi.sub_apply]
    rw [integral_sub (hX.integrable (by norm_num)) (hY.integrable (by norm_num)),
      hW.mean f hf, hW.mean g hg, sub_self]
  have hz := ae_eq_integral_of_variance_eq_zero (hX.sub hY) hvar
  rw [hmean] at hz
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

/-- **Orthogonal white-noise coordinates are independent.** If every `f i` is orthogonal in `L²`
to every `g j`, then the families `(W (f i))_i` and `(W (g j))_j` are independent, since jointly
Gaussian random variables are independent exactly when their covariance vanishes
(`IsGaussianProcess.indepFun_of_covariance_eq_zero`), and covariance here is the `L²` inner
product (`Sandpile.Support.covariance_whiteNoise`). -/
theorem Sandpile.Support.indepFun_whiteNoise_orthogonal {Ω ι κ : Type*}
    [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (f : ι → Lp ℝ 2 (volume : Measure (Space d)))
    (g : κ → Lp ℝ 2 (volume : Measure (Space d)))
    (ho : ∀ i j, ⟪f i, g j⟫_ℝ = 0) :
    IndepFun (fun ω i => W (fun y => f i y) ω)
      (fun ω j => W (fun y => g j y) ω) P := by
  have hG : IsGaussianProcess
      (fun (j : Sum ι κ) ω => W (Sum.elim (fun i => fun y => f i y)
        (fun i => fun y => g i y) j) ω) P :=
    hW.gaussian.comp_right (Sum.elim (fun i => fun y => f i y) (fun i => fun y => g i y))
  have hG' : IsGaussianProcess (Sum.elim (fun i => W (fun y => f i y))
      (fun j => W (fun y => g j y))) P := by
    convert hG using 1
    funext j ω
    cases j <;> rfl
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero hG'
    (fun i => (hW.meas _ (Lp.memLp (f i))).aemeasurable)
    (fun j => (hW.meas _ (Lp.memLp (g j))).aemeasurable)
  intro i j
  rw [Sandpile.Support.covariance_whiteNoise hW _ _ (Lp.memLp _) (Lp.memLp _)]
  simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm] using ho i j

/-- The residual after subtracting the finite orthogonal projection of `x` onto `s` is orthogonal
to each basis vector `v i` used in that projection, for `i ∈ s`. -/
theorem Sandpile.Support.inner_sub_finite_projection {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (hv : Orthonormal ℝ v) (s : Finset ι) (x : E) {i : ι}
    (hi : i ∈ s) :
    ⟪v i, x - ∑ j ∈ s, ⟪v j, x⟫_ℝ • v j⟫_ℝ = 0 := by
  rw [inner_sub_right, hv.inner_right_sum (fun j => ⟪v j, x⟫_ℝ) hi, sub_self]

/-- **Strong measurability of white noise from its Hilbert-basis coefficients.** If `W (b i)` is
`m`-measurable at every index `i` where `f`'s coefficient `b.repr f i` is nonzero, then `W f`
itself is `m`-measurable: `W f` is (up to a.e. equality) the `L²` limit `whiteNoiseL2 hW f` of its
partial Hilbert-basis sums (`Sandpile.Support.hasSum_whiteNoise_hilbertBasis`), and the set of
`m`-measurable `L²` functions is closed. -/
theorem Sandpile.Support.aestronglyMeasurable_whiteNoise_of_coefficients {Ω ι : Type*}
    [mΩ : MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure (Space d))))
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (f : Lp ℝ 2 (volume : Measure (Space d)))
    (hb : ∀ i, b.repr f i ≠ 0 → AEStronglyMeasurable[m] (W (fun y => b i y)) P) :
    AEStronglyMeasurable[m] (W (fun y => f y)) P := by
  letI : MeasurableSpace Ω := mΩ
  let F := Sandpile.Support.whiteNoiseL2 hW
  let WF : Lp ℝ 2 (volume : Measure (Space d)) → Ω → ℝ := fun g => F g
  have hc := isClosed_aestronglyMeasurable (F := ℝ) (p := 2) (μ := P) hm
  have hf' : AEStronglyMeasurable[m] (WF f) P := by
    apply hc.mem_of_tendsto (Sandpile.Support.hasSum_whiteNoise_hilbertBasis hW b f)
    apply Filter.Eventually.of_forall
    intro s
    refine mem_lpMeas_iff_aestronglyMeasurable.mp
      ((lpMeas ℝ ℝ m 2 P).sum_mem (fun i _ => ?_))
    by_cases hi : b.repr f i = 0
    · rw [hi, zero_smul]
      exact (lpMeas ℝ ℝ m 2 P).zero_mem
    · apply (lpMeas ℝ ℝ m 2 P).smul_mem
      apply mem_lpMeas_iff_aestronglyMeasurable.mpr
      exact (hb i hi).congr
        (hW.gaussian.hasGaussianLaw_eval (fun y => b i y)).memLp_two.coeFn_toLp.symm
  exact hf'.congr (hW.gaussian.hasGaussianLaw_eval (fun y => f y)).memLp_two.coeFn_toLp

/-- White noise commutes with subtracting a finite linear combination: `W` applied to `f` minus a
finite sum `∑ c_i • v_i` agrees almost surely with `W f` minus the corresponding finite sum
`∑ c_i · W (v_i)`, transported through the linear isometry
`Sandpile.Support.whiteNoiseLinearIsometry`. -/
theorem Sandpile.Support.whiteNoise_residual_ae_eq {Ω ι : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) (v : ι → Lp ℝ 2 (volume : Measure (Space d)))
    (f : Lp ℝ 2 (volume : Measure (Space d))) (s : Finset ι) (c : ι → ℝ) :
    W (fun y => (f - ∑ i ∈ s, c i • v i) y) =ᵐ[P]
      fun ω => W (fun y => f y) ω - ∑ i ∈ s, c i * W (fun y => v i y) ω := by
  classical
  let L := Sandpile.Support.whiteNoiseLinearIsometry hW
  let R := f - ∑ i ∈ s, c i • v i
  have heq : L R = L f - ∑ i ∈ s, c i • L (v i) := by
    simp only [R, map_sub, map_sum, map_smul]
  have hR : W (fun y => R y) =ᵐ[P] fun ω => L R ω :=
    (hW.gaussian.hasGaussianLaw_eval (fun y => R y)).memLp_two.coeFn_toLp.symm
  have hF : (fun ω => L f ω) =ᵐ[P] W (fun y => f y) :=
    (hW.gaussian.hasGaussianLaw_eval (fun y => f y)).memLp_two.coeFn_toLp
  have hV : ∀ᵐ ω ∂P, ∀ i : {i // i ∈ s},
      L (v i) ω = W (fun y => v i y) ω :=
    ae_all_iff.mpr fun i =>
      (hW.gaussian.hasGaussianLaw_eval (fun y => v i y)).memLp_two.coeFn_toLp
  have hsmul : ∀ᵐ ω ∂P, ∀ i : {i // i ∈ s},
      (c i • L (v i)) ω = c i * L (v i) ω :=
    ae_all_iff.mpr fun i => Lp.coeFn_smul (c i) (L (v i))
  filter_upwards [hR, hF, hV, hsmul,
    Lp.coeFn_sub (L f) (∑ i ∈ s, c i • L (v i)),
    Lp.coeFn_fun_finsetSum s (fun i => c i • L (v i))] with ω hωR hωF hωV hωsmul hωsub hωsum
  rw [hωR, heq, hωsub, Pi.sub_apply, hωsum, hωF]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hωsmul ⟨i,hi⟩, hωV ⟨i,hi⟩]

/-- The residual of `W` at `f` after subtracting its projection onto the basis vectors indexed by
`s` is `m`-measurable, given `m`-measurability of `W (b i)` for every `i ∉ s`: this specializes
`aestronglyMeasurable_whiteNoise_of_coefficients` to `f - ∑_{i∈s} (b.repr f i) • b i`, whose own
`i`-th coefficient vanishes for `i ∈ s` by `inner_sub_finite_projection`. -/
theorem Sandpile.Support.aestronglyMeasurable_whiteNoise_residual {Ω ι : Type*}
    [mΩ : MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure (Space d))))
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (s : Finset ι)
    (hb : ∀ i, i ∉ s → AEStronglyMeasurable[m] (W (fun y => b i y)) P)
    (f : Lp ℝ 2 (volume : Measure (Space d))) :
    AEStronglyMeasurable[m]
      (W (fun y => (f - ∑ i ∈ s, b.repr f i • b i) y)) P := by
  refine @Sandpile.Support.aestronglyMeasurable_whiteNoise_of_coefficients Ω ι mΩ d P W hW b m hm
    (f - ∑ i ∈ s, b.repr f i • b i) ?_
  intro i hi
  apply hb i
  intro his
  apply hi
  simp only [b.repr_apply_apply]
  exact Sandpile.Support.inner_sub_finite_projection b b.orthonormal s f his

/-- The `i`-th Hilbert-basis coefficient of the `L²` class of `f` is the integral pairing
`∫ f · b i`. -/
theorem Sandpile.Support.hilbertBasis_repr_toLp_eq_integral {ι : Type*} {d : ℕ}
    (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure (Space d))))
    (f : Space d → ℝ) (hf : MemLp f 2 volume) (i : ι) :
    b.repr (hf.toLp f) i = ∫ y, f y * b i y := by
  rw [b.repr_apply_apply, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with y hy
  rw [hy]

/-- `W f` with the contribution of the basis vectors indexed by `s` subtracted off explicitly,
using the integral pairings `∫ f · b i` as coefficients rather than the abstract Hilbert-basis
representation. -/
noncomputable def Sandpile.Support.finiteNoiseRemainder {Ω ι : Type*} {d : ℕ}
    (W : (Space d → ℝ) → Ω → ℝ) (b : ι → Lp ℝ 2 (volume : Measure (Space d)))
    (s : Finset ι) (f : Space d → ℝ) (ω : Ω) : ℝ :=
  W f ω - ∑ i ∈ s, (∫ y, f y * b i y) * W (fun y => b i y) ω

/-- **The explicit finite-coefficient remainder is `m`-measurable.** Given `m`-measurability of
`W (b i)` for `i ∉ s`, `finiteNoiseRemainder W b s f` is `m`-measurable, by identifying it almost
surely with the abstract residual of `aestronglyMeasurable_whiteNoise_residual` via
`hilbertBasis_repr_toLp_eq_integral` and `whiteNoise_residual_ae_eq`. -/
theorem Sandpile.Support.aestronglyMeasurable_finiteNoiseRemainder {Ω ι : Type*}
    [mΩ : MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure (Space d))))
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (s : Finset ι)
    (hb : ∀ i, i ∉ s → AEStronglyMeasurable[m] (W (fun y => b i y)) P)
    (f : Space d → ℝ) (hf : MemLp f 2 volume) :
    AEStronglyMeasurable[m] (Sandpile.Support.finiteNoiseRemainder W b s f) P := by
  let F := hf.toLp f
  have hmR := @Sandpile.Support.aestronglyMeasurable_whiteNoise_residual Ω ι mΩ d P W
    hW b m hm s hb F
  apply hmR.congr
  have hR := @Sandpile.Support.whiteNoise_residual_ae_eq Ω ι mΩ d P W hW b F s (fun i => b.repr F i)
  have hF := @Sandpile.Support.whiteNoise_ae_eq_of_ae_eq Ω mΩ d P _ W hW (fun y => F y) f
    (Lp.memLp F) hf hf.coeFn_toLp
  filter_upwards [hR, hF] with ω hωR hωF
  rw [hωR, hωF]
  unfold Sandpile.Support.finiteNoiseRemainder
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Sandpile.Support.hilbertBasis_repr_toLp_eq_integral b f hf i]

/-- The `L²` white-noise map `Sandpile.Support.whiteNoiseL2` commutes with a Bochner integral
over a parameter space, since it is a continuous linear map. -/
theorem Sandpile.Support.whiteNoiseL2_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) (μ : Measure X)
    (f : X → Lp ℝ 2 (volume : Measure (Space d))) (hf : Integrable f μ) :
    Sandpile.Support.whiteNoiseL2 hW (∫ x, f x ∂μ) =
      ∫ x, Sandpile.Support.whiteNoiseL2 hW (f x) ∂μ := by
  let L := (Sandpile.Support.whiteNoiseLinearIsometry hW).toContinuousLinearMap
  have h := L.integral_comp_comm hf
  convert! h.symm using 1
