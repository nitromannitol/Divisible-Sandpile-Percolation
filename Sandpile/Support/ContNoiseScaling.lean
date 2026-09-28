import Sandpile.Support.ContKernelScaling
import Sandpile.Support.ContScaleMeasure
import Sandpile.Support.ContWhiteNoise
import Sandpile.Support.ContBMSquare

/-!
# Brownian scaling and stationarity of the white noise

Brownian scaling and stationarity of the white noise of `ssec:continuum-membrane-fields`,
and the resulting exact scaling of the Gaussian heat potential `Z`.

The proof of `prop:continuum-value-selfsimilar` at `sandpile.tex:1985-1993` reads:
"Stationarity of white noise gives $\mathcal U(T,x)\stackrel d=\mathcal U(T,0)$. Brownian
scaling then gives $\{Z(Ts,\sqrt Ty)\}\stackrel d=\{T^{1-d/4}Z(s,y)\}$."

Both statements are one identity here. For `T>0` and `x∈ℝ^d` put `ψ(w) = T^{-1/2}(w-x)`;
the map `f ↦ T^{-d/4} 𝒲(f∘ψ)` (`scaledNoise`) is again a white noise
(`isWhiteNoise_scaledNoise`), because `ψ` scales Lebesgue measure by `T^{-d/2}` and the two
factors `T^{-d/4}` square to the reciprocal of that. The kernel scaling of
`Sandpile.Support.greenTimeBM_mul_time` then turns the index of `Z` at the scaled point
into the index of the transformed noise at the unscaled point,
`g^{BM}_{Ts}(x+\sqrt Ty,\cdot) = T^{1-d/2}\,g^{BM}_s(y,\psi(\cdot))` (`greenTimeBM_scaled_index`
and `greenTimeBM_scaled_fun`), and the two powers combine to `T^{1-d/4}`
(`gaussianPotential_scaled`, `gaussianPotential_scaled_pi`), giving the equality in law of
`map_gaussianPotential_scaled_combination` and, at a single point,
`map_gaussianPotential_point_scaled`. `integral_greenTimeBM_scaled` records the matching
scaling of the covariance kernel.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The index of the Gaussian heat potential at the parabolically scaled point,
written through the affine map `w ↦ T^{-1/2}(w-x)`. -/
theorem greenTimeBM_scaled_index (d : ℕ) {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : 0 ≤ s)
    (x y w : Space d) :
    greenTimeBM d (T * s) (x + T ^ ((1 : ℝ) / 2) • y) w
      = T ^ (1 - (d : ℝ) / 2) *
        greenTimeBM d s y (T ^ (-(1 : ℝ) / 2) • (w - x)) := by
  have hone : T ^ (-(1 : ℝ) / 2) * T ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hT]
    norm_num
  have hpt : T ^ (-(1 : ℝ) / 2) • (x + T ^ ((1 : ℝ) / 2) • y)
      = T ^ (-(1 : ℝ) / 2) • x + y := by
    rw [smul_add, smul_smul, hone, one_smul]
  rw [greenTimeBM_mul_time d hT hs, hpt, greenTimeBM_shift, ← smul_sub]

/-- The white noise seen at the parabolic scale `T` about the point `x`:
`f ↦ T^{-d/4} 𝒲(f∘ψ)` with `ψ(w) = T^{-1/2}(w-x)`. -/
noncomputable def scaledNoise {Ω : Type*} (d : ℕ) (T : ℝ) (x : Space d)
    (W : (Space d → ℝ) → Ω → ℝ) (f : Space d → ℝ) (ω : Ω) : ℝ :=
  T ^ (-(d : ℝ) / 4) * W (fun w => f (T ^ (-(1 : ℝ) / 2) • (w - x))) ω

/-- Reindexing a Gaussian process by a fixed map and scaling it by a constant
leaves it Gaussian. -/
theorem isGaussianProcess_scaled {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (W : (Space d → ℝ) → Ω → ℝ) (P : Measure Ω)
    (hW : IsGaussianProcess W P) (c : ℝ) (ψ : Space d → Space d) :
    IsGaussianProcess (fun (f : Space d → ℝ) (ω : Ω) => c * W (fun w => f (ψ w)) ω) P := by
  have h1 : IsGaussianProcess (W ∘ (fun (f : Space d → ℝ) => (fun w => f (ψ w)))) P :=
    hW.comp_right (fun (f : Space d → ℝ) => (fun w => f (ψ w)))
  have h2 := h1.smul (fun _ : Space d → ℝ => c)
  exact h2

/-- The index of the Gaussian heat potential at the parabolically scaled point, as
a scalar multiple of the index of the unscaled potential composed with the affine
map. -/
theorem greenTimeBM_scaled_fun (d : ℕ) {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : 0 ≤ s)
    (x y : Space d) :
    (fun w : Space d => greenTimeBM d (T * s) (x + T ^ ((1 : ℝ) / 2) • y) w)
      = T ^ (1 - (d : ℝ) / 2) •
        (fun w : Space d => greenTimeBM d s y (T ^ (-(1 : ℝ) / 2) • (w - x))) := by
  funext w
  simp only [Pi.smul_apply, smul_eq_mul]
  exact greenTimeBM_scaled_index d hT hs x y w

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Each value of the rescaled noise is measurable. -/
theorem scaledNoise_measurable (d : ℕ)
    (W : (Space d → ℝ) → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : IsWhiteNoise d W P) {T : ℝ} (hT : 0 < T) (x : Space d)
    (f : Space d → ℝ) (hf : MemLp f 2 (volume : Measure (Space d))) :
    Measurable (scaledNoise d T x W f) := by
  have hc : (0:ℝ) < T ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hT _
  have hmem := memLp_comp_scaleShift d hc x hf
  show Measurable fun ω => T ^ (-(d : ℝ) / 4) *
    W (fun w => f (T ^ (-(1 : ℝ) / 2) • (w - x))) ω
  exact (hW.meas _ hmem).const_mul _

/-- Each value of the rescaled noise is centred. -/
theorem scaledNoise_mean (d : ℕ)
    (W : (Space d → ℝ) → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : IsWhiteNoise d W P) {T : ℝ} (hT : 0 < T) (x : Space d)
    (f : Space d → ℝ) (hf : MemLp f 2 (volume : Measure (Space d))) :
    ∫ ω, scaledNoise d T x W f ω ∂P = 0 := by
  have hc : (0:ℝ) < T ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hT _
  have hmem := memLp_comp_scaleShift d hc x hf
  simp only [scaledNoise]
  rw [MeasureTheory.integral_const_mul, hW.mean _ hmem, mul_zero]

/-- The covariance of the rescaled noise is the `L²` inner product: the
Jacobian `T^{d/2}` of the affine map cancels against the two factors `T^{-d/4}`. -/
theorem scaledNoise_cov (d : ℕ)
    (W : (Space d → ℝ) → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : IsWhiteNoise d W P) {T : ℝ} (hT : 0 < T) (x : Space d)
    (f g : Space d → ℝ) (hf : MemLp f 2 (volume : Measure (Space d)))
    (hg : MemLp g 2 (volume : Measure (Space d))) :
    ∫ ω, scaledNoise d T x W f ω * scaledNoise d T x W g ω ∂P
      = ∫ y : Space d, f y * g y := by
  have hc : (0:ℝ) < T ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hT _
  have hmf := memLp_comp_scaleShift d hc x hf
  have hmg := memLp_comp_scaleShift d hc x hg
  have hcov := hW.cov _ _ hmf hmg
  have hchange : ∫ w : Space d, f (T ^ (-(1 : ℝ) / 2) • (w - x)) *
        g (T ^ (-(1 : ℝ) / 2) • (w - x))
      = ((T ^ (-(1 : ℝ) / 2)) ^ d)⁻¹ * ∫ u : Space d, f u * g u :=
    integral_comp_scaleShift d hc x (fun u => f u * g u)
  have hprod : (fun ω => scaledNoise d T x W f ω * scaledNoise d T x W g ω)
      = fun ω => (T ^ (-(d : ℝ) / 4) * T ^ (-(d : ℝ) / 4)) *
          (W (fun w => f (T ^ (-(1 : ℝ) / 2) • (w - x))) ω *
            W (fun w => g (T ^ (-(1 : ℝ) / 2) • (w - x))) ω) := by
    funext ω
    simp only [scaledNoise]
    ring
  rw [hprod, MeasureTheory.integral_const_mul, hcov, hchange, inv_pow_rpow_neg_half d hT,
    ← mul_assoc, scale_factor_sq d hT, one_mul]

/-- The rescaled noise is additive in its index, almost surely. -/
theorem scaledNoise_add (d : ℕ)
    (W : (Space d → ℝ) → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : IsWhiteNoise d W P) {T : ℝ} (hT : 0 < T) (x : Space d)
    (f g : Space d → ℝ) (hf : MemLp f 2 (volume : Measure (Space d)))
    (hg : MemLp g 2 (volume : Measure (Space d))) :
    scaledNoise d T x W (f + g)
      =ᵐ[P] fun ω => scaledNoise d T x W f ω + scaledNoise d T x W g ω := by
  have hc : (0:ℝ) < T ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hT _
  have hmf := memLp_comp_scaleShift d hc x hf
  have hmg := memLp_comp_scaleShift d hc x hg
  have hidx : (fun w : Space d => (f + g) (T ^ (-(1 : ℝ) / 2) • (w - x)))
      = (fun w : Space d => f (T ^ (-(1 : ℝ) / 2) • (w - x)))
        + (fun w : Space d => g (T ^ (-(1 : ℝ) / 2) • (w - x))) := by
    funext w
    simp
  have hadd := hW.add _ _ hmf hmg
  filter_upwards [hadd] with ω hω
  show T ^ (-(d : ℝ) / 4) * W (fun w => (f + g) (T ^ (-(1 : ℝ) / 2) • (w - x))) ω
      = T ^ (-(d : ℝ) / 4) * W (fun w => f (T ^ (-(1 : ℝ) / 2) • (w - x))) ω
        + T ^ (-(d : ℝ) / 4) * W (fun w => g (T ^ (-(1 : ℝ) / 2) • (w - x))) ω
  rw [hidx, hω]
  ring

/-- The rescaled noise is homogeneous in its index, almost surely. -/
theorem scaledNoise_smul (d : ℕ)
    (W : (Space d → ℝ) → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : IsWhiteNoise d W P) {T : ℝ} (hT : 0 < T) (x : Space d)
    (a : ℝ) (f : Space d → ℝ) (hf : MemLp f 2 (volume : Measure (Space d))) :
    scaledNoise d T x W (a • f) =ᵐ[P] fun ω => a * scaledNoise d T x W f ω := by
  have hc : (0:ℝ) < T ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hT _
  have hmf := memLp_comp_scaleShift d hc x hf
  have hidx : (fun w : Space d => (a • f) (T ^ (-(1 : ℝ) / 2) • (w - x)))
      = a • (fun w : Space d => f (T ^ (-(1 : ℝ) / 2) • (w - x))) := by
    funext w
    simp
  have hs := hW.smul a _ hmf
  filter_upwards [hs] with ω hω
  show T ^ (-(d : ℝ) / 4) * W (fun w => (a • f) (T ^ (-(1 : ℝ) / 2) • (w - x))) ω
      = a * (T ^ (-(d : ℝ) / 4) * W (fun w => f (T ^ (-(1 : ℝ) / 2) • (w - x))) ω)
  rw [hidx, hω]
  ring

/-- **Brownian scaling and stationarity of the white noise**: `f ↦ T^{-d/4} 𝒲(f∘ψ)`
with `ψ(w) = T^{-1/2}(w-x)` is again a white noise on `ℝ^d`.  This is the content of
"Stationarity of white noise ... Brownian scaling then gives" at `sandpile.tex:1985-1990`. -/
theorem isWhiteNoise_scaledNoise (d : ℕ)
    (W : (Space d → ℝ) → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : IsWhiteNoise d W P) {T : ℝ} (hT : 0 < T) (x : Space d) :
    IsWhiteNoise d (scaledNoise d T x W) P where
  gaussian := isGaussianProcess_scaled d W P hW.gaussian (T ^ (-(d : ℝ) / 4))
    (fun w => T ^ (-(1 : ℝ) / 2) • (w - x))
  meas := fun f hf => scaledNoise_measurable d W P hW hT x f hf
  mean := fun f hf => scaledNoise_mean d W P hW hT x f hf
  cov := fun f g hf hg => scaledNoise_cov d W P hW hT x f g hf hg
  add := fun f g hf hg => scaledNoise_add d W P hW hT x f g hf hg
  smul := fun a f hf => scaledNoise_smul d W P hW hT x a f hf
  jointMeas := by
    intro U mU μ hμ f hf hs
    exact LatticeProb.exists_joint_version_of_covariance volume P (scaledNoise d T x W)
      (fun q => ((isGaussianProcess_scaled d W P hW.gaussian
        (T ^ (-(d : ℝ) / 4))
        (fun w => T ^ (-(1 : ℝ) / 2) • (w - x))).hasGaussianLaw_eval q).memLp_two)
      (fun a b ha hb => scaledNoise_cov d W P hW hT x a b ha hb) f hf hs

/-- **The Brownian scaling of the Gaussian heat potential.**  This is the display
of `sandpile.tex:1988-1990`,
`{Z(Ts,√T y)} =^d {T^{1-d/4} Z(s,y)}`, in its exact almost-sure form: the left side
is, at every point, `T^{1-d/4}` times the potential of the rescaled white noise. -/
theorem gaussianPotential_scaled {ΩW : Type*} [MeasurableSpace ΩW] (d : ℕ)
    (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν2 : ℝ)
    (W : (Space d → ℝ) → ΩW → ℝ) (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (hW : IsWhiteNoise d W PW) {T : ℝ} (hT : 0 < T) (x : Space d) {s : ℝ} (hs : 0 ≤ s)
    (y : Space d) :
    (fun ω => gaussianPotential d ν2 W (T * s) (x + T ^ ((1 : ℝ) / 2) • y) ω)
      =ᵐ[PW] fun ω =>
        T ^ (1 - (d : ℝ) / 4) * gaussianPotential d ν2 (scaledNoise d T x W) s y ω := by
  have hc : (0:ℝ) < T ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hT _
  have hmemG : MemLp (fun w : Space d => greenTimeBM d s y (T ^ (-(1 : ℝ) / 2) • (w - x))) 2
      (volume : Measure (Space d)) :=
    memLp_comp_scaleShift d hc x (memLp_greenTimeBM hd hd3 hs y)
  have hfun := greenTimeBM_scaled_fun d hT hs x y
  have hsm := hW.smul (T ^ (1 - (d : ℝ) / 2)) _ hmemG
  have harith : T ^ (1 - (d : ℝ) / 2)
      = T ^ (1 - (d : ℝ) / 4) * T ^ (-(d : ℝ) / 4) := by
    rw [← Real.rpow_add hT]
    congr 1
    ring
  filter_upwards [hsm] with ω hω
  show Real.sqrt ν2 * W (fun w => greenTimeBM d (T * s) (x + T ^ ((1 : ℝ) / 2) • y) w) ω
      = T ^ (1 - (d : ℝ) / 4) *
        (Real.sqrt ν2 * (T ^ (-(d : ℝ) / 4) *
          W (fun w => greenTimeBM d s y (T ^ (-(1 : ℝ) / 2) • (w - x))) ω))
  rw [hfun, hω, harith]
  ring

/-- **The two fields of the paper's scaling display have the same law**, in the
sense that every linear combination of finitely many of their values does.  This is
`{Z(Ts,√T y)} =^d {T^{1-d/4} Z(s,y)}` of `sandpile.tex:1988-1990`: the left side is
a linear combination of the values of the rescaled white noise, which is a white
noise, so both laws are the centred Gaussian whose variance is the square of the
`L²` norm of the same combination of Green kernels. -/
theorem map_gaussianPotential_scaled_combination {ΩW : Type*} [MeasurableSpace ΩW]
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν2 : ℝ)
    (W : (Space d → ℝ) → ΩW → ℝ) (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (hW : IsWhiteNoise d W PW) {T : ℝ} (hT : 0 < T) (x : Space d)
    {m : ℕ} (t : Fin m → ℝ) (s : Fin m → ℝ) (hs : ∀ i, 0 ≤ s i) (y : Fin m → Space d) :
    PW.map (fun ω => ∑ i, t i *
        gaussianPotential d ν2 W (T * s i) (x + T ^ ((1 : ℝ) / 2) • y i) ω)
      = PW.map (fun ω => ∑ i, t i *
        (T ^ (1 - (d : ℝ) / 4) * gaussianPotential d ν2 W (s i) (y i) ω)) := by
  classical
  have hW' : IsWhiteNoise d (scaledNoise d T x W) PW :=
    isWhiteNoise_scaledNoise d W PW hW hT x
  have hg : ∀ i : Fin m, MemLp (fun w : Space d => greenTimeBM d (s i) (y i) w) 2
      (volume : Measure (Space d)) := fun i => memLp_greenTimeBM hd hd3 (hs i) (y i)
  have hall : ∀ᵐ ω ∂PW, ∀ i : Fin m,
      gaussianPotential d ν2 W (T * s i) (x + T ^ ((1 : ℝ) / 2) • y i) ω
        = T ^ (1 - (d : ℝ) / 4) *
          gaussianPotential d ν2 (scaledNoise d T x W) (s i) (y i) ω :=
    MeasureTheory.ae_all_iff.mpr
      (fun i => gaussianPotential_scaled d hd hd3 ν2 W PW hW hT x (hs i) (y i))
  have hae : (fun ω => ∑ i, t i *
        gaussianPotential d ν2 W (T * s i) (x + T ^ ((1 : ℝ) / 2) • y i) ω)
      =ᵐ[PW] fun ω => ∑ i : Fin m,
        (t i * T ^ (1 - (d : ℝ) / 4) * Real.sqrt ν2) *
          scaledNoise d T x W (fun w => greenTimeBM d (s i) (y i) w) ω := by
    filter_upwards [hall] with ω hω
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hω i]
    show t i * (T ^ (1 - (d : ℝ) / 4) *
        (Real.sqrt ν2 * scaledNoise d T x W (fun w => greenTimeBM d (s i) (y i) w) ω))
      = (t i * T ^ (1 - (d : ℝ) / 4) * Real.sqrt ν2) *
        scaledNoise d T x W (fun w => greenTimeBM d (s i) (y i) w) ω
    ring
  have hrhs : (fun ω => ∑ i, t i *
        (T ^ (1 - (d : ℝ) / 4) * gaussianPotential d ν2 W (s i) (y i) ω))
      = fun ω => ∑ i : Fin m,
        (t i * T ^ (1 - (d : ℝ) / 4) * Real.sqrt ν2) *
          W (fun w => greenTimeBM d (s i) (y i) w) ω := by
    funext ω
    refine Finset.sum_congr rfl fun i _ => ?_
    show t i * (T ^ (1 - (d : ℝ) / 4) *
        (Real.sqrt ν2 * W (fun w => greenTimeBM d (s i) (y i) w) ω))
      = (t i * T ^ (1 - (d : ℝ) / 4) * Real.sqrt ν2) *
        W (fun w => greenTimeBM d (s i) (y i) w) ω
    ring
  rw [MeasureTheory.Measure.map_congr hae, hrhs,
    map_whiteNoise_combination (scaledNoise d T x W) PW hW'
      (fun i : Fin m => t i * T ^ (1 - (d : ℝ) / 4) * Real.sqrt ν2)
      (fun i : Fin m => fun w : Space d => greenTimeBM d (s i) (y i) w) hg,
    map_whiteNoise_combination W PW hW
      (fun i : Fin m => t i * T ^ (1 - (d : ℝ) / 4) * Real.sqrt ν2)
      (fun i : Fin m => fun w : Space d => greenTimeBM d (s i) (y i) w) hg]

/-- **The Brownian scaling of the covariance of the Gaussian heat potential.**  The
covariance of `Z` is `Var(ζ(0))` times this integral (`sandpile.tex:1022-1028`), so the
display says that the covariance picks up exactly `T^{2-d/2} = (T^{1-d/4})²`. -/
theorem integral_greenTimeBM_scaled (d : ℕ) {T : ℝ} (hT : 0 < T)
    (x : Space d) {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s') (y y' : Space d) :
    ∫ w : Space d, greenTimeBM d (T * s) (x + T ^ ((1 : ℝ) / 2) • y) w *
        greenTimeBM d (T * s') (x + T ^ ((1 : ℝ) / 2) • y') w
      = T ^ (2 - (d : ℝ) / 2) *
        ∫ u : Space d, greenTimeBM d s y u * greenTimeBM d s' y' u := by
  have hc : (0:ℝ) < T ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hT _
  have hpt : ∀ w : Space d,
      greenTimeBM d (T * s) (x + T ^ ((1 : ℝ) / 2) • y) w *
        greenTimeBM d (T * s') (x + T ^ ((1 : ℝ) / 2) • y') w
      = T ^ (1 - (d : ℝ) / 2) * T ^ (1 - (d : ℝ) / 2) *
        (fun u : Space d => greenTimeBM d s y u * greenTimeBM d s' y' u)
          (T ^ (-(1 : ℝ) / 2) • (w - x)) := by
    intro w
    rw [greenTimeBM_scaled_index d hT hs x y w, greenTimeBM_scaled_index d hT hs' x y' w]
    ring
  have hpow : T ^ (1 - (d : ℝ) / 2) * T ^ (1 - (d : ℝ) / 2) * T ^ ((d : ℝ) / 2)
      = T ^ (2 - (d : ℝ) / 2) := by
    rw [← Real.rpow_add hT, ← Real.rpow_add hT]
    congr 1
    ring
  simp only [hpt]
  rw [MeasureTheory.integral_const_mul,
    integral_comp_scaleShift d hc x
      (fun u : Space d => greenTimeBM d s y u * greenTimeBM d s' y' u),
    inv_pow_rpow_neg_half d hT, ← mul_assoc, hpow]

/-- The law of the Gaussian heat potential at `(T,x)` is the law of `T^{1-d/4}` times its
value at `(1,0)`.  This is the field half of the first sentence of
`prop:continuum-value-selfsimilar`. -/
theorem map_gaussianPotential_point_scaled {ΩW : Type*} [MeasurableSpace ΩW]
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν2 : ℝ)
    (W : (Space d → ℝ) → ΩW → ℝ) (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (hW : IsWhiteNoise d W PW) {T : ℝ} (hT : 0 < T) (x : Space d) :
    PW.map (fun ω => gaussianPotential d ν2 W T x ω)
      = PW.map (fun ω => T ^ (1 - (d : ℝ) / 4) * gaussianPotential d ν2 W 1 0 ω) := by
  have h := map_gaussianPotential_scaled_combination d hd hd3 ν2 W PW hW hT x
    (m := 1) (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) (fun _ => zero_le_one) (fun _ => (0 : Space d))
  simpa using h

/-- The vector form of the scaling: finitely many points at once. -/
theorem gaussianPotential_scaled_pi {ΩW : Type*} [MeasurableSpace ΩW]
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν2 : ℝ)
    (W : (Space d → ℝ) → ΩW → ℝ) (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (hW : IsWhiteNoise d W PW) {T : ℝ} (hT : 0 < T) (x : Space d)
    {m : ℕ} (s : Fin m → ℝ) (hs : ∀ i, 0 ≤ s i) (y : Fin m → Space d) :
    (fun ω (i : Fin m) =>
        gaussianPotential d ν2 W (T * s i) (x + T ^ ((1 : ℝ) / 2) • y i) ω)
      =ᵐ[PW] fun ω (i : Fin m) =>
        T ^ (1 - (d : ℝ) / 4) *
          gaussianPotential d ν2 (scaledNoise d T x W) (s i) (y i) ω := by
  have hall : ∀ᵐ ω ∂PW, ∀ i : Fin m,
      gaussianPotential d ν2 W (T * s i) (x + T ^ ((1 : ℝ) / 2) • y i) ω
        = T ^ (1 - (d : ℝ) / 4) *
          gaussianPotential d ν2 (scaledNoise d T x W) (s i) (y i) ω :=
    MeasureTheory.ae_all_iff.mpr
      (fun i => gaussianPotential_scaled d hd hd3 ν2 W PW hW hT x (hs i) (y i))
  filter_upwards [hall] with ω hω
  funext i
  exact hω i

end Sandpile.Support
