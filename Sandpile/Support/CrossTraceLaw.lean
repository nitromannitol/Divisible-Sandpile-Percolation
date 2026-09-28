import Sandpile.Support.LimNoiseCoordinates
import Sandpile.Support.ContWhiteNoise
import Sandpile.Support.CrossBallMemLp
import Sandpile.Support.CrossLevelLoss
import Sandpile.Support.CrossFixedScaleBall

/-!
# The trace laws of Step 3

The trace laws of Step 3 of `prop:fixed-scale-crossings` (`sandpile.tex:2350-2382`).

  "Let `z_1,\ldots,z_M` be the processed square centers ... and let `\P_\ell^{\rm tr}`
   be the law of `\mathfrak T_M` under `\P_\ell`."

The exploration reads the white noise at finitely many test functions; when those
test functions are orthonormal in `L²`, the coordinates are independent standard
Gaussians, so the trace law is the standard Gaussian product.  This is the
unshifted law `\P_0^{\rm tr}` of the level loss; the shifted law `\P_{L/R}^{\rm tr}`
is the same product with the Cameron--Martin means.
-/

open MeasureTheory ProbabilityTheory
open Sandpile.Continuum
open Sandpile.Frozen.FixedScaleCrossings
open Filter

namespace Sandpile.Support

/-- The law of the white noise on an orthonormal family of `n` indices is the
standard Gaussian product: the coordinates are independent (`iIndepFun` from
orthogonality) and each has law `gaussianReal 0 1`. -/
theorem map_whiteNoise_orthonormal {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    {n : ℕ} (f : Fin n → Lp ℝ 2 (volume : Measure (Space d)))
    (hf : Orthonormal ℝ f)
    (hnorm : ∀ i, ∫ y : Space d, (f i : Space d → ℝ) y * (f i : Space d → ℝ) y = 1) :
    P.map (fun ω => (fun i : Fin n => W (fun y => (f i : Space d → ℝ) y) ω))
      = Measure.pi fun _ : Fin n => gaussianReal 0 1 := by
  have hind := Sandpile.Support.iIndepFun_whiteNoise_orthonormal hW f hf
  have hmap := ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
    (fun i : Fin n => (hW.meas _ (Lp.memLp (f i))).aemeasurable) hind
  rw [hmap]
  congr 1
  funext i
  rw [Sandpile.Support.map_whiteNoise_eq_gaussianReal W P hW _ (Lp.memLp (f i))]
  have h := hnorm i
  rw [h]
  norm_num

/-- The shifted trace law of Step 3: the law of the white noise on an orthonormal
family of `n` indices, shifted by the Cameron--Martin means `c`, is the product
of the shifted one-dimensional Gaussians. -/
theorem map_whiteNoise_orthonormal_shift {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    {n : ℕ} (f : Fin n → Lp ℝ 2 (volume : Measure (Space d)))
    (hf : Orthonormal ℝ f)
    (hnorm : ∀ i, ∫ y : Space d, (f i : Space d → ℝ) y * (f i : Space d → ℝ) y = 1)
    (c : Fin n → ℝ) :
    P.map (fun ω => (fun i : Fin n => W (fun y => (f i : Space d → ℝ) y) ω + c i))
      = Measure.pi fun i : Fin n => gaussianReal (c i) 1 := by
  have hbase := Sandpile.Support.map_whiteNoise_orthonormal hW f hf hnorm
  have hfmeas : Measurable fun ω => (fun i : Fin n => W (fun y => (f i : Space d → ℝ) y) ω) :=
    measurable_pi_iff.mpr fun i => hW.meas _ (Lp.memLp (f i))
  have hgmeas : Measurable fun x : Fin n → ℝ => (fun i => x i + c i) := by fun_prop
  have hcomp : (fun ω => (fun i : Fin n => W (fun y => (f i : Space d → ℝ) y) ω + c i))
      = (fun x : Fin n → ℝ => fun i => x i + c i) ∘
        (fun ω => fun i => W (fun y => (f i : Space d → ℝ) y) ω) := rfl
  rw [hcomp, ← Measure.map_map hgmeas hfmeas, hbase]
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 1)
    (f := fun i (y : ℝ) => y + c i) (fun i => (measurable_id.add_const (c i)).aemeasurable)
  rw [h]
  congr 1
  funext i
  rw [ProbabilityTheory.gaussianReal_map_add_const]
  norm_num

/-- The white noise at an `L²` function and at any representative of its class
agree almost surely: the difference has zero `L²` norm, so its covariance with
itself vanishes and it is zero almost surely. -/
theorem whiteNoise_toLp_ae {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (f : Space d → ℝ) (hf : MemLp f 2 (volume : Measure (Space d))) :
    W (fun y => (hf.toLp f : Space d → ℝ) y) =ᵐ[P] W f := by
  have hcoe : (fun y => (hf.toLp f : Space d → ℝ) y) =ᵐ[volume] f :=
    MemLp.coeFn_toLp hf
  have hsub : MemLp (fun y => (hf.toLp f : Space d → ℝ) y - f y) 2 (volume : Measure (Space d)) :=
    (Lp.memLp (hf.toLp f)).sub hf
  have hzero : ∫ y : Space d,
      ((hf.toLp f : Space d → ℝ) y - f y) * ((hf.toLp f : Space d → ℝ) y - f y) = 0 := by
    rw [← integral_eq_zero_of_ae]
    filter_upwards [hcoe] with y hy
    rw [hy]
    simp
  have hcov := hW.cov (fun y => (hf.toLp f : Space d → ℝ) y - f y)
    (fun y => (hf.toLp f : Space d → ℝ) y - f y) hsub hsub
  rw [hzero] at hcov
  have hdiff : W (fun y => (hf.toLp f : Space d → ℝ) y - f y) =ᵐ[P] fun ω =>
      W (fun y => (hf.toLp f : Space d → ℝ) y) ω - W f ω := by
    have h1 := hW.add (fun y => (hf.toLp f : Space d → ℝ) y - f y) f hsub hf
    filter_upwards [h1] with ω h1ω
    have hthis : W ((fun y => (hf.toLp f : Space d → ℝ) y - f y) + f) ω
        = W (fun y => (hf.toLp f : Space d → ℝ) y) ω := by
      congr 1
      funext y
      simp
    rw [h1ω] at hthis
    linarith
  have hsq : ∫ ω, (W (fun y => (hf.toLp f : Space d → ℝ) y) ω - W f ω) ^ 2 ∂P = 0 := by
    rw [← hcov]
    apply integral_congr_ae
    filter_upwards [hdiff] with ω hω
    rw [← hω]
    ring
  have hint : Integrable (fun ω => (W (fun y => (hf.toLp f : Space d → ℝ) y) ω - W f ω) ^ 2) P :=
    ((hW.gaussian.hasGaussianLaw_eval _).memLp_two.sub
      (hW.gaussian.hasGaussianLaw_eval f).memLp_two).integrable_sq
  have hzeroae : (fun ω => (W (fun y => (hf.toLp f : Space d → ℝ) y) ω - W f ω) ^ 2) =ᵐ[P] 0 := by
    refine (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint).mp hsq
  filter_upwards [hzeroae] with ω h2
  have h4 : W (fun y => (hf.toLp f : Space d → ℝ) y) ω - W f ω = 0 := by
    rw [← sq_eq_zero_iff]
    exact h2
  show W (fun y => (hf.toLp f : Space d → ℝ) y) ω = W f ω
  linarith


/-
Vacuity check: everything past this point in an earlier version of this file
(`exploration_supplies_orthonormal` and its descendants, down to
`fixed_scale_crossings_of_exploration_data_red`) built the trace law on `hdata`/`horth`, an
`Orthonormal ℝ` hypothesis on the BALL KERNELS `ballKernel d 1 (q i)` at finitely many distinct
points `q i`.  That hypothesis is unsatisfiable for `n ≥ 1` (the ball kernel is a log/Newtonian
kernel, not of unit `L²` norm, and is not orthogonal to its translates), so those theorems could
never be instantiated at real exploration data; the deleted material is dead code, not a working
reduction.  The corrected trace law uses the indicators of the exploration's DISJOINT UNIT CUBES,
which genuinely are orthonormal in `L²`: see `Sandpile/Support/CrossCubeLaw.lean`
(`map_whiteNoise_cubeIndicators`, `exploration_supplies_cube_data`), which is what
`Sandpile/Support/CrossLevelLoss.lean`'s `hloss_ballField_of_shift_laws` and
`Sandpile/Support/CrossCubeLaw.lean`'s `hloss_ballField_of_cube_data` consume.  The three lemmas
kept above this note (`map_whiteNoise_orthonormal`, `map_whiteNoise_orthonormal_shift`,
`whiteNoise_toLp_ae`) are the general facts the cube-indicator route itself uses and are not part
of the deleted, ball-kernel-specific material.
-/

end Sandpile.Support
