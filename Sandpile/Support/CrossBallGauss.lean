/-
The ball field of `sandpile.tex:2076-2088` as a Gaussian process, and its
positive association.

`sandpile.tex:2104`: "Finite collections are positively associated by Pitt's
Gaussian FKG theorem."  `Sandpile/External/PittGaussianFKG.lean` is that
theorem, frozen as an R1 hypothesis: a centred Gaussian planar field with
nonnegative covariances is `Sandpile.Continuum.IsAssociatedField`.  What is
needed to apply it to `𝒳_s` is here.

The ball field is the white noise reindexed by the ball kernels, so it is a
Gaussian process by `IsGaussianProcess.comp_right`, and its mean and covariance
are the mean and covariance of the white noise at those kernels.  The covariance
is the `L²` inner product of two ball kernels, and a ball kernel is nonnegative:
in dimension two it is `log(s/|x-z|)/2π` inside the ball, and `s/|x-z| ≥ 1`
there; in dimension three it is `(1/|x-z| - 1/s)/4π`, and `1/|x-z| ≥ 1/s`
there.  The single exception is the centre, where the junk value `1/0 = 0` makes
the dimension-three kernel `-1/(4πs)`; that is one point, which is null in
dimension two and three, so the product of two kernels is almost everywhere
nonnegative and its integral is nonnegative.

The square integrability `MemLp (ballKernel d s u) 2` of the kernel, which every
clause of `IsWhiteNoise` asks for before it says anything, is carried here as
the hypothesis `hmem`; it is proved in `Sandpile/Support/CrossBallMemLp.lean`,
where `isAssociatedField_ballField_of_whiteNoise` discharges it.
-/
import Sandpile.Support.CrossBall
import Sandpile.External.PittGaussianFKG
import Sandpile.Continuum.WhiteNoise

open MeasureTheory ProbabilityTheory Set

namespace Sandpile.Frozen.FixedScaleCrossings

/-- The ball kernel is nonnegative away from its centre. -/
theorem ballKernel_nonneg {d : ℕ} {s : ℝ} (u : Sandpile.Continuum.Space 2)
    {z : Sandpile.Continuum.Space d} (hz : z ≠ planePoint u) :
    0 ≤ ballKernel d s u z := by
  have hne : ‖(planePoint (d := d) u) - z‖ ≠ 0 := by
    simp only [ne_eq, norm_eq_zero, sub_eq_zero]
    intro h
    exact hz h.symm
  have hpos : 0 < ‖(planePoint (d := d) u) - z‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  unfold ballKernel
  by_cases hlt : ‖(planePoint (d := d) u) - z‖ < s
  · rw [if_pos hlt]
    by_cases hd : d = 2
    · rw [if_pos hd]
      have hge : (1 : ℝ) ≤ s / ‖(planePoint (d := d) u) - z‖ := (one_le_div hpos).mpr hlt.le
      exact mul_nonneg (by positivity) (Real.log_nonneg hge)
    · rw [if_neg hd]
      have hinv : 1 / s ≤ 1 / ‖(planePoint (d := d) u) - z‖ :=
        one_div_le_one_div_of_le hpos hlt.le
      exact mul_nonneg (by positivity) (by linarith)
  · rw [if_neg hlt]

/-- The product of two ball kernels is almost everywhere nonnegative: it can be
negative only at the two centres, and a point is null in dimension two or three. -/
theorem ae_ballKernel_mul_nonneg {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ}
    (u v : Sandpile.Continuum.Space 2) :
    ∀ᵐ z : Sandpile.Continuum.Space d ∂(volume),
      0 ≤ ballKernel d s u z * ballKernel d s v z := by
  have hsub : {z : Sandpile.Continuum.Space d | ¬ (0 ≤ ballKernel d s u z * ballKernel d s v z)}
      ⊆ {planePoint (d := d) u, planePoint (d := d) v} := by
    intro z hz
    by_contra hzz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hzz
    exact hz (mul_nonneg (ballKernel_nonneg u hzz.1) (ballKernel_nonneg v hzz.2))
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null hsub ?_
  rcases hd with rfl | rfl
  · rw [Set.insert_eq]
    exact measure_union_null (measure_singleton _) (measure_singleton _)
  · rw [Set.insert_eq]
    exact measure_union_null (measure_singleton _) (measure_singleton _)

/-- The ball field is a Gaussian process: it is the white noise reindexed by the
ball kernels. -/
theorem isGaussianProcess_ballField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
    {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (s : ℝ) :
    ProbabilityTheory.IsGaussianProcess (ballField d W s) P :=
  hW.gaussian.comp_right (ballKernel d s)

/-- The ball field is positively associated, by Pitt's Gaussian FKG theorem: it
is a centred Gaussian field whose covariances, the `L²` inner products of the
ball kernels, are nonnegative because the kernels are. -/
theorem isAssociatedField_ballField (hPitt : Sandpile.External.PittGaussianFKG)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (s : ℝ)
    (hmem : ∀ u : Sandpile.Continuum.Space 2, MemLp (ballKernel d s u) 2 volume) :
    Sandpile.Continuum.IsAssociatedField P (ballField d W s) := by
  have hgauss := isGaussianProcess_ballField hW s
  refine hPitt Ω P (ballField d W s) hgauss (fun u => hW.meas _ (hmem u)) ?_ ?_
  · intro u
    exact ⟨(hgauss.hasGaussianLaw_eval u).integrable, hW.mean _ (hmem u)⟩
  · intro u v
    refine ⟨?_, ?_⟩
    · have h := (hgauss.hasGaussianLaw_eval u).memLp_two.integrable_mul
        (hgauss.hasGaussianLaw_eval v).memLp_two
      simpa [Pi.mul_def] using h
    · show 0 ≤ ∫ ω, W (ballKernel d s u) ω * W (ballKernel d s v) ω ∂P
      rw [hW.cov _ _ (hmem u) (hmem v)]
      exact integral_nonneg_of_ae (ae_ballKernel_mul_nonneg hd u v)

end Sandpile.Frozen.FixedScaleCrossings
