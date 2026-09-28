import LatticeProb.Gauss.IsonormalSum

/-!
Independence in the isonormal picture of `Support/LinGaussIso.lean`: two isonormal images
are independent as soon as their coefficient families are orthogonal, and a finite
orthogonal family of coefficients gives a jointly independent family of images.

This is the splitting that the conditioning of Step 2 of case (a) rests on
(`sandpile.tex:5105-5109`): writing `e=G(0,\cdot)/\|G(0,\cdot)\|` and
`r_z=G(z,\cdot)-\langle G(z,\cdot),e\rangle e`, conditioning the scenery on `V_\infty(0)`
leaves the residual field built from the `r_z` untouched and shifts the scenery by a
deterministic multiple of `G(0,\cdot)`.

The Gaussian input is that a vector of isonormal images is a centred Gaussian vector whose
covariance is the Gram matrix of the coefficient families (`map_gaussIso_vector`), together
with the theorem that jointly Gaussian and uncorrelated implies independent; the covariance
is the inner product because the isonormal map is an isometry.
-/

open LatticeProb.Isonormal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {ι : Type*} [Countable ι]

/-- The pair `(gaussIso f, gaussIso g)` of isonormal images is jointly Gaussian: it is the
image of the Gaussian `EuclideanSpace ℝ (Fin 2)`-valued vector `gaussIso ![f, g]` under the
continuous linear coordinate-projection map. -/
theorem hasGaussianLaw_gaussIso_pair (f g : lp (fun _ : ι => ℝ) 2) :
    HasGaussianLaw (fun ω => ((⇑(LatticeProb.gaussIso f) ω, ⇑(LatticeProb.gaussIso g) ω) : ℝ × ℝ))
      (LatticeProb.gaussLaw ι) := by
  classical
  have hvec : HasGaussianLaw (fun ω => (WithLp.toLp 2
      (fun i => ⇑(LatticeProb.gaussIso (![f, g] i)) ω) : EuclideanSpace ℝ (Fin 2)))
      (LatticeProb.gaussLaw ι) := by
    constructor
    rw [map_gaussIso_vector (fun i => ![f, g] i)]
    infer_instance
  have hL : HasGaussianLaw
      ((((EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj (1 : Fin 2)) :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ)) ∘
        fun ω => (WithLp.toLp 2 (fun i => ⇑(LatticeProb.gaussIso (![f, g] i)) ω) :
          EuclideanSpace ℝ (Fin 2))) (LatticeProb.gaussLaw ι) :=
    HasGaussianLaw.map_of_measurable _ hvec (by fun_prop)
  exact hL

/-- **The covariance of two isonormal images is the inner product of their coefficients.** -/
theorem covariance_gaussIso (f g : lp (fun _ : ι => ℝ) 2) :
    cov[⇑(LatticeProb.gaussIso f), ⇑(LatticeProb.gaussIso g); LatticeProb.gaussLaw ι]
      = (inner ℝ f g : ℝ) := by
  have hf : MemLp (⇑(LatticeProb.gaussIso f)) 2 (LatticeProb.gaussLaw ι) := Lp.memLp _
  have hg : MemLp (⇑(LatticeProb.gaussIso g)) 2 (LatticeProb.gaussLaw ι) := Lp.memLp _
  rw [covariance_eq_sub hf hg, integral_gaussIso f, integral_gaussIso g]
  have hmul : (∫ ω, (⇑(LatticeProb.gaussIso f) * ⇑(LatticeProb.gaussIso g)) ω
        ∂(LatticeProb.gaussLaw ι))
      = ∫ ω, ⇑(LatticeProb.gaussIso f) ω * ⇑(LatticeProb.gaussIso g) ω
        ∂(LatticeProb.gaussLaw ι) := by
    simp [Pi.mul_apply]
  rw [hmul, integral_gaussIso_mul f g]
  ring

/-- **Orthogonal coefficient families give independent isonormal images.**  The two images
are jointly Gaussian, and their covariance is their inner product. -/
theorem indepFun_gaussIso (f g : lp (fun _ : ι => ℝ) 2) (h : (inner ℝ f g : ℝ) = 0) :
    ProbabilityTheory.IndepFun (⇑(LatticeProb.gaussIso f)) (⇑(LatticeProb.gaussIso g))
      (LatticeProb.gaussLaw ι) := by
  refine (hasGaussianLaw_gaussIso_pair f g).indepFun_of_covariance_eq_zero ?_
  rw [covariance_gaussIso f g]
  exact h

/-- A finite family `gs : Fin m → lp (fun _ : ι => ℝ) 2` of coefficient vectors produces a
jointly Gaussian family of isonormal images `fun i => gaussIso (gs i)`, obtained as a
coordinate-continuous-linear-equivalence image of the vector `gaussIso gs`. -/
theorem hasGaussianLaw_gaussIso_pi {m : ℕ} (gs : Fin m → lp (fun _ : ι => ℝ) 2) :
    HasGaussianLaw (fun ω (i : Fin m) => ⇑(LatticeProb.gaussIso (gs i)) ω)
      (LatticeProb.gaussLaw ι) := by
  have hvec : HasGaussianLaw (fun ω => (WithLp.toLp 2
      (fun i => ⇑(LatticeProb.gaussIso (gs i)) ω) : EuclideanSpace ℝ (Fin m)))
      (LatticeProb.gaussLaw ι) := by
    constructor
    rw [map_gaussIso_vector gs]
    infer_instance
  exact HasGaussianLaw.map_of_measurable
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).toContinuousLinearMap) hvec
    (by fun_prop)

/-- **Pairwise orthogonal coefficient families give a jointly independent family of isonormal
images.** Combines `hasGaussianLaw_gaussIso_pi` with the fact that a jointly Gaussian family
is independent as soon as its pairwise covariances, computed via `covariance_gaussIso`,
vanish. -/
theorem iIndepFun_gaussIso {m : ℕ} (gs : Fin m → lp (fun _ : ι => ℝ) 2)
    (h : ∀ i j : Fin m, i ≠ j → (inner ℝ (gs i) (gs j) : ℝ) = 0) :
    ProbabilityTheory.iIndepFun (fun i => ⇑(LatticeProb.gaussIso (gs i)))
      (LatticeProb.gaussLaw ι) :=
  (hasGaussianLaw_gaussIso_pi gs).iIndepFun_of_covariance_eq_zero fun i j hij => by
    rw [covariance_gaussIso (gs i) (gs j)]
    exact h i j hij

end Sandpile
