/-
Step 1 of `lem:dgt4-path-survival` (`sandpile.tex:5495-5526`) in the Gaussian
branch of `IsThresholdField`.

The paper compares the probability that the threshold events hold at every site
of a finite set with the product of the one-site probabilities:

  "When $J$ is Gaussian, write $\rho_{xy}\coloneqq\Cov(J(x),J(y))/\Var(J(0))$
   for the correlation; the comparison estimate \citep[Corollary~2.1,
   p.~496]{LiShao} bounds the left-hand side by
   $C\sum_{\{x,y\}\subset\Lambda}|\rho_{xy}|
    \exp\{-(b_x^2+b_y^2)/(2\Var(J(0))(1+|\rho_{xy}|))\}$."

To apply that input the law of the vector `(J(x))_{x∈Λ}` has to be exhibited as a
centred Gaussian vector with a constant diagonal and nonnegative correlations.
`Support/LinGaussBridge.lean` identifies the law of `(V_∞(x))_{x∈Λ}`; here the
sign of `J=-V_∞` is carried through (a centred Gaussian vector is symmetric), the
Gram matrix of the Green coefficients is shown to have the constant diagonal
`Var(ζ(0))∑_z G(0,z)^2` and nonnegative entries, and the comparison inequality is
applied.  What is left of Step 1 after this file is the analytic estimate of the
right-hand side, which is where the tail inversion and the splitting of the pairs
at distance `(\log R)^{2/(d-4)}` enter.
-/
import Sandpile.Support.LinGaussBridge
import Sandpile.Support.ExitGreen
import Sandpile.External.NormalComparison
import Sandpile.External.GreenBoundsHighProved

open LatticeProb.Isonormal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- `Var(J(0))/Var(ζ(0)) = ∑_z G(0,z)^2`, the common variance of the Gaussian
threshold field in units of the one-site variance of the scenery. -/
noncomputable def greenSqSum (d : ℕ) : ℝ := ∑' z : Site d, green d 0 z ^ 2

/-- The covariance matrix `Var(ζ(0))∑_z G(x,z)G(y,z)` of
`sandpile.tex:5450-5452`. -/
noncomputable def greenGram (d : ℕ) (v : ℝ≥0) {m : ℕ} (xs : Fin m → Site d) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => (v : ℝ) * ∑' z : Site d, green d (xs i) z * green d (xs j) z

/-- The covariance matrix is the Gram matrix of the scaled Green coefficient
families. -/
theorem greenGram_eq_gramMatrix (hd : 5 ≤ d) (v : ℝ≥0) {m : ℕ} (xs : Fin m → Site d) :
    greenGram d v xs = gramMatrix (fun i => Real.sqrt (v : ℝ) • greenLp d hd (xs i)) := by
  ext i j
  simp only [greenGram, gramMatrix, Matrix.of_apply]
  rw [real_inner_smul_left, real_inner_smul_right, inner_greenLp, ← mul_assoc,
    Real.mul_self_sqrt v.coe_nonneg]

/-- The covariance matrix is positive semidefinite, as the covariance matrix of
the source's Gaussian vector is required to be. -/
theorem greenGram_posSemidef (hd : 5 ≤ d) (v : ℝ≥0) {m : ℕ} (xs : Fin m → Site d) :
    (greenGram d v xs).PosSemidef := by
  rw [greenGram_eq_gramMatrix hd v xs]
  exact gramMatrix_posSemidef _

/-- The correlations of the Gaussian threshold field are nonnegative: the
covariance is a sum of products of Green functions (`sandpile.tex:5450-5452`),
which is the case of the normal comparison inequality the paper applies. -/
theorem greenGram_nonneg (v : ℝ≥0) {m : ℕ} (xs : Fin m → Site d) (i j : Fin m) :
    0 ≤ greenGram d v xs i j := by
  simp only [greenGram, Matrix.of_apply]
  exact mul_nonneg v.coe_nonneg
    (tsum_nonneg fun z => mul_nonneg (green_nonneg _ _) (green_nonneg _ _))

/-- The diagonal of the covariance matrix is constant: `Var(J(x)) = Var(J(0))`
for every site, by translation invariance of the Green function.  This is the
`∀ i, S i i = v` hypothesis of the normal comparison input. -/
theorem greenGram_diag (v : ℝ≥0) {m : ℕ} (xs : Fin m → Site d) (i : Fin m) :
    greenGram d v xs i i = (v : ℝ) * greenSqSum d := by
  simp only [greenGram, Matrix.of_apply, greenSqSum]
  congr 1
  calc ∑' z : Site d, green d (xs i) z * green d (xs i) z
      = ∑' z : Site d, green d 0 (z - xs i) ^ 2 := by
        refine tsum_congr fun z => ?_
        rw [green_shift (xs i) z]
        ring
    _ = ∑' w : Site d, green d 0 w ^ 2 :=
        (Equiv.subRight (xs i)).tsum_eq (fun w => green d 0 w ^ 2)

/-- The variance of the Gaussian threshold field is bounded below: `G(0,0) ≥ 1`,
so `∑_z G(0,z)^2 ≥ 1`.  This is the paper's `Var(J(0)) > 0`. -/
theorem one_le_greenSqSum (hd : 5 ≤ d) : (1 : ℝ) ≤ greenSqSum d := by
  have hsum : Summable (fun z : Site d => green d 0 z ^ 2) := summable_green_sq hd 0
  have hterm : green d 0 (0 : Site d) ^ 2 ≤ ∑' z : Site d, green d 0 z ^ 2 :=
    hsum.le_tsum 0 (fun b _ => sq_nonneg _)
  have hg : (1 : ℝ) ≤ green d 0 0 := by
    rw [Sandpile.External.green_eq_srwGreenInf d 0 0, sub_zero]
    exact LatticeProb.one_le_srwGreenInf_origin (d := d) (by omega)
  have h1 : (1 : ℝ) ≤ green d 0 (0 : Site d) ^ 2 := by nlinarith
  simpa [greenSqSum] using h1.trans hterm

/-! ### The law of the threshold field -/

/-- A centred Gaussian vector is symmetric: negating it does not change its law.
This is what carries the sign of `J=-V_∞` (`sandpile.tex:5449-5450`) through the
identification of the finite-dimensional laws. -/
theorem multivariateGaussian_map_neg {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S).map (fun y => -y)
      = multivariateGaussian 0 S := by
  have hneg : (fun y : EuclideanSpace ℝ (Fin m) => -y) = fun y => (-1 : ℝ) • y := by
    funext y
    simp
  haveI : IsProbabilityMeasure
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S).map (fun y => -y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun ?_
  funext t
  rw [hneg, charFun_map_smul, charFun_multivariateGaussian hS,
    charFun_multivariateGaussian hS]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_smul, one_smul,
    WithLp.ofLp_neg, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]

/-- The vector of Green fields is almost everywhere measurable in the mass
normalization. -/
theorem aemeasurable_greenFieldVector_mass (hd : 5 ≤ d) (v : ℝ≥0) {m : ℕ}
    (xs : Fin m → Site d) :
    AEMeasurable (fun σ : Site d → ℝ =>
        (WithLp.toLp 2 (fun i => infiniteGreenField (scenery d σ) (xs i)) :
          EuclideanSpace ℝ (Fin m)))
      (centeredMassLaw d (gaussianReal 0 v)) := by
  have h := aemeasurable_greenFieldVector_iid hd v xs
  rw [← map_scenery_centeredMassLaw d (gaussianReal 0 v) (by omega)] at h
  exact h.comp_aemeasurable (measurable_scenery d).aemeasurable

/-- The vector of threshold fields is almost everywhere measurable. -/
theorem aemeasurable_thresholdFieldVector (hd : 5 ≤ d) (v : ℝ≥0) {m : ℕ}
    (xs : Fin m → Site d) :
    AEMeasurable (fun σ : Site d → ℝ =>
        (WithLp.toLp 2 (fun i => -infiniteGreenField (scenery d σ) (xs i)) :
          EuclideanSpace ℝ (Fin m)))
      (centeredMassLaw d (gaussianReal 0 v)) := by
  have h := (aemeasurable_greenFieldVector_mass hd v xs).neg
  refine h.congr ?_
  filter_upwards with σ
  ext i
  simp

/-- **The finite-dimensional laws of the Gaussian threshold field.**  Under a
centred Gaussian scenery of variance `v` the vector `(J(x))_{x∈Λ}` of
`sandpile.tex:5449-5450` is the centred Gaussian vector with covariance
`Var(ζ(0))∑_z G(x,z)G(y,z)`. -/
theorem map_thresholdField_vector (hd : 5 ≤ d) (v : ℝ≥0) {m : ℕ} (xs : Fin m → Site d) :
    (centeredMassLaw d (gaussianReal 0 v)).map
        (fun σ => (WithLp.toLp 2 (fun i => -infiniteGreenField (scenery d σ) (xs i)) :
          EuclideanSpace ℝ (Fin m)))
      = multivariateGaussian 0 (greenGram d v xs) := by
  have hfun : (fun σ : Site d → ℝ =>
        (WithLp.toLp 2 (fun i => -infiniteGreenField (scenery d σ) (xs i)) :
          EuclideanSpace ℝ (Fin m)))
      = (fun y : EuclideanSpace ℝ (Fin m) => -y) ∘
        (fun σ : Site d → ℝ =>
          (WithLp.toLp 2 (fun i => infiniteGreenField (scenery d σ) (xs i)) :
            EuclideanSpace ℝ (Fin m))) := by
    funext σ
    ext i
    simp
  rw [hfun, ← AEMeasurable.map_map_of_aemeasurable
      (measurable_neg (G := EuclideanSpace ℝ (Fin m))).aemeasurable
      (aemeasurable_greenFieldVector_mass hd v xs),
    map_infiniteGreenField_vector_mass hd v xs]
  exact multivariateGaussian_map_neg (greenGram_posSemidef hd v xs)

/-- The orthant `{y | ∀ i, y i ≤ b i}` is measurable. -/
theorem measurableSet_orthant {m : ℕ} (b : Fin m → ℝ) :
    MeasurableSet {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i} := by
  have hrw : {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}
      = ⋂ i : Fin m, {y : EuclideanSpace ℝ (Fin m) | y i ≤ b i} := by
    ext y
    simp
  rw [hrw]
  exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const

/-- The probability that the threshold events hold at every site of a finite
family is the orthant probability of the centred Gaussian vector. -/
theorem measure_threshold_orthant (hd : 5 ≤ d) (v : ℝ≥0) {m : ℕ} (xs : Fin m → Site d)
    (b : Fin m → ℝ) :
    (centeredMassLaw d (gaussianReal 0 v))
        {σ : Site d → ℝ | ∀ i, -infiniteGreenField (scenery d σ) (xs i) ≤ b i}
      = multivariateGaussian 0 (greenGram d v xs)
          {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i} := by
  rw [← map_thresholdField_vector hd v xs,
    Measure.map_apply_of_aemeasurable (aemeasurable_thresholdFieldVector hd v xs)
      (measurableSet_orthant b)]
  rfl

/-- **The one-site law of the Gaussian threshold field.**  `J(x)` is a centred
real Gaussian of variance `Var(ζ(0))∑_z G(0,z)^2`, the same at every site. -/
theorem map_thresholdField_single (hd : 5 ≤ d) (v : ℝ≥0) (x : Site d) :
    (centeredMassLaw d (gaussianReal 0 v)).map
        (fun σ => -infiniteGreenField (scenery d σ) x)
      = gaussianReal 0 (((v : ℝ) * greenSqSum d).toNNReal) := by
  have hS := greenGram_posSemidef hd v (fun _ : Fin 1 => x)
  have hmp := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin 1))) hS (i := 0)
  have hfun : (fun σ : Site d → ℝ => -infiniteGreenField (scenery d σ) x)
      = (fun y : EuclideanSpace ℝ (Fin 1) => y.ofLp 0) ∘
        (fun σ : Site d → ℝ => (WithLp.toLp 2
          (fun _ : Fin 1 => -infiniteGreenField (scenery d σ) x) :
            EuclideanSpace ℝ (Fin 1))) := rfl
  rw [hfun, ← AEMeasurable.map_map_of_aemeasurable
      (Measurable.aemeasurable (by fun_prop))
      (aemeasurable_thresholdFieldVector hd v (fun _ : Fin 1 => x)),
    map_thresholdField_vector hd v (fun _ : Fin 1 => x), hmp.map_eq]
  congr 1
  rw [greenGram_diag]

/-- The one-site threshold probability, as a measure of a half line. -/
theorem measure_threshold_single (hd : 5 ≤ d) (v : ℝ≥0) (x : Site d) (c : ℝ) :
    (centeredMassLaw d (gaussianReal 0 v))
        {σ : Site d → ℝ | -infiniteGreenField (scenery d σ) x ≤ c}
      = gaussianReal 0 (((v : ℝ) * greenSqSum d).toNNReal) (Set.Iic c) := by
  have hae : AEMeasurable (fun σ : Site d → ℝ => -infiniteGreenField (scenery d σ) x)
      (centeredMassLaw d (gaussianReal 0 v)) :=
    (Measurable.aemeasurable (f := fun y : EuclideanSpace ℝ (Fin 1) => y.ofLp 0)
      (by fun_prop)).comp_aemeasurable
      (aemeasurable_thresholdFieldVector hd v (fun _ : Fin 1 => x))
  rw [← map_thresholdField_single hd v x,
    Measure.map_apply_of_aemeasurable hae measurableSet_Iic]
  rfl

/-! ### The comparison inequality applied -/

/-- **Step 1 of `lem:dgt4-path-survival` in the Gaussian branch,**
`eq:dgt4-path-threshold-factorization` (`sandpile.tex:5497-5511`).  The
probability that the threshold events hold at every site of a finite family
differs from the product of the one-site probabilities by at most
`C ∑_{i<j} ρ_{ij} exp(-(b_i²+b_j²)/(2 Var(J(0))(1+ρ_{ij})))`, where
`ρ_{ij} = Cov(J(x_i),J(x_j))/Var(J(0))` and `Var(J(0)) = Var(ζ(0))∑_z G(0,z)^2`.
The constant is the universal constant of the normal comparison inequality: it
is bound before the dimension, the variance, the sites and the levels.  What is
left of Step 1 is the analytic estimate of the right-hand side. -/
theorem exists_gaussian_threshold_factorization (hNormal : External.NormalComparison) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 5 ≤ d → ∀ (v : ℝ≥0), 0 < (v : ℝ) →
      ∀ (m : ℕ) (xs : Fin m → Site d) (b : Fin m → ℝ),
        |((centeredMassLaw d (gaussianReal 0 v))
              {σ : Site d → ℝ | ∀ i, -infiniteGreenField (scenery d σ) (xs i) ≤ b i}).toReal -
            ∏ i, ((centeredMassLaw d (gaussianReal 0 v))
              {σ : Site d → ℝ | -infiniteGreenField (scenery d σ) 0 ≤ b i}).toReal| ≤
          C * ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
            greenGram d v xs i j / ((v : ℝ) * greenSqSum d) *
              Real.exp (-(b i ^ 2 + b j ^ 2) /
                (2 * ((v : ℝ) * greenSqSum d) *
                  (1 + greenGram d v xs i j / ((v : ℝ) * greenSqSum d)))) := by
  obtain ⟨C, hC, hcomp⟩ := hNormal
  refine ⟨C, hC, ?_⟩
  intro d hd v hv m xs b
  have hgs : (1 : ℝ) ≤ greenSqSum d := one_le_greenSqSum hd
  have hwpos : (0 : ℝ) < (v : ℝ) * greenSqSum d := by nlinarith
  set w : ℝ≥0 := ((v : ℝ) * greenSqSum d).toNNReal with hw
  have hwcoe : (w : ℝ) = (v : ℝ) * greenSqSum d := Real.coe_toNNReal _ hwpos.le
  have hw0 : 0 < w := by
    rw [← NNReal.coe_pos, hwcoe]
    exact hwpos
  have hmain := hcomp m w hw0 (greenGram d v xs) (greenGram_posSemidef hd v xs)
    (fun i => by rw [greenGram_diag, hwcoe]) (fun i j => greenGram_nonneg v xs i j) b
  rw [hwcoe] at hmain
  have hprod : ∀ i : Fin m, (centeredMassLaw d (gaussianReal 0 v))
      {σ : Site d → ℝ | -infiniteGreenField (scenery d σ) 0 ≤ b i}
      = gaussianReal 0 w (Set.Iic (b i)) := fun i => measure_threshold_single hd v 0 (b i)
  simp only [hprod]
  rw [measure_threshold_orthant hd v xs b]
  exact hmain

end Sandpile
