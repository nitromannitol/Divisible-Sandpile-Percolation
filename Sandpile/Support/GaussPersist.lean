import Sandpile.External.BerryEsseen
import LatticeProb.Prob.GaussOrthant

/-!
# Explicit Gaussian Persistence Ratio

The Gaussian persistence bound with an explicit ratio.

`sandpile.tex:1751-1758` bounds the probability that a Gaussian with nearly
isotropic covariance stays below a small threshold in every coordinate by
`[√((1+δ)/(1-δ)) Φ(η/√(1+δ))]^m`, and chooses `η` so that the bracket is less
than one.  The library proves the bound; what is fixed here is the pair `(δ, η)`
that makes the bracket explicit.  Taking `η = 1` and
`δ = (1-Φ(1))/(2+2Φ(1))` gives the bracket at most `√Φ(1) < 1`, since
`(1+δ)/(1-δ) = (3+Φ(1))/(1+3Φ(1))` and `Φ(1)(3+Φ(1)) ≤ 1+3Φ(1)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Sandpile

/-- The standard normal law puts mass strictly less than one on `Set.Iic η`, since its
complement `Set.Ioi η` carries positive mass by absolute continuity with Lebesgue measure. -/
theorem gaussianReal_Iic_lt_one (η : ℝ) :
    gaussianReal 0 1 (Set.Iic η) < 1 := by
  have hv : (1 : ℝ≥0) ≠ 0 := by norm_num
  have hpos : gaussianReal 0 1 (Set.Ioi η) ≠ 0 := by
    intro h
    have hvol := gaussianReal_absolutelyContinuous' 0 hv h
    rw [Real.volume_Ioi] at hvol
    exact ENNReal.top_ne_zero hvol
  have hadd : gaussianReal 0 1 (Set.Iic η) + gaussianReal 0 1 (Set.Ioi η) = 1 := by
    have hcompl : (Set.Iic η)ᶜ = Set.Ioi η := by
      ext x; simp
    have := measure_add_measure_compl (μ := gaussianReal 0 1) (s := Set.Iic η)
      measurableSet_Iic
    rw [hcompl] at this
    rw [this]
    exact measure_univ
  have hle : gaussianReal 0 1 (Set.Iic η) ≤ 1 := prob_le_one
  by_contra hcon
  push Not at hcon
  have heq : gaussianReal 0 1 (Set.Iic η) = 1 := le_antisymm hle hcon
  rw [heq] at hadd
  have hI : gaussianReal 0 1 (Set.Ioi η) = 0 := by
    have h1 : (1 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have h2 : (1 : ℝ≥0∞) + gaussianReal 0 1 (Set.Ioi η) = 1 + 0 := by
      rw [add_zero]; exact hadd
    exact (ENNReal.add_right_inj h1).mp h2
  exact hpos hI

end Sandpile

namespace Sandpile

open Sandpile.External.BerryEsseen

/-- The standard normal distribution function, as a real. -/
noncomputable def gaussTail (η : ℝ) : ℝ := (gaussianReal 0 1 (Set.Iic η)).toReal

/-- `gaussTail η < 1`, the real-valued restatement of `gaussianReal_Iic_lt_one`. -/
theorem gaussTail_lt_one (η : ℝ) : gaussTail η < 1 := by
  have h := gaussianReal_Iic_lt_one η
  have hne : gaussianReal 0 1 (Set.Iic η) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  rw [gaussTail, ← ENNReal.toReal_lt_toReal hne ENNReal.one_ne_top] at *
  simpa using h

/-- `0 < gaussTail η`, since the standard normal law puts positive mass on `Set.Iic η` (by
absolute continuity with Lebesgue measure) and this mass is finite. -/
theorem gaussTail_pos (η : ℝ) : 0 < gaussTail η := by
  have hv : (1 : ℝ≥0) ≠ 0 := by norm_num
  have hne0 : gaussianReal 0 1 (Set.Iic η) ≠ 0 := by
    intro h
    have hvol := gaussianReal_absolutelyContinuous' 0 hv h
    rw [Real.volume_Iic] at hvol
    exact ENNReal.top_ne_zero hvol
  have hne : gaussianReal 0 1 (Set.Iic η) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  exact ENNReal.toReal_pos hne0 hne

/-- `gaussTail` is monotone: `x ≤ y` implies `gaussTail x ≤ gaussTail y`, since `Set.Iic x ⊆
Set.Iic y`. -/
theorem gaussTail_mono {x y : ℝ} (h : x ≤ y) : gaussTail x ≤ gaussTail y := by
  have hne : gaussianReal 0 1 (Set.Iic y) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  exact ENNReal.toReal_mono hne (measure_mono (Set.Iic_subset_Iic.mpr h))

end Sandpile

namespace Sandpile

/-- The spectral tolerance `δ` of `sandpile.tex:1745-1749`, chosen from the
value of the normal distribution function at one. -/
noncomputable def persistDelta : ℝ := (1 - gaussTail 1) / (2 + 2 * gaussTail 1)

/-- The persistence ratio `κ` of `sandpile.tex:1751-1758`: the bracket
`√((1+δ)/(1-δ)) Φ(η/√(1+δ))` at `η = 1` is at most `√Φ(1) < 1`. -/
noncomputable def persistKappa : ℝ := Real.sqrt (gaussTail 1)

/-- `0 < persistDelta`, since `gaussTail 1` lies strictly between `0` and `1`. -/
theorem persistDelta_pos : 0 < persistDelta := by
  have h1 := gaussTail_lt_one 1
  have h2 := gaussTail_pos 1
  rw [persistDelta]
  positivity

/-- `persistDelta < 1`, since `gaussTail 1` lies strictly between `0` and `1`. -/
theorem persistDelta_lt_one : persistDelta < 1 := by
  have h1 := gaussTail_lt_one 1
  have h2 := gaussTail_pos 1
  rw [persistDelta, div_lt_one (by linarith)]
  linarith

/-- `0 < persistKappa`, the square root of the positive quantity `gaussTail 1`. -/
theorem persistKappa_pos : 0 < persistKappa :=
  Real.sqrt_pos.mpr (gaussTail_pos 1)

/-- `persistKappa < 1`, since `gaussTail 1 < 1` and the square root is monotone. -/
theorem persistKappa_lt_one : persistKappa < 1 := by
  have h1 := gaussTail_lt_one 1
  have h2 : Real.sqrt (gaussTail 1) < Real.sqrt 1 :=
    Real.sqrt_lt_sqrt (gaussTail_pos 1).le h1
  rw [Real.sqrt_one] at h2
  exact h2

/-- **The bracket of the Gaussian persistence bound is at most `κ`.** -/
theorem bracket_le_persistKappa :
    Real.sqrt ((1 + persistDelta) / (1 - persistDelta)) *
        gaussTail (1 / Real.sqrt (1 + persistDelta)) ≤ persistKappa := by
  set p := gaussTail 1 with hp
  have hp1 : p < 1 := gaussTail_lt_one 1
  have hp0 : 0 < p := gaussTail_pos 1
  have hd0 : 0 < persistDelta := persistDelta_pos
  have hd1 : persistDelta < 1 := persistDelta_lt_one
  have hone : 1 / Real.sqrt (1 + persistDelta) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (1 + persistDelta) := by
      have h2 : Real.sqrt 1 ≤ Real.sqrt (1 + persistDelta) :=
        Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_one] at h2
    rw [div_le_one (by linarith)]
    exact h1
  have hmono : gaussTail (1 / Real.sqrt (1 + persistDelta)) ≤ p := gaussTail_mono hone
  have hratio : (1 + persistDelta) / (1 - persistDelta) = (3 + p) / (1 + 3 * p) := by
    rw [persistDelta, ← hp]
    have hden : (0 : ℝ) < 2 + 2 * p := by linarith
    have hb : (0 : ℝ) < 1 + 3 * p := by linarith
    have hnum1 : 1 + (1 - p) / (2 + 2 * p) = (3 + p) / (2 + 2 * p) := by
      field_simp
      ring
    have hnum2 : 1 - (1 - p) / (2 + 2 * p) = (1 + 3 * p) / (2 + 2 * p) := by
      field_simp
      ring
    rw [hnum1, hnum2]
    rw [div_div_div_comm]
    rw [div_self (ne_of_gt hden), div_one]
  have hA : 0 ≤ Real.sqrt ((1 + persistDelta) / (1 - persistDelta)) := Real.sqrt_nonneg _
  have hstep : Real.sqrt ((1 + persistDelta) / (1 - persistDelta)) *
      gaussTail (1 / Real.sqrt (1 + persistDelta))
      ≤ Real.sqrt ((3 + p) / (1 + 3 * p)) * p := by
    rw [hratio] at *
    exact mul_le_mul_of_nonneg_left hmono hA
  refine hstep.trans ?_
  have hsq : Real.sqrt ((3 + p) / (1 + 3 * p)) * p ≤ Real.sqrt p := by
    have hnn : (0 : ℝ) ≤ (3 + p) / (1 + 3 * p) := by positivity
    have hkey : ((3 + p) / (1 + 3 * p)) * p ^ 2 ≤ p := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    have h1 : Real.sqrt ((3 + p) / (1 + 3 * p)) * p
        = Real.sqrt (((3 + p) / (1 + 3 * p)) * p ^ 2) := by
      rw [Real.sqrt_mul hnn, Real.sqrt_sq hp0.le]
    rw [h1]
    exact Real.sqrt_le_sqrt hkey
  exact hsq

end Sandpile

namespace Sandpile

open LatticeProb Matrix
open Sandpile.External.BerryEsseen

/-- The matrix dot product `v ⬝ᵥ S *ᵥ v` equals the quadratic form `quadForm S v`, both being the
double sum `∑ i j, S i j * v i * v j`. -/
theorem dotProduct_eq_quadForm {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) :
    v ⬝ᵥ S *ᵥ v = quadForm S v := by
  rw [quadForm]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The squared Euclidean norm of `v` is the sum of the squares of its coordinates. -/
theorem euclidean_norm_sq {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    ‖v‖ ^ 2 = ∑ j, v j ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => by positivity)]
  exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]

/-- **The Gaussian persistence bound at the tolerance `persistDelta`.** -/
theorem multivariateGaussian_orthant_persist {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ)
    (hS : S.PosSemidef)
    (hlo : ∀ v : Fin m → ℝ, (1 - persistDelta) * ∑ j, v j ^ 2 ≤ quadForm S v)
    (hhi : ∀ v : Fin m → ℝ, quadForm S v ≤ (1 + persistDelta) * ∑ j, v j ^ 2) :
    multivariateGaussian 0 S {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ 1}
      ≤ ENNReal.ofReal (persistKappa ^ m) := by
  have hd0 : 0 < persistDelta := persistDelta_pos
  have hd1 : persistDelta < 1 := persistDelta_lt_one
  have hlib := LatticeProb.multivariateGaussian_orthant_le S hS hd0 hd1
    (fun v => by rw [dotProduct_eq_quadForm, euclidean_norm_sq]; exact hlo v)
    (fun v => by rw [dotProduct_eq_quadForm, euclidean_norm_sq]; exact hhi v) 1
  refine hlib.trans ?_
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  rw [hcard]
  have hne : gaussianReal 0 1 (Set.Iic (1 / Real.sqrt (1 + persistDelta))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  have hmu : gaussianReal 0 1 (Set.Iic (1 / Real.sqrt (1 + persistDelta)))
      = ENNReal.ofReal (gaussTail (1 / Real.sqrt (1 + persistDelta))) := by
    rw [gaussTail, ENNReal.ofReal_toReal hne]
  have hkap : 0 ≤ persistKappa := persistKappa_pos.le
  have hA : (0 : ℝ) ≤ Real.sqrt ((1 + persistDelta) / (1 - persistDelta)) := Real.sqrt_nonneg _
  have hstep : ENNReal.ofReal (Real.sqrt ((1 + persistDelta) / (1 - persistDelta)))
        * gaussianReal 0 1 (Set.Iic (1 / Real.sqrt (1 + persistDelta)))
      ≤ ENNReal.ofReal persistKappa := by
    rw [hmu, ← ENNReal.ofReal_mul hA]
    exact ENNReal.ofReal_le_ofReal bracket_le_persistKappa
  calc (ENNReal.ofReal (Real.sqrt ((1 + persistDelta) / (1 - persistDelta)))
        * gaussianReal 0 1 (Set.Iic (1 / Real.sqrt (1 + persistDelta)))) ^ m
      ≤ (ENNReal.ofReal persistKappa) ^ m := pow_le_pow_left' hstep m
    _ = ENNReal.ofReal (persistKappa ^ m) := (ENNReal.ofReal_pow hkap m).symm

end Sandpile
