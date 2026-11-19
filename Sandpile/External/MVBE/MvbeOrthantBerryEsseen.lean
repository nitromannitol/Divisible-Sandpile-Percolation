import Mathlib
import Sandpile.External.MVBE.MvbeBootstrap
import Sandpile.External.MVBE.MvbeWhitening
import Sandpile.External.MVBE.MvbeRegularClass
import Sandpile.External.MVBE.MvbeSmoothing
import Sandpile.External.MVBE.MvbeImageClass
import Sandpile.External.MVBE.MvbeImageNegOpen
import Sandpile.External.MVBE.MvbeOrthantPerimeter

/-!
# Final assembly: from Theorem R to the frozen multivariate Berry-Esseen shape

Adapted from Lattice-Probability, `LatticeProb/Prob/MvbeOrthantBerryEsseen.lean`, commit `9d53f3aa`,
following Raič, *Bernoulli* 25 (2019), Theorem 1.3.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace Sandpile.External.MVBE

open LatticeProb

section Assembly

/-! ### Operator norms from quadratic bounds -/

/-- A quadratic bound `∑ j, (L v)_j² ≤ c ∑ j, v_j²` bounds the operator norm of
`toEuclideanCLM L` by `√c`. -/
theorem mvbe_opNorm_le_of_sq_bound {m : ℕ} (L : Matrix (Fin m) (Fin m) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hL : ∀ v : Fin m → ℝ, ∑ j, (L *ᵥ v) j ^ 2 ≤ c * ∑ j, v j ^ 2) :
    ‖toEuclideanCLM (𝕜 := ℝ) L‖ ≤ Real.sqrt c := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg c) fun x => ?_
  have h1 : ‖toEuclideanCLM (𝕜 := ℝ) L x‖ = Real.sqrt (∑ j, (L *ᵥ x.ofLp) j ^ 2) := by
    rw [← mvbe_whiten_norm_toLp]
    rfl
  have h2 : ‖x‖ = Real.sqrt (∑ j, x.ofLp j ^ 2) := by
    have := mvbe_whiten_norm_toLp (m := m) x.ofLp
    simpa using this
  rw [h1, h2, ← Real.sqrt_mul hc]
  exact Real.sqrt_le_sqrt (hL x.ofLp)

/-! ### The sets `A_{L,h}` belong to the image class -/

/-- The rounded orthant at level `0` is the plain orthant `{y | ∀ j, y j ≤ h j}`. -/
theorem mvbe_orthant_zero_eq {m : ℕ} [NeZero m] (h : Fin m → ℝ) :
    mvbeOrthant h 0 = {y : EuclideanSpace ℝ (Fin m) | ∀ j, y j ≤ h j} := by
  ext y
  rw [mvbe_mem_orthant, mvbeRho_le_iff_of_nonpos le_rfl]
  simp

/-- `A_{L,h} = L (O_h)` belongs to the class of images of the rounded-orthant class under an
invertible matrix `L`. -/
theorem mvbe_orthantImage_mem_image_cls {m : ℕ} [NeZero m] (L : Matrix (Fin m) (Fin m) ℝ)
    (hL : IsUnit L.det) (h : Fin m → ℝ) :
    mvbeOrthantImage L h ∈ ((mvbeRoundedRegularClass m).image L hL).cls := by
  rw [MvbeRegularClass.image_cls]
  refine ⟨mvbeOrthant h 0, mvbeOrthant_mem_roundedClass le_rfl, ?_⟩
  rw [mvbe_orthant_zero_eq, mvbeOrthantImage_eq_image hL]

/-! ### T1: the whitened bound from Theorem R -/

/-- **T1.**  Theorem R and a Gaussian perimeter bound `γ*(rounded orthants) ≤ c F(m)` for the
class of rounded orthants (with `F m ≥ 1` for `m ≥ 1`) give the whitened bound
`MvbeWhitenedBound F`.

For fixed `δ ∈ (0, 1)`, the set `A_{L,h} = L (O_h)` belongs to the image class `L C₀` of the class
`C₀` of rounded orthants (`κ = 1`, `MvbeNegOpen`), whose perimeter is at most
`γ*(C₀) max (1, ‖L‖) ‖L⁻¹‖ ≤ c F(m) (1 - δ)^{-1/2} (1 + δ)^{1/2}`; Theorem R then gives
`K = max c₀ (1 + c₁ √2 c (1 - δ)^{-1/2} (1 + δ)^{1/2})`, independent of `m`, `n`, `μ`, `L`, `h`. -/
theorem mvbe_whitenedBound_of_thmR (hR : MvbeThmR) (F : ℕ → ℝ) (hF1 : ∀ m, 1 ≤ m → 1 ≤ F m)
    (hF : ∃ c : ℝ, 0 < c ∧ ∀ m, 1 ≤ m → ∀ [NeZero m],
      (mvbeRoundedRegularClass m).gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))
        ≤ ENNReal.ofReal (c * F m)) :
    MvbeWhitenedBound F := by
  obtain ⟨c0, c1, hc0, hc1, hRmain⟩ := hR
  obtain ⟨c, hc, hFc⟩ := hF
  intro δ hδ0 hδ1
  have hδ' : 0 < 1 - δ := by linarith
  have ha1 : 1 ≤ Real.sqrt ((1 - δ)⁻¹) := by
    rw [Real.one_le_sqrt, one_le_inv₀ hδ']
    linarith
  have ha0 : 0 ≤ Real.sqrt ((1 - δ)⁻¹) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ Real.sqrt (1 + δ) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  refine ⟨max c0 (1 + c1 * Real.sqrt 2 * c * (Real.sqrt ((1 - δ)⁻¹) * Real.sqrt (1 + δ))),
    lt_max_of_lt_left hc0, ?_⟩
  intro m n hm μ _ hint hmean hcov L hL hL1 hL2 h
  have : NeZero m := ⟨by omega⟩
  have hLu : IsUnit L.det := mvbe_isUnit_det_of_posDef hL
  have hneg : MvbeNegOpen ((mvbeRoundedRegularClass m).image L hLu) :=
    MvbeRegularClass.image_negOpen _ L hLu (mvbeRoundedRegularClass_negOpen m)
  have hLn : ‖toEuclideanCLM (𝕜 := ℝ) L‖ ≤ Real.sqrt ((1 - δ)⁻¹) :=
    mvbe_opNorm_le_of_sq_bound L (inv_nonneg.2 hδ'.le) hL1
  have hLin : ‖toEuclideanCLM (𝕜 := ℝ) L⁻¹‖ ≤ Real.sqrt (1 + δ) :=
    mvbe_opNorm_le_of_sq_bound L⁻¹ (by linarith) hL2
  have hFm : 1 ≤ F m := hF1 m hm
  have hM : max 1 ‖toEuclideanCLM (𝕜 := ℝ) L‖ * ‖toEuclideanCLM (𝕜 := ℝ) L⁻¹‖
      ≤ Real.sqrt ((1 - δ)⁻¹) * Real.sqrt (1 + δ) :=
    mul_le_mul (max_le ha1 hLn) hLin (norm_nonneg _) ha0
  have hgs : ((mvbeRoundedRegularClass m).image L hLu).gammaStar
      (stdGaussian (EuclideanSpace ℝ (Fin m)))
        ≤ ENNReal.ofReal (c * F m * (Real.sqrt ((1 - δ)⁻¹) * Real.sqrt (1 + δ))) := by
    calc _ ≤ (mvbeRoundedRegularClass m).gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))
            * ENNReal.ofReal (max 1 ‖toEuclideanCLM (𝕜 := ℝ) L‖
              * ‖toEuclideanCLM (𝕜 := ℝ) L⁻¹‖) :=
          MvbeRegularClass.image_gammaStar_le_max _ L hLu
      _ ≤ ENNReal.ofReal (c * F m)
            * ENNReal.ofReal (Real.sqrt ((1 - δ)⁻¹) * Real.sqrt (1 + δ)) :=
          mul_le_mul' (hFc m hm) (ENNReal.ofReal_le_ofReal hM)
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hfin : ((mvbeRoundedRegularClass m).image L hLu).gammaStar
      (stdGaussian (EuclideanSpace ℝ (Fin m))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgs
  have hgsr : (((mvbeRoundedRegularClass m).image L hLu).gammaStar
      (stdGaussian (EuclideanSpace ℝ (Fin m)))).toReal
        ≤ c * F m * (Real.sqrt ((1 - δ)⁻¹) * Real.sqrt (1 + δ)) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hgs
  have key := hRmain m 1 ((mvbeRoundedRegularClass m).image L hLu) hneg hfin n μ hint hmean hcov
    (mvbeOrthantImage L h) (mvbe_orthantImage_mem_image_cls L hLu h)
  refine key.trans ?_
  have hsum : 0 ≤ ∑ i, ∫ x, ‖x‖ ^ 3 ∂μ i :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun x => by positivity
  refine mul_le_mul_of_nonneg_right ?_ hsum
  set K := max c0 (1 + c1 * Real.sqrt 2 * c * (Real.sqrt ((1 - δ)⁻¹) * Real.sqrt (1 + δ)))
    with hK
  have hK0 : 0 ≤ K := (lt_max_of_lt_left hc0).le
  have hKd : 1 + c1 * Real.sqrt 2 * c * (Real.sqrt ((1 - δ)⁻¹) * Real.sqrt (1 + δ)) ≤ K :=
    le_max_right _ _
  have hs : Real.sqrt (1 + (1 : ℝ)) = Real.sqrt 2 := by norm_num
  rw [hs]
  refine max_le ?_ ?_
  · calc c0 ≤ K := le_max_left _ _
      _ = K * 1 := (mul_one K).symm
      _ ≤ K * F m := mul_le_mul_of_nonneg_left hFm hK0
  · have h1 : c1 * (((mvbeRoundedRegularClass m).image L hLu).gammaStar
        (stdGaussian (EuclideanSpace ℝ (Fin m)))).toReal * Real.sqrt 2
          ≤ c1 * (c * F m * (Real.sqrt ((1 - δ)⁻¹) * Real.sqrt (1 + δ))) * Real.sqrt 2 := by
      gcongr
    calc 1 + c1 * (((mvbeRoundedRegularClass m).image L hLu).gammaStar
          (stdGaussian (EuclideanSpace ℝ (Fin m)))).toReal * Real.sqrt 2
        ≤ 1 * F m + c1 * (c * F m * (Real.sqrt ((1 - δ)⁻¹) * Real.sqrt (1 + δ)))
            * Real.sqrt 2 := by linarith
      _ = (1 + c1 * Real.sqrt 2 * c * (Real.sqrt ((1 - δ)⁻¹) * Real.sqrt (1 + δ))) * F m := by
          ring
      _ ≤ K * F m := mul_le_mul_of_nonneg_right hKd (by linarith)

/-! ### T2: the frozen shape with `m` (unconditional in the perimeter) -/

/-- **T2.**  The frozen multivariate Berry-Esseen shape with the dimension factor `m` in place of
`m ^ (1/4)`: from Theorem R, the linear-in-`m` Gaussian perimeter bound
`γ*(rounded orthants) ≤ m / √(2π)` (`mvbeRoundedRegularClass_gammaStar_le`), the whitened bound
(`mvbe_whitenedBound_of_thmR`) and the whitening (`mvbe_frozenShape_linear_of_whitenedBound`).
Nothing is assumed beyond Theorem R. -/
theorem mvbe_frozenShape_linear (hR : MvbeThmR) :
    MvbeFrozenShape (fun m : ℕ => (m : ℝ)) := by
  refine mvbe_frozenShape_linear_of_whitenedBound
    (mvbe_whitenedBound_of_thmR hR (fun m : ℕ => (m : ℝ))
      (fun m hm => Nat.one_le_cast.2 hm) ?_)
  refine ⟨1 / Real.sqrt (2 * Real.pi), by positivity, fun m _ _ => ?_⟩
  refine mvbeRoundedRegularClass_gammaStar_le.trans (le_of_eq ?_)
  congr 1
  ring

/-! ### T3: the frozen statement with `m ^ (1/4)`, conditional on the perimeter bound -/

/-- The Gaussian perimeter of rounded orthants is bounded by a multiple of `m ^ (1 / 4)`. -/
def MvbeOrthantPerimeterQuarter : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) [NeZero m],
    (mvbeRoundedRegularClass m).gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))
      ≤ ENNReal.ofReal (c * (m : ℝ) ^ ((1 : ℝ) / 4))

/-- **T3.**  The frozen multivariate Berry-Esseen statement with `m ^ (1/4)` (in the vocabulary of
`MvbeWhitening.lean`, textually `Sandpile.External.MultivariateBerryEsseen`), from Theorem R and
the named perimeter proposition `MvbeOrthantPerimeterQuarter`. -/
theorem mvbe_frozenQuarter (hR : MvbeThmR) (hP : MvbeOrthantPerimeterQuarter) :
    MvbeFrozenQuarter := by
  obtain ⟨c, hc, hPc⟩ := hP
  exact mvbe_frozenQuarter_of_whitenedBound
    (mvbe_whitenedBound_of_thmR hR (fun m : ℕ => (m : ℝ) ^ ((1 : ℝ) / 4))
      (fun m hm => Real.one_le_rpow (Nat.one_le_cast.2 hm) (by norm_num))
      ⟨c, hc, fun m _ _ => hPc m⟩)

end Assembly

/-- **The multivariate Berry-Esseen comparison for orthants with the factor `m`**, unconditionally:
the frozen statement of `Sandpile.External.MultivariateBerryEsseen` with `C * m` in place of
`C * m ^ (1/4)`, from Raič's Theorem 1.3 (`mvbe_thmR`) and the linear Gaussian perimeter bound of
the rounded orthants (`mvbeRoundedRegularClass_gammaStar_le`). -/
theorem mvbe_frozenShape_linear_unconditional :
    MvbeFrozenShape (fun m : ℕ => (m : ℝ)) :=
  mvbe_frozenShape_linear mvbe_thmR

/-- **The frozen multivariate Berry-Esseen statement** (`MvbeFrozenQuarter` is textually
`Sandpile.External.MultivariateBerryEsseen`), from Raič's Theorem 1.3 (`mvbe_thmR`) and the single
named perimeter proposition `MvbeOrthantPerimeterQuarter` (Raič's Theorem 1.2). -/
theorem mvbe_frozenQuarter_of_perimeter (hP : MvbeOrthantPerimeterQuarter) :
    MvbeFrozenQuarter :=
  mvbe_frozenQuarter mvbe_thmR hP

end Sandpile.External.MVBE
