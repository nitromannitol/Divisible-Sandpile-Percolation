/-
The exact parabolic scaling identity of the DISCRETE rescaled odometer, and the
translation invariance behind it.

`sandpile.tex:1817-1821` defines `𝒰_R(T,x) = R^{-(2-d/2)}u_{⌊R²T⌋}(⌊Rx⌋)`.  At the
scale `S = R√T` one has `S² = R²T` and `R^{-(2-d/2)} = T^{(4-d)/4}S^{-(2-d/2)}`, so

  `𝒰_R(T,x) = T^{(4-d)/4}·S^{-(2-d/2)}u_{⌊S²⌋}(⌊Rx⌋)`   pointwise,

and the i.i.d. mass law is invariant under translation of the lattice, so the site
`⌊Rx⌋` may be moved to the origin inside any law-determined quantity.  Hence

  `E𝒰_R(T,x) = T^{(4-d)/4}E𝒰_{R√T}(1,0)`,
  `Var𝒰_R(T,x) = T^{(4-d)/2}Var𝒰_{R√T}(1,0)`,

both exactly, for every `R > 0` and `T > 0`.  These are the discrete forms of the
two self-similarity identities the corollary states for the limit, and they are
unconditional: nothing about the scaling limit enters.
-/
import Sandpile.Support.ContLawTransfer
import Sandpile.Support.LinStationary
import Sandpile.Support.Translation
import Sandpile.Support.MeanAValue

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

variable {d : ℕ}

/-- **The odometer at a site and at the origin have the same law.**  Translation
invariance of the i.i.d. mass law. -/
theorem map_odometer_eq (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℕ)
    (y : Sandpile.Site d) :
    (Sandpile.massLaw d μ).map (fun σ => Sandpile.odometer σ t y)
      = (Sandpile.massLaw d μ).map (fun σ => Sandpile.odometer σ t 0) := by
  have hshift : (Sandpile.massLaw d μ).map (Sandpile.shiftField y) = Sandpile.massLaw d μ :=
    Sandpile.massLaw_map_shiftField d μ y
  calc (Sandpile.massLaw d μ).map (fun σ => Sandpile.odometer σ t y)
      = (Sandpile.massLaw d μ).map (fun σ => Sandpile.odometer (Sandpile.shiftField y σ) t 0) := by
        refine Measure.map_congr (Filter.Eventually.of_forall fun σ => ?_)
        show Sandpile.odometer σ t y = Sandpile.odometer (Sandpile.shiftField y σ) t 0
        rw [Sandpile.odometer_shiftField σ y t 0, zero_add]
    _ = ((Sandpile.massLaw d μ).map (Sandpile.shiftField y)).map
          (fun σ => Sandpile.odometer σ t 0) := by
        rw [Measure.map_map (Sandpile.measurable_odometer t 0) (Sandpile.measurable_shiftField y)]
        rfl
    _ = (Sandpile.massLaw d μ).map (fun σ => Sandpile.odometer σ t 0) := by rw [hshift]

/-- The same, for the centred mass law of the paper. -/
theorem map_odometer_centered_eq (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℕ)
    (y : Sandpile.Site d) :
    (Sandpile.centeredMassLaw d ν).map (fun σ => Sandpile.odometer σ t y)
      = (Sandpile.centeredMassLaw d ν).map (fun σ => Sandpile.odometer σ t 0) := by
  have : IsProbabilityMeasure (ν.map fun z => 1 + 2 * (d : ℝ) * z) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  exact map_odometer_eq d (ν.map fun z => 1 + 2 * (d : ℝ) * z) t y

/-- **The mean identity from the law identity.** -/
theorem integral_of_map_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : Ω → ℝ) (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (h : P.map f = P.map g) : ∫ ω, f ω ∂P = ∫ ω, g ω ∂P := by
  have h1 : ∫ ω, f ω ∂P = ∫ y : ℝ, y ∂(P.map f) := by
    rw [integral_map hf (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y) (P.map f))]
  have h2 : ∫ ω, g ω ∂P = ∫ y : ℝ, y ∂(P.map g) := by
    rw [integral_map hg (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y) (P.map g))]
  rw [h1, h2, h]

/-- **The pointwise parabolic scaling identity.**  At `S = R√T`,
`𝒰_R(T,x) = T^{(4-d)/4}·S^{-(2-d/2)}·u_{⌊S²⌋}(⌊Rx⌋)`. -/
theorem rescaledOdometer_eq_scale (d : ℕ) (R T : ℝ) (hR : 0 ≤ R) (hT : 0 < T)
    (x : Sandpile.Continuum.Space d) (σ : Sandpile.Site d → ℝ) :
    Sandpile.Continuum.rescaledOdometer d R T x σ
      = T ^ ((4 - (d : ℝ)) / 4) *
        ((R * Real.sqrt T) ^ (-(2 - (d : ℝ) / 2)) *
          Sandpile.odometer σ ⌊(R * Real.sqrt T) ^ 2 * 1⌋₊ (fun i => ⌊R * x i⌋)) := by
  have hTpos : 0 < T := hT
  have hsq : (R * Real.sqrt T) ^ 2 * 1 = R ^ 2 * T := by
    rw [mul_one, mul_pow, Real.sq_sqrt (le_of_lt hT)]
  · have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
    have hfac : (R * Real.sqrt T) ^ (-(2 - (d : ℝ) / 2)) * T ^ ((4 - (d : ℝ)) / 4)
        = R ^ (-(2 - (d : ℝ) / 2)) := by
      rw [Real.mul_rpow hR (le_of_lt hsT), Real.sqrt_eq_rpow,
        ← Real.rpow_mul (le_of_lt hTpos), mul_assoc, ← Real.rpow_add hTpos]
      rw [show (1:ℝ) / 2 * -(2 - (d : ℝ) / 2) + (4 - (d : ℝ)) / 4 = 0 by ring, Real.rpow_zero,
        mul_one]
    unfold Sandpile.Continuum.rescaledOdometer
    rw [hsq]
    rw [show T ^ ((4 - (d : ℝ)) / 4) *
        ((R * Real.sqrt T) ^ (-(2 - (d : ℝ) / 2)) *
          Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ fun i => ⌊R * x i⌋)
        = ((R * Real.sqrt T) ^ (-(2 - (d : ℝ) / 2)) * T ^ ((4 - (d : ℝ)) / 4)) *
          Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ (fun i => ⌊R * x i⌋) by ring]
    rw [hfac]

/-- **The mean scaling identity, exactly.**  `E𝒰_R(T,x) = T^{(4-d)/4}E𝒰_{R√T}(1,0)`. -/
theorem integral_rescaledOdometer_scale (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 < T) (x : Sandpile.Continuum.Space d) :
    ∫ σ, Sandpile.Continuum.rescaledOdometer d R T x σ
        ∂(Sandpile.centeredMassLaw d ν)
      = T ^ ((4 - (d : ℝ)) / 4) *
        ∫ σ, Sandpile.Continuum.rescaledOdometer d (R * Real.sqrt T) 1 0 σ
          ∂(Sandpile.centeredMassLaw d ν) := by
  set P := Sandpile.centeredMassLaw d ν
  set S := R * Real.sqrt T
  set t := ⌊S ^ 2 * 1⌋₊
  have hpoint : ∫ σ, Sandpile.Continuum.rescaledOdometer d R T x σ ∂P
      = T ^ ((4 - (d : ℝ)) / 4) *
        (S ^ (-(2 - (d : ℝ) / 2)) * ∫ σ, Sandpile.odometer σ t (fun i => ⌊R * x i⌋) ∂P) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    rw [rescaledOdometer_eq_scale d R T hR hT x σ]
  have hsite : ∫ σ, Sandpile.odometer σ t (fun i => ⌊R * x i⌋) ∂P
      = ∫ σ, Sandpile.odometer σ t 0 ∂P := by
    exact integral_of_map_eq P _ _
      (Sandpile.measurable_odometer t (fun i => ⌊R * x i⌋)).aemeasurable
      (Sandpile.measurable_odometer t (0 : Sandpile.Site d)).aemeasurable
      (map_odometer_centered_eq d ν t (fun i => ⌊R * x i⌋))
  have hzero : ∫ σ, Sandpile.Continuum.rescaledOdometer d S 1 0 σ ∂P
      = S ^ (-(2 - (d : ℝ) / 2)) * ∫ σ, Sandpile.odometer σ t 0 ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    unfold Sandpile.Continuum.rescaledOdometer
    have hidx : (fun i => ⌊S * (0 : Sandpile.Continuum.Space d) i⌋) = (0 : Sandpile.Site d) := by
      funext i; simp
    rw [hidx]
  rw [hpoint, hsite, hzero]

/-- **The variance scaling identity, exactly.**
`Var𝒰_R(T,x) = T^{(4-d)/2}Var𝒰_{R√T}(1,0)`. -/
theorem variance_rescaledOdometer_scale (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 < T) (x : Sandpile.Continuum.Space d) :
    variance (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ)
        (Sandpile.centeredMassLaw d ν)
      = T ^ ((4 - (d : ℝ)) / 2) *
        variance (fun σ => Sandpile.Continuum.rescaledOdometer d
          (R * Real.sqrt T) 1 0 σ) (Sandpile.centeredMassLaw d ν) := by
  set P := Sandpile.centeredMassLaw d ν
  set S := R * Real.sqrt T
  set t := ⌊S ^ 2 * 1⌋₊
  have hfun : (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ)
      = fun σ => (T ^ ((4 - (d : ℝ)) / 4) * S ^ (-(2 - (d : ℝ) / 2))) *
          Sandpile.odometer σ t (fun i => ⌊R * x i⌋) := by
    funext σ
    rw [rescaledOdometer_eq_scale d R T hR hT x σ, ← mul_assoc]
  have hfun0 : (fun σ => Sandpile.Continuum.rescaledOdometer d S 1 0 σ)
      = fun σ => S ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ t 0 := by
    funext σ
    unfold Sandpile.Continuum.rescaledOdometer
    have hidx : (fun i => ⌊S * (0 : Sandpile.Continuum.Space d) i⌋) = (0 : Sandpile.Site d) := by
      funext i; simp
    rw [hidx]
  have hsite : variance (fun σ => Sandpile.odometer σ t (fun i => ⌊R * x i⌋)) P
      = variance (fun σ => Sandpile.odometer σ t 0) P :=
    variance_of_map_eq P _ _ (Sandpile.measurable_odometer t (fun i => ⌊R * x i⌋)).aemeasurable
      (Sandpile.measurable_odometer t (0 : Sandpile.Site d)).aemeasurable
      (map_odometer_centered_eq d ν t (fun i => ⌊R * x i⌋))
  have hTsq : (T ^ ((4 - (d : ℝ)) / 4)) ^ 2 = T ^ ((4 - (d : ℝ)) / 2) := by
    rw [← Real.rpow_natCast (T ^ ((4 - (d : ℝ)) / 4)) 2, ← Real.rpow_mul (le_of_lt hT)]
    congr 1
    push_cast
    ring
  rw [hfun, hfun0, variance_const_mul, variance_const_mul, hsite, mul_pow, hTsq]
  ring

/-- At `T = 1` and `x = 0` the rescaled odometer is the scale factor times the
odometer at the origin at time `⌊R²⌋`, which is the form the Green weights of
`lem:weighted-exp-conc` are read in. -/
theorem rescaledOdometer_one_zero (d : ℕ) (R : ℝ) (σ : Sandpile.Site d → ℝ) :
    Sandpile.Continuum.rescaledOdometer d R 1 0 σ
      = R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊R ^ 2⌋₊ 0 := by
  unfold Sandpile.Continuum.rescaledOdometer
  norm_num
  left
  congr 1

end Sandpile.Support
